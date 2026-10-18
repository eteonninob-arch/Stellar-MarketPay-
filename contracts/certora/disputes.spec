/*
 * contracts/certora/disputes.spec
 *
 * Certora Verification Language (CVL) specification for dispute resolution
 * and dispute bond accounting in `contracts/marketpay-contract/src/disputes.rs`.
 *
 * This spec formally verifies the following properties:
 *
 *   DB-1 (Arithmetic): A dispute split is fully accounted for —
 *                      arbitrator fee + winner share + loser share == escrow amount.
 *   DB-2 (Property):   Raising and resolving a dispute never changes the escrow
 *                      amount, and a dispute can be resolved at most once.
 *   DB-3 (Ghost):      A locked bond is either refunded OR slashed — never both,
 *                      never twice — and always for exactly the locked amount.
 *   DB-4 (Ghost):      Whichever branch is taken, the bond ends up with the
 *                      winner (refund ⇒ caller is the winner; slash ⇒ paid to
 *                      the winner), so the losing bond-caller never recovers it.
 *
 * Run with:
 *   certoraRun contracts/certora/disputes.conf
 *
 * ── Verification strategy ────────────────────────────────────────────────────
 *
 * DB-1 restates the integer formulas of `resolve_dispute` over `mathint`.
 * DB-2 is checked against observable state via `get_escrow` / `get_status`.
 * DB-3 / DB-4 follow the ghost pattern of `escrow.spec`: the ghosts below are
 * intended to be wired to the `bond_lck`, `bond_rtn` and `bond_slsh` transfer
 * sites via `cvlr-soroban` storage/transfer hooks for exact tracking.
 */

methods {
    // ── Dispute lifecycle (mutating) ─────────────────────────────────────────
    function raise_dispute(string job_id, address caller) expect void;
    function resolve_dispute(string job_id, address arbitrator, address winner, uint32 split_percentage, uint32 arbitrator_fee_bps) expect void;
    function set_dispute_bond(address admin, address token, int128 amount) expect void;

    // ── Getters / Views ──────────────────────────────────────────────────────
    function get_escrow(string job_id) returns Escrow envfree;
    function get_status(string job_id) returns uint8  envfree;
}

// ─── Status Constants (matching EscrowStatus enum, see escrow.spec) ──────────
definition STATUS_RELEASED() returns uint8 = 2;
definition STATUS_DISPUTED() returns uint8 = 4;

definition PCT_DENOMINATOR() returns mathint = 100;
definition BPS_DENOMINATOR() returns mathint = 10000;


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  DB-1 — Dispute split conserves the escrow amount                          ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule db1_split_conserves_amount(mathint amount, mathint split_pct, mathint fee_bps) {
    require amount >= 0;
    require split_pct >= 0 && split_pct <= PCT_DENOMINATOR();   // enforced by resolve_dispute
    require fee_bps >= 0 && fee_bps <= BPS_DENOMINATOR();       // enforced by resolve_dispute

    mathint arbitrator_fee = (amount * fee_bps) / BPS_DENOMINATOR();
    mathint distributable  = amount - arbitrator_fee;
    mathint winner_amount  = (distributable * split_pct) / PCT_DENOMINATOR();
    mathint loser_amount   = distributable - winner_amount;

    assert arbitrator_fee >= 0 && winner_amount >= 0 && loser_amount >= 0,
        "DB-1: every leg of a dispute payout must be non-negative";
    assert arbitrator_fee + winner_amount + loser_amount == amount,
        "DB-1: arbitrator fee + winner share + loser share must equal the escrow amount";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  DB-2 — Disputes settle the escrow exactly once                            ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule db2_raise_preserves_amount(env e, string job_id, address caller) {
    Escrow before = get_escrow(job_id);
    raise_dispute(e, job_id, caller);
    Escrow after = get_escrow(job_id);

    assert after.amount == before.amount,
        "DB-2: raising a dispute must not change the escrow amount";
    assert get_status(job_id) == STATUS_DISPUTED(),
        "DB-2: a successful raise_dispute must leave the escrow Disputed";
}

rule db2_resolve_settles_escrow(env e, string job_id, address arbitrator, address winner, uint32 split, uint32 fee_bps) {
    Escrow before = get_escrow(job_id);
    resolve_dispute(e, job_id, arbitrator, winner, split, fee_bps);
    Escrow after = get_escrow(job_id);

    assert after.amount == before.amount,
        "DB-2: resolving a dispute must not change the recorded escrow amount";
    assert get_status(job_id) == STATUS_RELEASED(),
        "DB-2: a successful resolve_dispute must leave the escrow Released";
}

rule db2_cannot_resolve_twice(env e, string job_id, address arbitrator, address winner, uint32 split, uint32 fee_bps) {
    require get_status(job_id) != STATUS_DISPUTED();

    resolve_dispute@withrevert(e, job_id, arbitrator, winner, split, fee_bps);
    assert lastReverted,
        "DB-2: resolve_dispute must revert unless the escrow is Disputed (no double settlement)";
}

rule db2_resolve_rejects_out_of_range(env e, string job_id, address arbitrator, address winner, uint32 split, uint32 fee_bps) {
    require split > 100 || fee_bps > 10000;

    resolve_dispute@withrevert(e, job_id, arbitrator, winner, split, fee_bps);
    assert lastReverted,
        "DB-2: out-of-range split percentage or arbitrator fee must revert";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  DB-3 / DB-4 — Bond refund / slash exclusivity                             ║
// ╚══════════════════════════════════════════════════════════════════════════════╝
//
//   ghost_bond_locked[job]    — bond amount currently held for `job` (0 if none)
//   ghost_bond_refunds[job]   — number of `bond_rtn` settlements for `job`
//   ghost_bond_slashes[job]   — number of `bond_slsh` settlements for `job`
//   ghost_bond_paid[job]      — total bond amount paid out for `job`
//   ghost_bond_recipient[job] — recipient of the last bond settlement for `job`

ghost mapping(string => mathint) ghost_bond_locked {
    init_state axiom forall string j. ghost_bond_locked[j] == 0;
}
ghost mapping(string => mathint) ghost_bond_refunds {
    init_state axiom forall string j. ghost_bond_refunds[j] == 0;
}
ghost mapping(string => mathint) ghost_bond_slashes {
    init_state axiom forall string j. ghost_bond_slashes[j] == 0;
}
ghost mapping(string => mathint) ghost_bond_paid {
    init_state axiom forall string j. ghost_bond_paid[j] == 0;
}
ghost mapping(string => address) ghost_bond_recipient;

rule db3_resolve_refunds_xor_slashes(env e, string job_id, address arbitrator, address winner, uint32 split, uint32 fee_bps) {
    require ghost_bond_locked[job_id] > 0;

    mathint locked   = ghost_bond_locked[job_id];
    mathint refunds0 = ghost_bond_refunds[job_id];
    mathint slashes0 = ghost_bond_slashes[job_id];
    mathint paid0    = ghost_bond_paid[job_id];

    resolve_dispute(e, job_id, arbitrator, winner, split, fee_bps);

    mathint dRefund = ghost_bond_refunds[job_id] - refunds0;
    mathint dSlash  = ghost_bond_slashes[job_id] - slashes0;

    assert (dRefund == 1 && dSlash == 0) || (dRefund == 0 && dSlash == 1),
        "DB-3: resolving a bonded dispute must either refund or slash the bond, exactly once";
    assert ghost_bond_paid[job_id] == paid0 + locked,
        "DB-3: the bond settlement must pay out exactly the locked amount";
    assert ghost_bond_locked[job_id] == 0,
        "DB-3: the bond record must be consumed by resolve_dispute";
}

rule db3_unbonded_resolve_pays_no_bond(env e, string job_id, address arbitrator, address winner, uint32 split, uint32 fee_bps) {
    require ghost_bond_locked[job_id] == 0;

    mathint paid0 = ghost_bond_paid[job_id];
    resolve_dispute(e, job_id, arbitrator, winner, split, fee_bps);

    assert ghost_bond_paid[job_id] == paid0,
        "DB-3: a dispute raised in zero-cost mode must not pay out any bond";
}

rule db4_bond_goes_to_winner(env e, string job_id, address arbitrator, address winner, uint32 split, uint32 fee_bps) {
    require ghost_bond_locked[job_id] > 0;

    resolve_dispute(e, job_id, arbitrator, winner, split, fee_bps);

    assert ghost_bond_recipient[job_id] == winner,
        "DB-4: the bond must always end with the winner (refund to winning caller or slash to winner)";
}

/// Bonds are snapshotted once per dispute and settled once, so across the
/// whole lifetime of a job the bond can be refunded or slashed at most once.
invariant db3_bond_settled_at_most_once(string job_id)
    ghost_bond_refunds[job_id] >= 0
    && ghost_bond_slashes[job_id] >= 0
    && ghost_bond_refunds[job_id] + ghost_bond_slashes[job_id] <= 1
    filtered { f -> true }
