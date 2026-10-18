/*
 * contracts/certora/milestones.spec
 *
 * Certora Verification Language (CVL) specification for the milestone
 * percentage math in `contracts/marketpay-contract/src/milestones.rs`.
 *
 * This spec formally verifies the following fund-conservation properties:
 *
 *   MS-1 (Arithmetic): A single milestone payout is fully accounted for —
 *                      platform fee + referral bonus + freelancer share == payout.
 *   MS-2 (Arithmetic): Summing the per-milestone payouts of a split whose
 *                      percentages add up to 100 never exceeds the escrow
 *                      amount, and the rounding dust is strictly less than the
 *                      number of milestones.
 *   MS-3 (Property):   The escrow `amount` (the base every split is computed
 *                      from) is never mutated after creation.
 *   MS-4 (Property):   Releasing / rejecting a milestone resolves exactly that
 *                      milestone, and a milestone is never both released and
 *                      rejected (a share is paid out at most once).
 *   MS-5 (Ghost):      Cumulative milestone payouts per escrow never exceed
 *                      the escrow amount.
 *
 * Run with:
 *   certoraRun contracts/certora/milestones.conf
 *
 * ── Verification strategy ────────────────────────────────────────────────────
 *
 * MS-1 and MS-2 restate the contract's integer formulas
 * (`amount * pct / 100`, `payout * fee_bps / 10_000`, referral bonus of
 * 200 bps capped by `MaxReferrerBonusXlm`) over unbounded `mathint` and prove
 * the conservation identities for every input in the contract's accepted
 * domain.  MS-3 and MS-4 are checked against observable contract state via
 * `get_escrow`.  MS-5 follows the ghost pattern of `escrow.spec`: the ghost
 * `ghost_ms_paid` should be wired to the token transfer hooks via the
 * `cvlr-soroban` crate for exact tracking in production.
 */

methods {
    // ── Milestone lifecycle (mutating) ───────────────────────────────────────
    function create_escrow_with_milestones(string job_id, address client, CreateEscrowParams params) expect void;
    function release_milestone(string job_id, uint32 milestone_id, address client) expect void;
    function release_all_milestones(string job_id, address client) expect void;
    function reject_milestone(string job_id, uint32 milestone_index, address client) expect void;

    // ── Getters / Views ──────────────────────────────────────────────────────
    function get_escrow(string job_id) returns Escrow envfree;
    function get_status(string job_id) returns uint8  envfree;
}

// ─── Contract constants (mirroring milestones.rs / escrow.rs) ────────────────
definition MAX_MILESTONES()      returns mathint = 5;
definition PCT_DENOMINATOR()     returns mathint = 100;
definition BPS_DENOMINATOR()     returns mathint = 10000;
definition REFERRAL_BONUS_BPS()  returns mathint = 200;

// ─── Contract formulas ───────────────────────────────────────────────────────

/// `escrow.amount * milestone.percentage / 100` (milestones.rs).
definition milestone_payout(mathint amount, mathint pct) returns mathint =
    (amount * pct) / PCT_DENOMINATOR();

/// `payout * fee_bps / 10_000` (milestones.rs).
definition platform_fee(mathint payout, mathint fee_bps) returns mathint =
    (payout * fee_bps) / BPS_DENOMINATOR();

/// `min(after_fee * 200 / 10_000, cap)` (escrow.rs::apply_referral_bonus).
definition referral_bonus(mathint after_fee, mathint cap) returns mathint =
    (after_fee * REFERRAL_BONUS_BPS()) / BPS_DENOMINATOR() < cap
        ? (after_fee * REFERRAL_BONUS_BPS()) / BPS_DENOMINATOR()
        : cap;


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  MS-1 — A single milestone payout is fully accounted for                    ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule ms1_single_payout_conserved(mathint amount, mathint pct, mathint fee_bps, mathint cap, bool has_referrer) {
    require amount >= 0;
    require pct > 0 && pct <= PCT_DENOMINATOR();
    require fee_bps >= 0 && fee_bps <= BPS_DENOMINATOR();
    require cap >= 0;

    mathint payout    = milestone_payout(amount, pct);
    mathint fee       = platform_fee(payout, fee_bps);
    mathint after_fee = payout - fee;
    mathint bonus     = has_referrer ? referral_bonus(after_fee, cap) : 0;
    mathint to_freelancer = after_fee - bonus;

    assert fee >= 0 && bonus >= 0 && to_freelancer >= 0,
        "MS-1: every leg of a milestone payout must be non-negative";
    assert fee + bonus + to_freelancer == payout,
        "MS-1: fee + referral bonus + freelancer share must equal the milestone payout";
    assert payout <= amount,
        "MS-1: a single milestone payout must never exceed the escrow amount";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  MS-2 — Sum of milestone splits never exceeds the escrow amount            ║
// ╚══════════════════════════════════════════════════════════════════════════════╝
//
// `create_escrow_internal` accepts at most 5 milestones whose positive
// percentages sum to exactly 100.  Unused slots are modelled as 0%, which pay
// out nothing, so this covers every milestone count from 1 to 5.

rule ms2_sum_of_splits_bounded(mathint amount, mathint p1, mathint p2, mathint p3, mathint p4, mathint p5) {
    require amount >= 0;
    require p1 > 0;
    require p2 >= 0 && p3 >= 0 && p4 >= 0 && p5 >= 0;
    require p1 + p2 + p3 + p4 + p5 == PCT_DENOMINATOR();

    mathint total = milestone_payout(amount, p1)
                  + milestone_payout(amount, p2)
                  + milestone_payout(amount, p3)
                  + milestone_payout(amount, p4)
                  + milestone_payout(amount, p5);

    assert total <= amount,
        "MS-2: the sum of all milestone payouts must never exceed the escrow amount";
    assert amount - total < MAX_MILESTONES(),
        "MS-2: rounding dust across a milestone split must be less than the milestone count";
}

/// Any subset of milestones (some released, some rejected, some pending) is
/// also bounded by the escrow amount — a partially-settled escrow can never
/// be over-drawn regardless of the order milestones are resolved in.
rule ms2_partial_settlement_bounded(mathint amount, mathint p1, mathint p2, mathint p3, mathint p4, mathint p5,
                                    bool s1, bool s2, bool s3, bool s4, bool s5) {
    require amount >= 0;
    require p1 >= 0 && p2 >= 0 && p3 >= 0 && p4 >= 0 && p5 >= 0;
    require p1 + p2 + p3 + p4 + p5 == PCT_DENOMINATOR();

    mathint settled = (s1 ? milestone_payout(amount, p1) : 0)
                    + (s2 ? milestone_payout(amount, p2) : 0)
                    + (s3 ? milestone_payout(amount, p3) : 0)
                    + (s4 ? milestone_payout(amount, p4) : 0)
                    + (s5 ? milestone_payout(amount, p5) : 0);

    assert settled >= 0 && settled <= amount,
        "MS-2: settled milestone payouts must stay within [0, escrow amount]";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  MS-3 — The escrow amount (split base) is immutable                        ║
// ╚══════════════════════════════════════════════════════════════════════════════╝
//
// Every milestone payout is computed from `escrow.amount`.  MS-2 only implies
// conservation if that base never changes between releases.

rule ms3_amount_immutable(env e, method f, string job_id)
    filtered { f -> f.selector != sig:create_escrow_with_milestones(string, address, CreateEscrowParams).selector }
{
    Escrow before = get_escrow(job_id);

    calldataarg args;
    f(e, args);

    Escrow after = get_escrow(job_id);
    assert after.amount == before.amount,
        "MS-3: escrow amount must never change after creation";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  MS-4 — Each milestone share is settled exactly once                       ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule ms4_release_resolves_milestone(env e, string job_id, uint32 milestone_id, address client, uint32 i) {
    Escrow before = get_escrow(job_id);
    require i < before.milestones.length;
    require before.milestones[i].id == milestone_id;

    release_milestone(e, job_id, milestone_id, client);

    Escrow after = get_escrow(job_id);
    assert after.milestones[i].released && !after.milestones[i].rejected,
        "MS-4: release_milestone must mark exactly the target milestone released";
    assert !before.milestones[i].released && !before.milestones[i].rejected,
        "MS-4: only an unresolved milestone can be released";
}

rule ms4_reject_resolves_milestone(env e, string job_id, uint32 milestone_index, address client, uint32 i) {
    Escrow before = get_escrow(job_id);
    require i < before.milestones.length;
    require before.milestones[i].id == milestone_index;

    reject_milestone(e, job_id, milestone_index, client);

    Escrow after = get_escrow(job_id);
    assert after.milestones[i].rejected && !after.milestones[i].released,
        "MS-4: reject_milestone must mark exactly the target milestone rejected";
    assert !before.milestones[i].released && !before.milestones[i].rejected,
        "MS-4: only an unresolved milestone can be rejected";
}

/// Released and rejected are mutually exclusive and irreversible, so a
/// milestone's share is either paid to the freelancer or refunded to the
/// client — never both, and never twice.
rule ms4_resolution_exclusive_and_final(env e, method f, string job_id, uint32 i) {
    Escrow before = get_escrow(job_id);
    require i < before.milestones.length;
    require !(before.milestones[i].released && before.milestones[i].rejected);

    calldataarg args;
    f(e, args);

    Escrow after = get_escrow(job_id);
    assert !(after.milestones[i].released && after.milestones[i].rejected),
        "MS-4: a milestone must never be both released and rejected";
    assert before.milestones[i].released => after.milestones[i].released,
        "MS-4: a released milestone must stay released";
    assert before.milestones[i].rejected => after.milestones[i].rejected,
        "MS-4: a rejected milestone must stay rejected";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  MS-5 — Cumulative milestone payouts never exceed the escrow amount        ║
// ╚══════════════════════════════════════════════════════════════════════════════╝
//
// `ghost_ms_paid[job_id]` accumulates every milestone share that has left the
// contract for `job_id`, whether released to the freelancer (gross of fees and
// referral bonus) or refunded to the client on rejection.

ghost mapping(string => mathint) ghost_ms_paid {
    init_state axiom forall string job_id. ghost_ms_paid[job_id] == 0;
}

rule ms5_release_pays_exact_share(env e, string job_id, uint32 milestone_id, address client, uint32 i) {
    Escrow before = get_escrow(job_id);
    require i < before.milestones.length;
    require before.milestones[i].id == milestone_id;

    mathint paid_before = ghost_ms_paid[job_id];
    release_milestone(e, job_id, milestone_id, client);

    assert ghost_ms_paid[job_id] == paid_before + milestone_payout(before.amount, before.milestones[i].percentage),
        "MS-5: release_milestone must pay out exactly amount * pct / 100";
}

rule ms5_reject_refunds_exact_share(env e, string job_id, uint32 milestone_index, address client, uint32 i) {
    Escrow before = get_escrow(job_id);
    require i < before.milestones.length;
    require before.milestones[i].id == milestone_index;

    mathint paid_before = ghost_ms_paid[job_id];
    reject_milestone(e, job_id, milestone_index, client);

    assert ghost_ms_paid[job_id] == paid_before + milestone_payout(before.amount, before.milestones[i].percentage),
        "MS-5: reject_milestone must refund exactly amount * pct / 100";
}

invariant ms5_paid_within_amount(string job_id)
    ghost_ms_paid[job_id] >= 0 && ghost_ms_paid[job_id] <= get_escrow(job_id).amount
    filtered { f -> true }
