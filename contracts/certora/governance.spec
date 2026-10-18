/*
 * contracts/certora/governance.spec
 *
 * Certora Verification Language (CVL) specification for the governance
 * quorum rules in `contracts/marketpay-contract/src/governance.rs`.
 *
 * This spec formally verifies the following properties:
 *
 *   GQ-1 (Arithmetic): Quorum is monotone — more turnout never un-meets
 *                      quorum; a lower threshold or a smaller electorate never
 *                      un-meets quorum.
 *   GQ-2 (Property):   Vote tallies only grow: `cast_vote` adds exactly one
 *                      vote, and no function ever decreases a tally.
 *   GQ-3 (Property):   The quorum denominator `EligibleVoterCount` never
 *                      decreases.
 *   GQ-4 (Property):   The quorum threshold stays within
 *                      [0, MAX_QUORUM_THRESHOLD_BPS] and only `set_quorum` may
 *                      change it.
 *   GQ-5 (Property):   A resolved proposal is final (tallies and outcome are
 *                      frozen), and a passing outcome implies quorum was met
 *                      with a strict majority at resolution time.
 *
 * Run with:
 *   certoraRun contracts/certora/governance.conf
 *
 * ── Verification strategy ────────────────────────────────────────────────────
 *
 * GQ-1 restates `quorum_met` (`turnout * 10_000 >= eligible * threshold_bps`)
 * over `mathint`.  GQ-2 … GQ-5 are checked against observable contract state
 * via the envfree getters `get_proposal`, `get_eligible_voter_count` and
 * `get_quorum_threshold_bps`.
 */

methods {
    // ── Governance (mutating) ────────────────────────────────────────────────
    function create_proposal(address proposer, string title, string description, uint32 duration_ledgers) returns uint32;
    function cast_vote(address voter, uint32 proposal_id, bool approve) expect void;
    function resolve_proposal(uint32 proposal_id) expect void;
    function execute_proposal(uint32 proposal_id) expect void;
    function propose_quorum_change(address proposer, uint32 new_threshold_bps, string description, uint32 duration_ledgers) returns uint32;
    function set_quorum(address admin, uint32 proposal_id, uint32 new_threshold_bps) expect void;

    // ── Getters / Views ──────────────────────────────────────────────────────
    function get_proposal(uint32 id)          returns Proposal envfree;
    function get_quorum_threshold_bps()       returns uint32   envfree;
    function get_eligible_voter_count()       returns uint32   envfree;
}

// ─── Contract constants (mirroring types.rs) ─────────────────────────────────
definition BPS_DENOMINATOR()          returns mathint = 10000;
definition MAX_QUORUM_THRESHOLD_BPS() returns mathint = 5000;

/// `quorum_met` from governance.rs (cross-multiplied, rounds the requirement up).
definition quorum_met(mathint turnout, mathint eligible, mathint threshold_bps) returns bool =
    turnout * BPS_DENOMINATOR() >= eligible * threshold_bps;

definition turnout(Proposal p) returns mathint = p.votes_for + p.votes_against;


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  GQ-1 — Quorum monotonicity                                                ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule gq1_quorum_monotone_in_turnout(mathint t1, mathint t2, mathint eligible, mathint bps) {
    require t1 >= 0 && t2 >= t1;
    require eligible >= 0;
    require bps >= 0 && bps <= MAX_QUORUM_THRESHOLD_BPS();

    assert quorum_met(t1, eligible, bps) => quorum_met(t2, eligible, bps),
        "GQ-1: additional votes must never cause a met quorum to fail";
}

rule gq1_quorum_antitone_in_threshold(mathint t, mathint eligible, mathint bps1, mathint bps2) {
    require t >= 0;
    require eligible >= 0;
    require bps1 >= 0 && bps1 <= bps2 && bps2 <= MAX_QUORUM_THRESHOLD_BPS();

    assert quorum_met(t, eligible, bps2) => quorum_met(t, eligible, bps1),
        "GQ-1: lowering the threshold must never cause a met quorum to fail";
}

rule gq1_quorum_antitone_in_electorate(mathint t, mathint e1, mathint e2, mathint bps) {
    require t >= 0;
    require e1 >= 0 && e2 >= e1;
    require bps >= 0 && bps <= MAX_QUORUM_THRESHOLD_BPS();

    assert quorum_met(t, e2, bps) => quorum_met(t, e1, bps),
        "GQ-1: a smaller electorate must never cause a met quorum to fail";
}

/// The cross-multiplied check rounds the vote requirement up: quorum is met
/// iff turnout reaches ceil(eligible * bps / 10_000).
rule gq1_quorum_rounds_up(mathint t, mathint eligible, mathint bps) {
    require t >= 0;
    require eligible >= 0;
    require bps >= 0 && bps <= MAX_QUORUM_THRESHOLD_BPS();

    mathint required = (eligible * bps + BPS_DENOMINATOR() - 1) / BPS_DENOMINATOR();

    assert quorum_met(t, eligible, bps) <=> t >= required,
        "GQ-1: quorum must require ceil(eligible * bps / 10000) votes";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  GQ-2 — Vote tallies only grow                                             ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule gq2_cast_vote_adds_exactly_one(env e, address voter, uint32 proposal_id, bool approve) {
    Proposal before = get_proposal(proposal_id);

    cast_vote(e, voter, proposal_id, approve);

    Proposal after = get_proposal(proposal_id);
    assert turnout(after) == turnout(before) + 1,
        "GQ-2: cast_vote must increase turnout by exactly one";
    assert approve  => (after.votes_for == before.votes_for + 1 && after.votes_against == before.votes_against),
        "GQ-2: an approving vote must only increment votes_for";
    assert !approve => (after.votes_against == before.votes_against + 1 && after.votes_for == before.votes_for),
        "GQ-2: a rejecting vote must only increment votes_against";
}

rule gq2_tallies_never_decrease(env e, method f, uint32 proposal_id) {
    Proposal before = get_proposal(proposal_id);

    calldataarg args;
    f(e, args);

    Proposal after = get_proposal(proposal_id);
    assert after.votes_for >= before.votes_for && after.votes_against >= before.votes_against,
        "GQ-2: no function may decrease a proposal's vote tallies";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  GQ-3 — The quorum denominator never decreases                             ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule gq3_eligible_voters_never_decrease(env e, method f) {
    mathint before = get_eligible_voter_count();

    calldataarg args;
    f(e, args);

    assert get_eligible_voter_count() >= before,
        "GQ-3: EligibleVoterCount must never decrease";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  GQ-4 — Quorum threshold bounds and write path                             ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

invariant gq4_threshold_within_bounds()
    get_quorum_threshold_bps() <= MAX_QUORUM_THRESHOLD_BPS()
    filtered { f -> true }

rule gq4_only_set_quorum_changes_threshold(env e, method f)
    filtered { f -> f.selector != sig:set_quorum(address, uint32, uint32).selector }
{
    mathint before = get_quorum_threshold_bps();

    calldataarg args;
    f(e, args);

    assert get_quorum_threshold_bps() == before,
        "GQ-4: only set_quorum may change the quorum threshold";
}

rule gq4_set_quorum_requires_passed_proposal(env e, address admin, uint32 proposal_id, uint32 bps) {
    Proposal p = get_proposal(proposal_id);
    require !p.resolved || !p.result;

    set_quorum@withrevert(e, admin, proposal_id, bps);
    assert lastReverted,
        "GQ-4: set_quorum must revert unless the bound proposal has passed";
}


// ╔══════════════════════════════════════════════════════════════════════════════╗
// ║  GQ-5 — Resolution is final and respects quorum                            ║
// ╚══════════════════════════════════════════════════════════════════════════════╝

rule gq5_resolved_proposal_is_final(env e, method f, uint32 proposal_id) {
    Proposal before = get_proposal(proposal_id);
    require before.resolved;

    calldataarg args;
    f(e, args);

    Proposal after = get_proposal(proposal_id);
    assert after.resolved
        && after.result == before.result
        && after.votes_for == before.votes_for
        && after.votes_against == before.votes_against,
        "GQ-5: a resolved proposal's tallies and outcome must be frozen";
}

rule gq5_pass_implies_quorum_and_majority(env e, uint32 proposal_id) {
    mathint eligible = get_eligible_voter_count();
    mathint bps      = get_quorum_threshold_bps();

    resolve_proposal(e, proposal_id);

    Proposal p = get_proposal(proposal_id);
    assert p.resolved, "GQ-5: resolve_proposal must mark the proposal resolved";
    assert p.result <=> (quorum_met(turnout(p), eligible, bps) && p.votes_for > p.votes_against),
        "GQ-5: a proposal passes iff quorum is met and votes_for strictly exceeds votes_against";
}
