# Formal Verification with Certora

This document describes how to run formal verification on the **Stellar MarketPay Escrow Contract** using the [Certora Prover](https://docs.certora.com).

## Overview

We use Certora's **CVL (Certora Verification Language)** to mathematically prove critical safety properties of the contract across four specifications:

### Escrow Lifecycle (`escrow.spec`)

| Property | Acceptance Criterion | Description |
|----------|---------------------|-------------|
| **AC-1** | `total funds held >= sum of all funded escrows` | The contract never creates or destroys tokens — it only holds them in escrow. A ghost variable `ghost_locked` tracks the sum of all active escrow amounts. The invariant asserts that `ghost_locked` is always non-negative and is correctly updated on every escrow operation. |
| **AC-2** | `funds cannot be released to a non-freelancer address` | The `freelancer` field in an `Escrow` is immutable after creation. Only the designated client may initiate a release, and the funds always flow to the freelancer (minus platform fees and referral bonuses). |
| **AC-3** | `an escrow can only be released once` | Once an escrow reaches a terminal status (`Released` or `Refunded`), all further attempts to release, refund, or mutate its status must revert. This prevents double-spending. |

### Milestone Percentage Math (`milestones.spec`)

| Property | Acceptance Criterion | Description |
|----------|---------------------|-------------|
| **MS-1** | `fee + referral bonus + freelancer share == payout` | Every leg of a single milestone payout (`amount * pct / 100`) is non-negative and their sum equals the milestone payout without exceeding the escrow amount. |
| **MS-2** | `sum of milestone splits <= escrow amount` | For any split of up to 5 positive percentages summing to 100, the total payout across all milestones (or any partially settled subset) never exceeds the escrow amount, and rounding dust is strictly less than the milestone count. |
| **MS-3** | `escrow.amount is immutable` | The escrow principal used as the denominator base for every milestone percentage calculation never changes after creation. |
| **MS-4** | `milestone resolution is exclusive and final` | Releasing or rejecting a milestone resolves only that milestone; no milestone can be both released and rejected, and resolved flags never revert. |
| **MS-5** | `cumulative milestone payouts <= escrow amount` | Per-job ghost tracking (`ghost_ms_paid`) verifies that each release/rejection pays out the exact percentage share and cumulative payouts stay within `[0, escrow.amount]`. |

### Dispute Bond Accounting (`disputes.spec`)

| Property | Acceptance Criterion | Description |
|----------|---------------------|-------------|
| **DB-1** | `arbitrator fee + winner share + loser share == escrow amount` | Dispute split arithmetic conserves the full escrow principal across arbitrator fee, winner payout, and loser payout. |
| **DB-2** | `disputes settle an escrow at most once` | Raising or resolving a dispute preserves `escrow.amount`, transitions status to `Disputed` / `Released`, and rejects double resolution or out-of-range split/fee parameters. |
| **DB-3** | `bond refund / slash exclusivity` | A locked dispute bond is either refunded (`bond_rtn`) **or** slashed (`bond_slsh`) — never both and never more than once — for the exact locked amount, while unbonded disputes pay out zero bond. |
| **DB-4** | `settled bond always goes to the winner` | Whether refunded to a winning bond-caller or slashed from a losing bond-caller, the bond recipient is always the dispute `winner`. |

### Governance Quorum Rules (`governance.spec`)

| Property | Acceptance Criterion | Description |
|----------|---------------------|-------------|
| **GQ-1** | `quorum monotonicity` | Increasing voter turnout, lowering `threshold_bps`, or having a smaller eligible electorate never causes a met quorum (`turnout * 10_000 >= eligible * threshold_bps`) to fail; the cross-multiplied check is equivalent to `turnout >= ceil(eligible * bps / 10_000)`. |
| **GQ-2** | `vote tallies are monotonically non-decreasing` | `cast_vote` increments total turnout by 1 (`votes_for` or `votes_against`), and no contract operation ever decreases a proposal's vote tallies. |
| **GQ-3** | `EligibleVoterCount never decreases` | The quorum denominator (`EligibleVoterCount`) is monotonically non-decreasing across all contract operations. |
| **GQ-4** | `quorum threshold bounds and governance gate` | `QuorumThresholdBps` never exceeds `MAX_QUORUM_THRESHOLD_BPS` (5000 bps), can only be modified by `set_quorum`, and requires a resolved, passed proposal. |
| **GQ-5** | `proposal resolution is final and enforces quorum + majority` | Once resolved, a proposal's tallies and outcome are immutable, and `result == true` holds if and only if quorum was met and `votes_for > votes_against`. |

## Files

| File | Purpose |
|------|---------|
| `contracts/certora/escrow.spec` | CVL specification for core escrow lifecycle invariants and rules (AC-1 .. AC-3) |
| `contracts/certora/milestones.spec` | CVL specification for milestone percentage split conservation (MS-1 .. MS-5) |
| `contracts/certora/disputes.spec` | CVL specification for dispute split conservation and bond refund/slash exclusivity (DB-1 .. DB-4) |
| `contracts/certora/governance.spec` | CVL specification for governance quorum monotonicity and tally rules (GQ-1 .. GQ-5) |
| `contracts/certora/config.conf` | Certora Prover configuration for `escrow.spec` |
| `contracts/certora/milestones.conf` | Certora Prover configuration for `milestones.spec` |
| `contracts/certora/disputes.conf` | Certora Prover configuration for `disputes.spec` |
| `contracts/certora/governance.conf` | Certora Prover configuration for `governance.spec` |
| `contracts/marketpay-contract/src/lib.rs` | The Soroban smart contract source (verification target) |

## Prerequisites

1. **Install the Certora CLI** — the Certora Prover is distributed as a Python package. Follow the [official Certora installation guide](https://docs.certora.com/en/latest/docs/user-guide/getting-started/install.html) to download and set up the `certoraRun` command.

   ```bash
   pip install certora-cli
   ```

   > **Note:** You need **Python 3.8+** and **Java JDK 11+** installed on your machine.

2. **Obtain your Certora API key** (required for both local runs and CI):

   1. Go to [https://www.certora.com](https://www.certora.com) and sign up for an account (free tier available for open-source projects).
   2. After logging in, navigate to **Dashboard → API Keys** (or visit [https://prover.certora.com/settings](https://prover.certora.com/settings) directly).
   3. Click **Create API Key**. Give it a descriptive name (e.g., `stellar-marketpay-local` or `ci-actions`).
   4. Copy the generated key immediately — it is shown only once.
   5. Export it in your shell:

   ```bash
   export CERTORAKEY="your-api-key-here"
   ```

   > **For CI:** Add the key as a repository secret named `CERTORAKEY` in **Settings → Secrets and variables → Actions**. The GitHub Actions workflow (`.github/workflows/certora.yml`) reads it automatically.

3. **Build the Soroban contract** (Certora verifies the Rust source, but a build is needed for dependency resolution):

   ```bash
   cd contracts/marketpay-contract
   cargo build --target wasm32v1-none --release
   cd ../..
   ```

## Running Verification

### Full verification (all specs)

From the **project root**, run each configuration:

```bash
certoraRun contracts/certora/config.conf
certoraRun contracts/certora/milestones.conf
certoraRun contracts/certora/disputes.conf
certoraRun contracts/certora/governance.conf
```

Expected output for `config.conf` (`escrow.spec`):

```
✅ ac1_create_escrow_increases_ghost               PASSED
✅ ac1_create_with_deliverable_increases_ghost      PASSED
✅ ac1_create_with_milestones_increases_ghost       PASSED
✅ ac1_release_decreases_ghost                      PASSED
✅ ac1_release_with_conversion_decreases_ghost      PASSED
✅ ac1_release_milestone_decreases_ghost            PASSED
✅ ac1_reject_milestone_decreases_ghost             PASSED
✅ ac1_refund_decreases_ghost                       PASSED
✅ ac1_timeout_refund_decreases_ghost               PASSED
✅ ac1_resolve_dispute_decreases_ghost              PASSED
✅ ac1_start_work_preserves_ghost                   PASSED
✅ ac1_freeze_preserves_ghost                       PASSED
✅ ac1_unfreeze_preserves_ghost                     PASSED
✅ ac1_ghost_locked_nonnegative                     PASSED (invariant)
✅ ac2_only_client_can_release                      PASSED
✅ ac2_only_client_can_release_with_conversion      PASSED
✅ ac2_only_client_can_release_milestone            PASSED
✅ ac2_only_client_can_reject_milestone             PASSED
✅ ac2_only_client_can_refund                       PASSED
✅ ac2_only_client_can_timeout_refund               PASSED
✅ ac2_freelancer_matches_at_creation               PASSED
✅ ac2_freelancer_never_mutated                     PASSED
✅ ac3_cannot_release_twice                         PASSED
✅ ac3_cannot_release_with_conversion_twice         PASSED
✅ ac3_refunded_cannot_be_released                  PASSED
✅ ac3_refunded_cannot_be_refunded_again            PASSED
✅ ac3_refunded_cannot_be_timeout_refunded          PASSED
✅ ac3_released_state_irreversible                  PASSED
✅ ac3_milestone_cannot_be_released_twice_full      PASSED
✅ ac3_milestone_cannot_be_rejected_twice_full      PASSED
✅ ac3_released_cannot_start_work                   PASSED
✅ ac3_released_cannot_be_refunded                  PASSED
✅ ac3_disputed_cannot_be_released                  PASSED
✅ ac3_disputed_cannot_be_refunded                  PASSED
✅ valid_transition_from_locked                     PASSED
✅ valid_transition_from_in_progress                PASSED
```

### Verifying a specific rule

To run a single rule (useful during development):

```bash
certoraRun contracts/certora/config.conf --rule ac3_cannot_release_twice
certoraRun contracts/certora/milestones.conf --rule ms2_sum_of_splits_bounded
certoraRun contracts/certora/disputes.conf --rule db3_resolve_refunds_xor_slashes
certoraRun contracts/certora/governance.conf --rule gq1_quorum_monotone_in_turnout
```

### Verifying only invariant rules

```bash
certoraRun contracts/certora/config.conf --rule ac1_
```

## Spec Structure

```
contracts/certora/
├── escrow.spec (config.conf)
│   ├── AC-1: Total Funds Invariant (ghost_locked)
│   ├── AC-2: Freelancer-Only Release & Immutability
│   ├── AC-3: Single Release & Terminal Status Irreversibility
│   └── Supplementary: State-Transition Sanity
├── milestones.spec (milestones.conf)
│   ├── MS-1: Single Milestone Payout Conservation (fee + bonus + freelancer == payout)
│   ├── MS-2: Sum of Splits & Partial Settlement Bounded by Escrow Amount
│   ├── MS-3: Escrow Amount Immutability
│   ├── MS-4: Exclusive & Irreversible Milestone Resolution
│   └── MS-5: Cumulative Milestone Payout Invariant (ghost_ms_paid)
├── disputes.spec (disputes.conf)
│   ├── DB-1: Dispute Split Conservation (arbitrator fee + winner + loser == amount)
│   ├── DB-2: Single Dispute Settlement & Input Bounds
│   ├── DB-3: Bond Refund XOR Slash Exclusivity & At-Most-Once Invariant
│   └── DB-4: Bond Settlement Recipient Is Always the Winner
└── governance.spec (governance.conf)
    ├── GQ-1: Quorum Monotonicity (turnout, threshold, electorate, ceiling equivalence)
    ├── GQ-2: Monotonic Vote Tallies
    ├── GQ-3: Monotonic EligibleVoterCount Denominator
    ├── GQ-4: Quorum Threshold Bounds & Governance Gate
    └── GQ-5: Finality of Resolved Proposals & Quorum + Majority Enforcement
```

## Interpreting Results

- **PASSED** (green ✅) — The rule holds for **all** possible inputs and execution paths. The property is mathematically proven.
- **VIOLATED** (red ❌) — The Prover found a counterexample. It will print a call trace showing the exact sequence of function calls that break the rule. Use this to diagnose the bug.
- **TIMEOUT** (yellow ⏱️) — The Prover could not conclude within the time limit. Try increasing `loop_iter` in `config.conf` or simplifying the rule.
- **UNKNOWN** (gray ❓) — The Prover could not determine the result (e.g., due to non-linear arithmetic). Consider adding assumptions or splitting complex rules.

## Troubleshooting

### "Escrow not found" in counterexamples

If the Prover reports violations related to missing escrows, ensure the rule's `require` statements properly constrain the job_id to an existing escrow. Use `get_status(e, job_id)` to check existence implicitly (it panics on missing escrows, so Certora will avoid those paths).

### Timeouts on complex rules

1. Increase `loop_iter` in `config.conf` (e.g., from `2` to `3`).
2. Split large rules into smaller, focused rules.
3. Add tighter `require` constraints to reduce the search space.

### Ghost variable inconsistencies

Ghost variables are not part of the actual contract state — they exist only in the verification model. If a rule fails with a ghost-related assertion, check that every function that modifies the tracked state also updates the ghost variable.

## CI/CD Integration

Formal verification runs automatically via [`.github/workflows/certora.yml`](../.github/workflows/certora.yml):

- **On push/PR** — triggered when files change under `contracts/marketpay-contract/src/**` or `contracts/certora/**`.
- **Nightly** — scheduled at 03:00 UTC to catch regressions from upstream Soroban SDK changes.
- **Manual** — use **Run workflow** in the Actions tab for ad-hoc verification.

The job requires the `CERTORAKEY` repository secret. See [Obtain your Certora API key](#prerequisites) above for setup instructions.

## References

- [Certora Documentation](https://docs.certora.com)
- [CVL Language Reference](https://docs.certora.com/en/latest/docs/cvl/index.html)
- [Ghost Variables Guide](https://docs.certora.com/en/latest/docs/cvl/ghosts.html)
- [Certora CLI Options](https://docs.certora.com/en/latest/docs/prover/cli/options.html)
- [Stellar Soroban Docs](https://developers.stellar.org/docs/smart-contracts)
