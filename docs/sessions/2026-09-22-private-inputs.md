# Session 2026-09-22 — private inputs in the specification (non-deterministic VMs, part 1)

## Bootstrap
- **Goal:** `session-goal.md` — generalize the abstract `ZkVM` and `CTE` so that a VM may
  take a private (prover-only) input that the extractor must recover, while keeping every
  existing deterministic VM intact. Not yet in `PLAN.md`; scoped and directed by Benedikt
  in-session.
- **Branch:** `main`, working tree at `58c5461`; changes left uncommitted by request.
- **Read at start:** the entire repository (all Lean modules, `INVARIANTS.md`,
  `CONVENTIONS.md`, `PLAN.md`, `CORRESPONDENCE.md`, `STEP_INTERFACES.md`, the math companion,
  the paper digest).
- **Build at start:** `lake build` green at `58c5461` (8604 jobs), after `lake exe cache get`.

## Design decisions (agreed with Benedikt)
- `ZkVM` gains `PrivInput : Type`; `initial` and `terminal` both take a private input.
  `terminal` must take it too: with the private input stored in the VM state, a
  statement-determined terminal state would expose it.
- `step` does **not** take the private input. A VM that needs it puts it into the state
  (the planned non-deterministic VM does exactly that), and this keeps the frozen
  `StepInterface` signatures unchanged.
- `TraceValid x w tr`; `Rstar.Wit := PrivInput × (ℕ → State)`; the `CTE` extractor returns
  such a pair.
- Deterministic VMs use `PrivInput := Unit` and projections that ignore it.

## What changed
- `Specification/Zkvm.lean`, `Specification/Cte.lean`: the generalization above; the keystone
  proof is unchanged in structure. Docstrings state where the Lean generalizes the paper.
- `VMs/TwoStep/TwoStep.lean`, `VMs/MultiStep/MultiStep.lean`: `toZkVM` sets
  `PrivInput := Unit`; `traceValid_full` is stated under `()`; the `cte` extractors return
  `((), trace)`. `VMs/TwoStep/WithBus.lean`: the `cte` extractor returns the pair.
  `VMs/VanillaVM/VanillaVM.lean` is untouched (it delegates to `MultiStep.cte`).
- `VMs/StepSanity.lean`, `VMs/ISASanity.lean`: the private sanity VMs gain the two fields.
- No new public declarations. No change to `Step.lean`, `Memory.lean`, `ISA.lean`, `Bus.lean`.
- Docs: math companion §0.2 (kernel), §1.4, §4.6, §7.2; README `Specification/` paragraph;
  `INVARIANTS.md` I4 amendment note; `CORRESPONDENCE.md` § note and the `Rstar`/`CTE` rows
  reopened for re-review.

## Axiom / `sorry` ledger diff
- Headline theorems: footprints unchanged; all within `{propext, Classical.choice, Quot.sound}`.
- `sorry`/`sorryAx`/`admit`/new `axiom` added: none.

## CORRESPONDENCE rows touched
- `VanillaZkVM.ZkVM.Rstar` and `VanillaZkVM.ZkVM.CTE`: fidelity cells reopened, reviewer
  cell set to re-review pending (previous sign-off recorded).

## Build at end
- `lake build`: green (8604 jobs).
- `scripts/ci_checks.py --self-test --check-correspondence --check-axioms --check-hygiene`:
  green; 72 correspondence declarations elaborate; 24 project modules pass hygiene.

## Handoff note
- Part 2 (not started, agreed scope for a later session): a non-deterministic VM whose state
  carries a read-only `List Word` of private inputs set by `initial`, with a private-input
  read instruction; then a two-step variant with a CTE proof in which the private input is a
  witness of the final SNARK relation (the VM verifier cannot commit an initial state it does
  not know).
- Reviewer action: re-sign the `Rstar` and `CTE` rows against the generalized statements.
