import Mathlib

/-!
# What a zkVM system is

The abstract packaging every concrete VM instantiates: a state type with a step
predicate, a fixed step count, a private-input type, mappings to initial and
terminal states, a final verifier, and the trace-validity predicate over it.

A **private input** is data the prover knows but the verifier never sees.
Deterministic VMs take `PrivInput := Unit` and ignore it; a non-deterministic
VM uses it to complete the initial state (say, as a read-only list of words the
program can load into registers) and reflects it in the terminal state as well,
so the statement contains only the public part of either boundary.

This file deliberately depends on nothing but Mathlib. What the system is meant
to *prove* — the correct-execution relation `R*`, correct-trace extractability,
and the keystone equivalence with knowledge soundness — is the specification
proper and lives in `Cte.lean`, which is the only file in `Specification/` that
needs the argument-system kernel.

## Main definitions
* an abstract `ZkVM` system (compare the zkVM of the vanilla document, stripped
  to what the security statement needs);
* `ZkVM.TraceValid`, the validity of a candidate execution trace for a statement.

Concrete systems (the two-step toy in `VMs/TwoStep/`, later the full vanilla VM)
instantiate `ZkVM` and prove `CTE` from `Cte.lean`.
-/

namespace VanillaZkVM

/-! ## Abstract zkVM systems -/

/-- An abstract zkVM system: a state type with a step predicate, a fixed step
count `T`, a statement type, a private-input type, `initial`/`terminal`
mappings that may consult the private input, and the final proof
type with its verifier.

The mappings `initial`/`terminal` map the statement (what the verifier sees) and
the private input (what only the prover sees) to an initial and terminal state
of the computation.

This is abstract packaging, motivated by `def:zkvm` and corrected `def:cte` at the
revision pinned in `docs/PAPER_REVISION.md`; a full formalization of `def:zkvm`
is the job of a concrete VM instance, not of this record. At the pinned revision,
program code and `T` are fixed system parameters rather than adversary outputs —
which is why `T` is a field here. Code is absent because the abstract step
predicate already closes over it.

`PrivInput` generalizes the paper: `def:zkvm` and `def:cte` have no private
inputs, and their statements determine both boundary states outright. A
deterministic VM recovers that reading with `PrivInput := Unit` and projections
that ignore their second argument. -/
structure ZkVM where
  State : Type
  step : State → State → Prop
  T : ℕ
  Stmt : Type
  PrivInput : Type -- `Unit` for a deterministic VM.
  initial : Stmt → PrivInput → State
  terminal : Stmt → PrivInput → State
  Proof : Type
  verify : Stmt → Proof → Prop

namespace ZkVM

variable (V : ZkVM)

/-- A candidate trace `tr` is **valid** for statement `x` under private input
`w` when it starts at the initial state determined by `x` and `w`, ends after
`T` steps at the terminal state determined by `x` and `w`, and every step
satisfies `step`.

Paper: the winning condition of `def:cte` and the step conjunct of
`eq:relation-star`, generalized by the private input `w`; for a deterministic
VM (`PrivInput := Unit`) the two coincide. -/
def TraceValid (x : V.Stmt) (w : V.PrivInput) (tr : ℕ → V.State) : Prop :=
  tr 0 = V.initial x w ∧ tr V.T = V.terminal x w ∧
  ∀ i, i < V.T → V.step (tr i) (tr (i + 1))

end ZkVM

end VanillaZkVM
