import Mathlib

/-!
# The definition of an abstract zkVM system

## Main definitions
* ZkVM, an abstract `ZkVM` system
* `ZkVM.TraceValid`, the validity of a candidate execution trace for a statement.

Concrete systems (e.g. the VanillaVM) instantiate `ZkVM` and prove `CTE` from `Cte.lean`.
-/

namespace VanillaZkVM

/-- An abstract zkVM system. -/
structure ZkVM where
  /-- The VM state. -/
  State : Type
  /-- `step s s'` holds when the VM can move from `s` to `s'` in one step. Program code is
  fixed inside this predicate. -/
  step : State → State → Prop
  /-- The fixed number of steps. A system parameter, as in the paper. -/
  T : ℕ
  /-- The public input. The verifier sees it. -/
  Stmt : Type
  /-- Private input to model a non-deterministic zkVM. `Unit` for a deterministic VM. -/
  PrivInput : Type
  /-- The start state, from the statement and the private input. -/
  initial : Stmt → PrivInput → State
  /-- The end state, from the statement and the private input. -/
  terminal : Stmt → PrivInput → State
  /-- The final proof. -/
  Proof : Type
  /-- The final verifier. -/
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
