import «recursion-topology-fv».Preliminaries.ArgumentSystem
import «recursion-topology-fv».Specification.Zkvm

/-!
# Correct-trace extractability

`CTE` is the security goal of a `ZkVM` (from `Zkvm.lean`): for every valid proof, an extractor
can recover a private input and a valid execution trace.

This file also provides a theorem that shows equivalence with knowledge soundness.

## Main definitions
* the correct-execution relation `Rstar` the system is meant to prove, and the
  final argument system `ASstar` viewed as an argument system for it;
* correct-trace extractability `CTE`, stated in VM-native terms.

## Main results
* The keystone theorem `cte_iff_knowledgeSound`: `CTE V ↔ KnowledgeSound V.ASstar`.

Concrete systems (e.g. the VanillaVM) instantiate `ZkVM` and prove `CTE` —
typically by proving `KnowledgeSound ASstar` and invoking the equivalence.
-/

namespace VanillaZkVM

namespace ZkVM

variable (V : ZkVM)

/-- The correct-execution relation `R*`.

* Statement: the public statement `x`
* Witness: private input `w` and a trace `tr`.

`x` and `w` together fix the start state `initial x w` and the end state
`terminal x w`.

`(x, (w, tr)) ∈ R*` iff `tr` is a valid trace from the start state to the end state.

Unlike the paper, the witness includes private input `w`. This is meant to model non-deterministic zkVMs. -/
def Rstar : Relation where
  Stmt := V.Stmt
  Wit := V.PrivInput × (ℕ → V.State)
  rel := fun x wt => V.TraceValid x wt.1 wt.2

/-- The system's final argument system, viewed as an argument system for `R*`. -/
def ASstar : ArgumentSystem V.Rstar where
  Proof := V.Proof
  verify := V.verify

/-- **Correct-trace extractability**: an extractor turns every accepting proof into a private input and a valid `T`-step execution of the
claim under that private input. -/
def CTE : Prop :=
  ∃ E : V.Stmt → V.Proof → V.PrivInput × (ℕ → V.State),
    ∀ (x : V.Stmt) (p : V.Proof), V.verify x p → V.TraceValid x (E x p).1 (E x p).2

/-- **Keystone.** Correct-trace extractability is equivalent to knowledge soundness of
the final argument system for `R*`.

Paper: `rem:cte-ks`. -/
theorem cte_iff_knowledgeSound : V.CTE ↔ KnowledgeSound V.ASstar := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨⟨E⟩, ?_⟩
    intro x p hp
    exact hE x p hp
  · rintro ⟨E, hE⟩
    refine ⟨E.extract, ?_⟩
    intro x p hp
    exact hE x p hp

end ZkVM

end VanillaZkVM
