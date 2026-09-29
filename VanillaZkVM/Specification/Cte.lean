import VanillaZkVM.Preliminaries.ArgumentSystem
import VanillaZkVM.Specification.Zkvm

/-!
# Correct-trace extractability — the specification (the abstract heart)

This is the central file: what an abstract `ZkVM` (from `Zkvm.lean`) is *meant to
prove*, and its equivalence with the frozen knowledge-soundness notion.

## Main definitions
* the correct-execution relation `Rstar` the system is meant to prove, and the
  final argument system `ASstar` viewed as an argument system for it;
* correct-trace extractability `CTE`, stated in VM-native terms.

## Main results
* The keystone theorem `cte_iff_knowledgeSound`:
  `CTE V ↔ KnowledgeSound V.ASstar`.

Concrete systems (the two-step toy in `VMs/TwoStep/`, later the full vanilla VM)
instantiate `ZkVM` and prove `CTE` — typically by proving `KnowledgeSound ASstar`
and invoking the equivalence.
-/

namespace VanillaZkVM

namespace ZkVM

variable (V : ZkVM)

/-- The correct-execution relation `R*`: statements are boundary claims,
witnesses are a private input together with a trace, membership is trace
validity under that private input.

Paper: `eq:relation-star`, whose witness is the trace alone; the private-input
component is the Lean generalization and is trivial for a deterministic VM. -/
def Rstar : Relation where
  Stmt := V.Stmt
  Wit := V.PrivInput × (ℕ → V.State)
  rel := fun x wt => V.TraceValid x wt.1 wt.2

/-- The system's final argument system, viewed as an argument system for `R*`. -/
def ASstar : ArgumentSystem V.Rstar where
  Proof := V.Proof
  verify := V.verify

/-- **Correct-trace extractability** (VM-native form): a single extractor turns
every accepting proof into a private input and a valid `T`-step execution of the
claim under that private input.

Paper: `def:cte` in `docs/vanillaVM.pdf`. This is its
perfect, probability-free core: PPT/probability bookkeeping is out of scope (I8),
and the full-memory boundary commitment equations belong to a concrete VM instance
rather than to this abstract statement. The paper's extractor returns only the
trace; the private-input component is the Lean generalization, and for a
deterministic VM it carries no information. -/
def CTE : Prop :=
  ∃ E : V.Stmt → V.Proof → V.PrivInput × (ℕ → V.State),
    ∀ (x : V.Stmt) (p : V.Proof), V.verify x p → V.TraceValid x (E x p).1 (E x p).2

/-- **Keystone.** Correct-trace extractability is exactly knowledge soundness of
the final argument system for the correct-execution relation `R*`. The proof is
structural: both sides are "∃ extractor, ∀ accepting (x, p), the output is a
private input and a valid trace", differing only in packaging the extractor as a
bare function versus an `Extractor` record.

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
