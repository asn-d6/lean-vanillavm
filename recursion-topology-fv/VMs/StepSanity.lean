import «recursion-topology-fv».Specification.Cte
import «recursion-topology-fv».VMs.Step

/-!
# Sanity model for the abstract zkVM and the step interface

An accepting one-step Boolean toggle model witnesses that the abstract `ZkVM`,
`CTE`, and the step-interface bridge proposition are jointly satisfiable.
The model's step genuinely relates `false` to `true`, and its representation
predicate is equality, so it does not make every proposition `True`. All model
data is private; this module adds no public API.

One model witnesses both layers at once, so this file lives in `VMs/` (it needs
`Step.lean`) even though it also checks `Specification/Cte.lean`'s `ZkVM.CTE`.

## Main results
* The examples below exhibit an accepting one-step zkVM satisfying `CTE`.
* The same model admits `StepInterface.BusBridge`.
-/

namespace VanillaZkVM

private def oneStepZkVM : ZkVM where
  State := Bool
  step := fun pre post => post = !pre
  T := 1
  Stmt := Unit
  PrivInput := Unit
  initial := fun _ _ => false
  terminal := fun _ _ => true
  Proof := Unit
  verify := fun _ _ => True

private def oneStepInterface : StepInterface oneStepZkVM where
  CommittedState := Bool
  represents := fun committed plain => committed = plain
  stepCommitted := fun pre post => post = !pre

private def oneStepWithBus : Bool → Bool → Unit → Prop :=
  fun pre post _ => post = !pre

example : oneStepZkVM.verify () () := by
  trivial

example : oneStepZkVM.CTE := by
  let trace : ℕ → Bool
    | 0 => false
    | _ + 1 => true
  refine ⟨fun _ _ => ((), trace), ?_⟩
  intro x p hp
  refine ⟨rfl, rfl, ?_⟩
  intro i hi
  have hi' : i < 1 := by
    simpa [oneStepZkVM] using hi
  have hi0 : i = 0 := by omega
  subst i
  rfl

example : oneStepInterface.BusBridge oneStepWithBus := by
  intro Ŝ₁ Ŝ₂ b hstep
  exact hstep

end VanillaZkVM
