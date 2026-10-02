import «recursion-topology-fv».Specification.Zkvm

/-!
# Step-interface contract

A VM's execution appears at three levels of detail: ordinary execution over
full states, execution over memory commitments that a SNARK can check, and a
predicate that also includes bus data. This module records how those
levels must relate, so later files do not introduce unrelated predicates all
called "step." It states the required properties; concrete VM files prove them.

## Main definitions
* `StepInterface` — a committed predicate and representation relation attached
  to the single plain predicate `ZkVM.step`.
* `StepInterface.BusBridge` — the proposition that a bus-deferred step implies
  the committed step after bus unification.

`TwoStep.System.memoryStepInterface` is the one instance so far. Its
`ZkVM.step` is `ISA.System.stepPlain`.
`Bus.System.stepWithBus_committedOperation` checks the ISA cases and
preserves the segment's explicit memory witness without choosing how segment
proofs are combined. `Bus.TwoStepSystem.busBridge` uses that witness to prove
that the two-layer VM has a suitable memory witness. See
`docs/STEP_INTERFACES.md` for the layer-by-layer map.
-/

namespace VanillaZkVM

/-- Connects the plain step `V.step` of a zkVM to its committed-memory layer.

Not a paper definition. It is shared Lean glue for `eq:step-bus2`,
`prop:memory-extractability` and `lem:segment`. -/
structure StepInterface (V : ZkVM) where
  /-- A state with memory replaced by a commitment. -/
  CommittedState : Type
  /-- `represents Ŝ S` means committed state `Ŝ` represents plain state `S`. -/
  represents : CommittedState → V.State → Prop
  /-- One committed step, from its two end states only. If the step needs operation data or an
  opening proof, this proposition says that such data exists. The bus is not a field: it is a
  parameter of `BusBridge`, so a memory-only instance needs no bus. -/
  stepCommitted : CommittedState → CommittedState → Prop

namespace StepInterface

variable {V : ZkVM} (I : StepInterface V)

/-- The statement required from the bus layer: once the extracted bus/chip data
has been unified into evidence of type `BusEvidence`, the supplied complete
bus-backed predicate implies the canonical committed step. `BusEvidence` and
`stepWithBus` are arguments rather than `StepInterface` fields, so an instance that
only has a memory layer is not forced to name a bus witness type.

`Bus.System.stepWithBus_committedOperation` proves the reusable implication for
the exact `MemStep` recovered from a segment. `Bus.TwoStepSystem.busBridge` is
the concrete two-layer result: it uses that exact value to prove that a memory
witness exists. Inner-proof extraction and collision resistance first establish
`stepWithBus` for one common segment bus. The reusable theorem then checks the
selected ISA case, and the concrete bridge supplies the same `MemStep` as the
required witness.

Paper target: `lem:segment`, feeding `prop:memory-extractability`. -/
def BusBridge {BusEvidence : Type}
    (stepWithBus : I.CommittedState → I.CommittedState → BusEvidence → Prop) : Prop :=
  ∀ (Ŝ₁ Ŝ₂ : I.CommittedState) (b : BusEvidence),
    stepWithBus Ŝ₁ Ŝ₂ b → I.stepCommitted Ŝ₁ Ŝ₂

end StepInterface

end VanillaZkVM
