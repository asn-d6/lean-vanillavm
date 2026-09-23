import VanillaZkVM.Specification.Cte

/-!
# Adding a private input to a zkVM

A **non-deterministic** zkVM is one whose boundary states are only partly
public: the missing part is a private input known to the prover alone. This
module builds such a VM from any given zkVM `B`, by hardcoding the private
input, proving with `B`, and then wrapping the proof in a final outer proof.
The wrapper touches neither `B`'s states nor its step predicate.

## Main definitions
* `System` — the public statement, the private input, how the two complete a
  statement of `B`, and the outer proof system.
* `System.ROuter` / `System.ASOuter` — the relation the outer proof must be
  knowledge-sound for, and that argument system.
* `System.toZkVM` — the resulting zkVM: `B`'s execution model under the public
  statement, with private input `sys.PrivInput × B.PrivInput`.

## Main results
* `System.cte` — correct-trace extractability of `B` and knowledge soundness of
  the outer proof give correct-trace extractability of `toZkVM`. The extractor
  returns the extracted private input beside `B`'s extracted trace.

The paper's zkVM is deterministic, so this construction has no paper
counterpart; it is Lean-only. It also leaves open *how* a concrete VM consumes
the private input: that is the job of `embed`. One natural choice writes the
private input into a reserved region of the initial memory, which the fixed
program then reads with ordinary load instructions.
-/

namespace VanillaZkVM
namespace NonDeterministic

/-- The data completing a zkVM `B` with a private input.

`embed x w` is the statement of `B` that the public statement `x` and the
private input `w` together describe. The outer argument system proves knowledge
of such a `w` and of a `B`-proof accepted for `embed x w`. -/
structure System (B : ZkVM) where
  /-- The public statement received by the verifier. -/
  Stmt : Type
  /-- The private input the extractor must recover in addition to `B`'s. -/
  PrivInput : Type
  /-- Hardcode a private input into a public statement to get a statement of `B`. -/
  hardcode : Stmt → PrivInput → B.Stmt
  /-- Proofs of the outer argument system. -/
  OuterProof : Type
  /-- Verifier of the outer argument system. -/
  outerVerify : Stmt → OuterProof → Prop

namespace System

variable {B : ZkVM} (sys : System B)

/-- The relation certified by the outer proof: for the public statement `x`,
a private input `w` and a `B`-proof accepted for the completed statement
`embed x w`. Knowledge soundness for this relation recovers exactly the two
things the extractor of `toZkVM` needs before delegating to `B`. -/
def ROuter : Relation where
  Stmt := sys.Stmt
  Wit := sys.PrivInput × B.Proof
  rel := fun x wp => B.verify (sys.hardcode x wp.1) wp.2

/-- The outer argument system. -/
def ASOuter : ArgumentSystem sys.ROuter where
  Proof := sys.OuterProof
  verify := sys.outerVerify

/-- The zkVM obtained by adding the private input to `B`. Execution is `B`'s:
same states, same step predicate, same step count. The statement is the public
one, the private input pairs the new input with `B`'s, and both boundary
projections are `B`'s applied to the completed statement. A trace is valid for
`x` under `(w, wB)` exactly when it is `B`-valid for `embed x w` under `wB`. -/
def toZkVM : ZkVM where
  State := B.State
  step := B.step
  T := B.T
  Stmt := sys.Stmt
  PrivInput := sys.PrivInput × B.PrivInput
  initial := fun x w => B.initial (sys.hardcode x w.1) w.2
  terminal := fun x w => B.terminal (sys.hardcode x w.1) w.2
  Proof := sys.OuterProof
  verify := sys.outerVerify

/-- **Correct-trace extractability transfers across the wrapper.** From an
accepting outer proof, the outer extractor yields a private input `w` and a
`B`-proof for `embed x w`; `B`'s extractor turns the latter into `B`'s private
input and a valid trace of the completed statement, which is a valid trace of
`toZkVM` for `x` under `(w, ·)`. -/
theorem cte (hB : B.CTE) (hOuter : KnowledgeSound sys.ASOuter) : sys.toZkVM.CTE := by
  obtain ⟨EB, hEB⟩ := hB
  obtain ⟨EO, hEO⟩ := hOuter
  refine ⟨fun x p =>
      let wp := EO.extract x p
      let wt := EB (sys.hardcode x wp.1) wp.2
      ((wp.1, wt.1), wt.2), ?_⟩
  intro x p hp
  exact hEB _ _ (hEO x p hp)

end System
end NonDeterministic
end VanillaZkVM
