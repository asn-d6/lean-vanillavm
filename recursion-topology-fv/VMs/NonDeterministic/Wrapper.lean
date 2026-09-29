import «recursion-topology-fv».Specification.Cte

/-!
# Adding a private input to a zkVM

A **non-deterministic** zkVM is one whose boundary states are only partly
public: the missing part is a private input known to the prover alone. This
module builds such a VM from any given zkVM `Base`, by hardcoding the private
input, proving with `Base`, and then wrapping the proof in a final outer proof.
The wrapper touches neither `Base`'s states nor its step predicate.

## Main definitions
* `System` — the public statement, the private input, how the two complete a
  statement of `Base`, and the outer proof system.
* `System.ROuter` / `System.ASOuter` — the relation the outer proof must be
  knowledge-sound for, and that argument system.
* `System.toZkVM` — the resulting zkVM: `Base`'s execution model under the public
  statement, with private input `sys.PrivInput × B.PrivInput`.

## Main results
* `System.cte` — correct-trace extractability of `Base` and knowledge soundness of
  the outer proof give correct-trace extractability of `toZkVM`. The extractor
  returns the extracted private input beside `Base`'s extracted trace.

The paper's zkVM is deterministic, so this construction has no paper
counterpart; it is Lean-only. It also leaves open *how* a concrete VM consumes
the private input: that is the job of `hardcode`. One natural choice writes the
private input into a reserved region of the initial memory, which the fixed
program then reads with ordinary load instructions.
-/

namespace VanillaZkVM
namespace NonDeterministic

/-- The data completing a zkVM `Base` with a private input.

`hardcode x w` is the statement of `Base` that the public statement `x` and the
private input `w` together describe. The outer argument system proves knowledge
of such a `w` and of a `Base`-proof accepted for `hardcode x w`. -/
structure System (Base : ZkVM) where
  /-- The public statement received by the verifier. -/
  Stmt : Type
  /-- The private input the extractor must recover in addition to `Base`'s. -/
  PrivInput : Type
  /-- Hardcode a private input into a public statement to get a statement of `Base`. -/
  hardcode : Stmt → PrivInput → Base.Stmt
  /-- Proofs of the outer argument system. -/
  OuterProof : Type
  /-- Verifier of the outer argument system. -/
  outerVerify : Stmt → OuterProof → Prop

namespace System

variable {Base : ZkVM} (sys : System Base)

/-- The relation certified by the outer proof: for the public statement `x`,
a private input `w` and a `Base`-proof accepted for the completed statement
`hardcode x w`. Knowledge soundness for this relation recovers exactly the two
things the extractor of `toZkVM` needs before delegating to `Base`. -/
def ROuter : Relation where
  Stmt := sys.Stmt
  Wit := sys.PrivInput × Base.Proof
  rel := fun x wp => Base.verify (sys.hardcode x wp.1) wp.2

/-- The outer argument system. -/
def ASOuter : ArgumentSystem sys.ROuter where
  Proof := sys.OuterProof
  verify := sys.outerVerify

/-- The zkVM obtained by adding the private input to `Base`. Execution is `Base`'s:
same states, same step predicate, same step count. The statement is the public
one, the private input pairs the new input with `Base`'s, and both boundary
projections are `Base`'s applied to the completed statement. A trace is valid for
`x` under `(w, wB)` exactly when it is `Base`-valid for `hardcode x w` under `wB`. -/
def toZkVM : ZkVM where
  State := Base.State
  step := Base.step
  T := Base.T
  Stmt := sys.Stmt
  PrivInput := sys.PrivInput × Base.PrivInput
  initial := fun x w => Base.initial (sys.hardcode x w.1) w.2
  terminal := fun x w => Base.terminal (sys.hardcode x w.1) w.2
  Proof := sys.OuterProof
  verify := sys.outerVerify

/-- **Correct-trace extractability transfers across the wrapper.** From an
accepting outer proof, the outer extractor yields a private input `w` and a
`Base`-proof for `hardcode x w`; `Base`'s extractor turns the latter into `Base`'s private
input and a valid trace of the completed statement, which is a valid trace of
`toZkVM` for `x` under `(w, ·)`. -/
theorem cte (hB : Base.CTE) (hOuter : KnowledgeSound sys.ASOuter) : sys.toZkVM.CTE := by
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
