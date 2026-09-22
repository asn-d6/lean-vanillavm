import VanillaZkVM.VMs.NonDeterministic.Wrapper

/-!
# Consistency-floor model for the private-input wrapper

A one-step counter whose statement fixes both endpoints is wrapped so that only
the final value is public and the initial value is the private input. The outer
proof is the claimed initial value. This witnesses (I6) that the hypotheses of
`NonDeterministic.System.cte` are jointly satisfiable, that the wrapped
verifier accepts a concrete proof, and that the private input is not trivial:
the wrapped VM's traces start at a value the statement does not contain.

All declarations are private; this module adds no public API.
-/

namespace VanillaZkVM
namespace NonDeterministicSanity

/-- A counter that increments once. The statement fixes both endpoints. -/
private def counter : ZkVM where
  State := ℕ
  step := fun a b => b = a + 1
  T := 1
  Stmt := ℕ × ℕ
  PrivInput := Unit
  initial := fun x _ => x.1
  terminal := fun x _ => x.2
  Proof := Unit
  verify := fun x _ => x.2 = x.1 + 1

private theorem counter_cte : counter.CTE := by
  refine ⟨fun x _ => ((), fun i => if i = 0 then x.1 else x.2), ?_⟩
  intro x p hp
  refine ⟨rfl, by simp [counter], ?_⟩
  intro i hi
  have hi0 : i = 0 := by
    change i < 1 at hi
    omega
  subst hi0
  simpa [counter] using hp

/-- Only the final value is public; the initial value is the private input, and
the outer proof is the claimed initial value. -/
private def hidden : NonDeterministic.System counter where
  Stmt := ℕ
  PrivInput := ℕ
  embed := fun final start => (start, final)
  OuterProof := ℕ
  outerVerify := fun final start => final = start + 1

private theorem hidden_outer_sound : KnowledgeSound hidden.ASOuter := by
  refine ⟨⟨fun _ start => (start, ())⟩, ?_⟩
  intro x p hp
  exact hp

example : hidden.toZkVM.verify (show hidden.toZkVM.Stmt from (5 : ℕ))
    (show hidden.toZkVM.Proof from (4 : ℕ)) := by
  show (5 : ℕ) = 4 + 1
  rfl

example : hidden.toZkVM.CTE :=
  hidden.cte counter_cte hidden_outer_sound

/-- The private input carries information the statement does not: a valid
trace for public statement `final` under private input `(start, ())` starts at
`start`, and validity forces `final = start + 1`. -/
private theorem trace_starts_at_private_input (final start : ℕ) (tr : ℕ → ℕ)
    (h : hidden.toZkVM.TraceValid final (start, ()) tr) :
    tr 0 = start ∧ final = start + 1 := by
  obtain ⟨h0, h1, hstep⟩ := h
  have hs : tr 1 = tr 0 + 1 := hstep 0 Nat.one_pos
  change tr 0 = start at h0
  change tr 1 = final at h1
  omega

end NonDeterministicSanity
end VanillaZkVM
