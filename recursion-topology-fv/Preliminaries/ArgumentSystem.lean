import Mathlib

/-!
# Relations and argument systems

Scheme-independent definitions: relations, non-interactive arguments, and straight-line knowledge
soundness.

* `Relation` — a statement/witness relation.
* `ArgumentSystem` — a non-interactive argument
* `Extractor` + `KnowledgeSound` — straight-line knowledge soundness.

Security notions here are idealized. See `IDEALIZATION.md`.
-/

namespace VanillaZkVM

/-! ## Structure of definitions:

      Relation              -- statements, witnesses, membership
         ▲  R
      ArgumentSystem R      -- proof type + verifier for `R`
         ▲  AS
      Extractor R AS        -- From R.Stmt and AS.Proof, we get R.Wit
         ▲  ∃ E
      KnowledgeSound AS     -- every accepting proof for AS extracts
-/

/-- A relation `R ⊆ Stmt × Wit`. -/
structure Relation where
  /-- The statement type. -/
  Stmt : Type
  /-- The witness type. -/
  Wit : Type
  /-- `rel x w` means `(x; w) ∈ R`. -/
  rel : Stmt → Wit → Prop

/-- A non-interactive argument system for a relation `R`.

Paper: `def:zkvm` writes `Π = (Prove, Verify)`. Lean omits `Prove`, because soundness does not
use it. -/
structure ArgumentSystem (R : Relation) where
  /-- The proof type. -/
  Proof : Type
  /-- `verify x p` means `Verify(x, p) = 1`. A `Prop` here, representing a Boolean algorithm. -/
  verify : R.Stmt → Proof → Prop

/-- A straight-line extractor for `AS`: no rewinding, no access to the adversary's code. -/
structure Extractor (R : Relation) (AS : ArgumentSystem R) where
  /-- Map a statement and a proof to a candidate witness. -/
  extract : R.Stmt → AS.Proof → R.Wit

/-- `AS` is **knowledge-sound** (perfect straight-line extraction) if there is a
single universal extractor `E` such that whenever a proof verifies for a
statement, `E` recovers a valid witness.

Paper: `def:extractable` / `eq:extractable`. Lean uses the perfect,
probability-free version. -/
def KnowledgeSound {R : Relation} (AS : ArgumentSystem R) : Prop :=
  ∃ E : Extractor R AS, ∀ (x : R.Stmt) (p : AS.Proof),
    AS.verify x p → R.rel x (E.extract x p)

end VanillaZkVM
