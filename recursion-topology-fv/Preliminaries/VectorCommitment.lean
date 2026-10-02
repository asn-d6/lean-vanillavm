import Mathlib

/-!
# Vector commitments and their binding notions

These definitions are used as memory-commitments by the layers above.

Binding notions are idealized. See `IDEALIZATION.md`.
-/

namespace VanillaZkVM

/-- A vector commitment scheme `Com = (Commit, Open, Verify)`. A vector is a
total map `Index → Value`. `verify C i v p` checks that position `i` of the
committed vector holds value `v` under commitment `C`.

Paper: `def:binding` (commit/open/verify interface). -/
structure VectorCommitment where
  Value : Type
  Index : Type
  Com : Type
  OpenProof : Type
  commit : (Index → Value) → Com
  openProof : (Index → Value) → Index → OpenProof
  verify : Com → Index → Value → OpenProof → Prop

namespace VectorCommitment

/-- **Commitment completeness**: an honest opening always verifies.
This makes explicit the correctness property used by the binding reductions,
as requested by the instruction preceding `def:binding` in ch05. -/
def Complete (VC : VectorCommitment) : Prop :=
  ∀ (m : VC.Index → VC.Value) (i : VC.Index),
    VC.verify (VC.commit m) i (m i) (VC.openProof m i)

/-- **Position-binding**: no commitment admits two accepted openings of
different values at the same position.

Paper: `def:binding`. -/
def PositionBinding (VC : VectorCommitment) : Prop :=
  ∀ (C : VC.Com) (i : VC.Index) (v v' : VC.Value) (pi pi' : VC.OpenProof),
    VC.verify C i v pi → VC.verify C i v' pi' → v = v'

/-- **Update-binding** (`def:binding`, ch05): suppose `m'` is obtained
from `m` by changing only `addr`, whose new value is `x`. If the same opening
`pi` verifies the old value against `VC.commit m` and the new value against a
candidate commitment `C'`, then `C'` must equal `VC.commit m'`.

In plain terms, merely passing verification at the changed address is not
enough. The commitment after the write must be the value computed by
`VC.commit` from exactly the updated full memory. -/
def UpdateBinding (VC : VectorCommitment) : Prop :=
  ∀ (m m' : VC.Index → VC.Value) (addr : VC.Index) (x : VC.Value)
    (C' : VC.Com) (pi : VC.OpenProof),
    m' addr = x → (∀ j, j ≠ addr → m' j = m j) →
    VC.verify (VC.commit m) addr (m addr) pi →
    VC.verify C' addr x pi →
    C' = VC.commit m'

end VectorCommitment

end VanillaZkVM
