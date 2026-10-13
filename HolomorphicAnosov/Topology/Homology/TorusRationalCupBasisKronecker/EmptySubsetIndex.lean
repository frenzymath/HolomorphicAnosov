import Mathlib.Data.Finset.Card

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero subset index consists solely of the empty subset, for every
number of coordinates. This is the unit index in Hatcher's product basis p.216. -/
def emptySubsetIndex (n : ℕ) :
    Unit ≃ {S : Finset (Fin n) // S.card = 0} where
  toFun _ := ⟨∅, rfl⟩
  invFun _ := ()
  left_inv := by intro u; cases u; rfl
  right_inv := by
    intro S
    apply Subtype.ext
    exact (Finset.card_eq_zero.mp S.property).symm

end HolomorphicAnosov.TorusRationalCupBasisKronecker
