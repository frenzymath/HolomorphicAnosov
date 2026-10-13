import Mathlib.Data.Finset.Card

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The degree-one subset index is exactly the original coordinate index, also for the
empty coordinate set. -/
def singletonIndex (n : ℕ) : Fin n ≃ {S : Finset (Fin n) // S.card = 1} :=
  Equiv.ofBijective (fun i ↦ ⟨{i}, by simp⟩) (by
    constructor
    · intro i j h
      exact Finset.singleton_injective (congrArg Subtype.val h)
    · intro S
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp S.property
      exact ⟨i, Subtype.ext hi.symm⟩)

end HolomorphicAnosov.TorusRationalCupBasisKronecker
