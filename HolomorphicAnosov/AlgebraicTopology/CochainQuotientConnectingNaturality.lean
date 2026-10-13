import HolomorphicAnosov.AlgebraicTopology.CochainQuotientConnectingDefinition
import Mathlib.Algebra.Homology.HomologySequenceLemmas
open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- Connecting maps on the explicit cohomology quotients commute with morphisms
of short exact cochain sequences. Source: Hatcher, *Algebraic Topology*, p.201;
Mathlib `HomologicalComplex.HomologySequence.δ_naturality`.
Expand the quotient maps and connecting maps, cancel the intermediate canonical
homology isomorphisms, and apply naturality of the snake-lemma connecting map. -/
theorem cochain_quotient_connecting_naturality (R : Type u) [CommRing R]
    {S T : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) (n : ℕ) :
    quotientConnecting R hS n ≫ quotientMap R φ.τ₁ (n+1) =
      quotientMap R φ.τ₃ n ≫ quotientConnecting R hT n := by
  simp only [quotientConnecting, quotientMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (hS.δ n (n+1) rfl),
    HomologicalComplex.HomologySequence.δ_naturality φ hS hT n (n+1) rfl]
  simp only [Category.assoc]
end HolomorphicAnosov.SingularCochain
