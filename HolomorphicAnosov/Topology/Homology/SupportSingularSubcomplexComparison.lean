import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietorisData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Topology
universe u

/-- The support pair identifies with its complement singular subcomplex, fixing
ambient simplices. This is the pair part of the singular subspace adapter. -/
theorem supportSingularPair_iso_exists (X : TopCat.{u}) (K : Set X) :
    ∃ e : supportSingularPair X K ≅ (singularSubspace X Kᶜ).pair,
      e.hom.hom.right = 𝟙 (TopCat.toSSet.obj X) := by
  obtain ⟨e, _, _, _, _, _, ep, hep, _⟩ := singular_subspace_subcomplex_adapter.{u,u,u}
  exact ⟨ep X Kᶜ, (hep X Kᶜ).2⟩

/-- Canonical choice of the complement-subcomplex pair comparison. -/
def supportSingularPairIso (X : TopCat.{u}) (K : Set X) :
    supportSingularPair X K ≅ (singularSubspace X Kᶜ).pair :=
  (supportSingularPair_iso_exists X K).choose

@[simp] theorem supportSingularPairIso_right (X : TopCat.{u}) (K : Set X) :
    (supportSingularPairIso X K).hom.hom.right = 𝟙 (TopCat.toSSet.obj X) :=
  (supportSingularPair_iso_exists X K).choose_spec

/-- Relative chain comparison induced by the actual pair comparison. -/
def supportSingularChainIso (X : TopCat.{u}) (K : Set X) (R : ModuleCat.{u} ℤ) :
    supportSingularChainComplex X K R ≅ (singularSubspace X Kᶜ).pair.chainComplex R :=
  ((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R).mapIso
    (supportSingularPairIso X K)

@[reassoc (attr := simp)]
theorem supportSingularChainIso_projection_naturality (X : TopCat.{u}) (K : Set X)
    (R : ModuleCat.{u} ℤ) :
    (supportSingularPair X K).chainComplexπ R ≫ (supportSingularChainIso X K R).hom =
      SSet.chainComplexMap (supportSingularPairIso X K).hom.hom.right R ≫
        (singularSubspace X Kᶜ).pair.chainComplexπ R := by
  have h := (((SSetPair.chainComplexFunctorπ (ModuleCat.{u} ℤ)).app R).naturality
    (supportSingularPairIso X K).hom).symm
  change (supportSingularPair X K).chainComplexπ R ≫
      (supportSingularChainIso X K R).hom =
    SSet.chainComplexMap (supportSingularPairIso X K).hom.hom.right R ≫ _ at h
  exact h

@[reassoc (attr := simp)]
theorem supportSingularChainIso_projection (X : TopCat.{u}) (K : Set X)
    (R : ModuleCat.{u} ℤ) :
    (supportSingularPair X K).chainComplexπ R ≫ (supportSingularChainIso X K R).hom =
        (singularSubspace X Kᶜ).pair.chainComplexπ R := by
  rw [supportSingularChainIso_projection_naturality, supportSingularPairIso_right]
  change SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj X)) R ≫
    (singularSubspace X Kᶜ).pair.chainComplexπ R = _
  exact (congrArg (fun m ↦ m ≫ (singularSubspace X Kᶜ).pair.chainComplexπ R)
    (((SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj R).map_id (TopCat.toSSet.obj X))).trans
      (Category.id_comp _)

end HolomorphicAnosov.Topology
