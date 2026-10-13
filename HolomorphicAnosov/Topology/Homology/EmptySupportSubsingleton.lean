import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietorisData
noncomputable section
namespace HolomorphicAnosov
open CategoryTheory CategoryTheory.Limits HolomorphicAnosov.Topology _root_.Topology
universe u
/-- Empty support has zero relative singular homology. -/
theorem support_empty_subsingleton_public (X : TopCat.{u}) (R : ModuleCat.{u} ℤ) (q : ℕ) :
    Subsingleton (supportSingularHomology X ∅ R q : Type u) := by
  let i : TopCat.of ↥((∅ : Set X)ᶜ) ⟶ X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsIso i := TopCat.isIso_of_bijective_of_isOpenMap i
    ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, by simp⟩, rfl⟩⟩
    (by
      change IsOpenMap (Subtype.val : ↥((∅ : Set X)ᶜ) → X)
      exact (by simp : IsOpen ((∅ : Set X)ᶜ)).isOpenMap_subtype_val)
  have hi' : IsIso (TopCat.toSSet.map i) := inferInstance
  have : IsIso (supportSingularPair X ∅).hom := hi'
  have : IsIso (SSet.chainComplexMap (supportSingularPair X ∅).hom R) := inferInstance
  have hz : IsZero (((supportSingularPair X ∅).chainComplex R).X q) := by
    exact CokernelCofork.IsColimit.isZero_of_epi
      ((supportSingularPair X ∅).isColimitCokernelCoforkChainComplexX R q)
  exact ModuleCat.subsingleton_of_isZero
    (ShortComplex.isZero_homology_of_isZero_X₂ _ hz)
end HolomorphicAnosov
