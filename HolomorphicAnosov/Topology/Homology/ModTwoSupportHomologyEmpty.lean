import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology

/-!
# Empty-support mod-two relative homology

The inclusion of the complement of an empty support is an isomorphism, so the
relative singular homology with empty support vanishes in every degree.
-/

noncomputable section

namespace HolomorphicAnosov.Topology.Homology

universe u

open CategoryTheory CategoryTheory.Limits

/-- Relative mod-two singular support homology with empty support is zero in every degree.

The pair is the inclusion of the whole space into itself. Its chain map is an isomorphism,
so the cokernel chain complex is zero and its homology is subsingleton. -/
theorem modTwoSupportHomology_empty_subsingleton
    (M : Type u) [TopologicalSpace M] (q : ℕ) :
    Subsingleton (modTwoSupportHomology M ∅ q) := by
  let i : TopCat.of ↥((∅ : Set M)ᶜ) ⟶ TopCat.of M :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsIso i := TopCat.isIso_of_bijective_of_isOpenMap i
    ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, by simp⟩, rfl⟩⟩
    (by
      change IsOpenMap (Subtype.val : ↥((∅ : Set M)ᶜ) → M)
      exact (by simp : IsOpen ((∅ : Set M)ᶜ)).isOpenMap_subtype_val)
  let P := singularSubspacePair M ((∅ : Set M)ᶜ)
  let R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  have : IsIso P.hom := inferInstanceAs (IsIso (TopCat.toSSet.map i))
  have : IsIso (SSet.chainComplexMap P.hom R) := inferInstance
  have hz : IsZero ((P.chainComplex R).X q) := by
    exact CokernelCofork.IsColimit.isZero_of_epi
      (P.isColimitCokernelCoforkChainComplexX R q)
  exact ModuleCat.subsingleton_of_isZero
    (ShortComplex.isZero_homology_of_isZero_X₂ _ hz)

end HolomorphicAnosov.Topology.Homology

