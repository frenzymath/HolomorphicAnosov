import HolomorphicAnosov.Topology.EuclideanSupportOrientation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open CategoryTheory TopologicalSpace Set
namespace HolomorphicAnosov

/-- Finite inclusion of Euclidean space into its one-point compactification
induces an isomorphism on homology relative to the punctured origin.
Source: Hatcher, Algebraic Topology, Theorem 2.20, pp.119–124. The full Euclidean
open set and singleton support specialize the support excision theorem; the
homeomorphism from Euclidean space to its full subtype identifies the precise maps. -/
theorem euclideanCompactificationLocalInclusion_isIso (n : ℕ) :
    IsIso (euclideanCompactificationLocalInclusion n) := by
  let E := EuclideanSpace ℝ (Fin n)
  let P := singularSubspacePair (TopCat.of E) ({0} : Set E)ᶜ
  let Q := euclideanSupportPair n univ {0}
  let f : TopCat.of E ⟶ TopCat.of (univ : Set E) :=
    TopCat.ofHom ⟨fun x ↦ ⟨x, mem_univ x⟩, continuous_id.subtype_mk _⟩
  let g : TopCat.of (univ : Set E) ⟶ TopCat.of E :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let F : P ⟶ Q := singularSubspacePairMap f _ _ (by intro x hx; exact hx)
  let G : Q ⟶ P := singularSubspacePairMap g _ _ (by intro x hx; exact hx)
  have hFG : F ≫ G = 𝟙 P := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      rfl
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      rfl
  have hGF : G ≫ F = 𝟙 Q := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      rfl
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = 𝟙 _
      rw [← Functor.map_comp, ← TopCat.toSSet.map_id]
      rfl
  let e : P ≅ Q := ⟨F, G, hFG, hGF⟩
  have hF : IsIso (SSetPair.homologyMap F reducedSingularIntegralCoefficients n) :=
    ((SSetPair.homologyFunctor reducedSingularIntegralCoefficients n).mapIso e).isIso_hom
  let I : Q ⟶ euclideanCompactificationOriginPair n :=
    singularSubspacePairMap (euclideanSupportFiniteInclusion n univ) _ _ (by
      intro u hu hz
      exact hu (OnePoint.coe_injective hz))
  have hI : IsIso (SSetPair.homologyMap I reducedSingularIntegralCoefficients n) := by
    have h := euclideanSupportHomologyInclusion_isIso n univ {0}
      isOpen_univ isCompact_singleton (subset_univ _)
    unfold euclideanSupportHomologyInclusion euclideanSupportPairInclusion at h
    unfold euclideanSupportPair euclideanCompactificationSupportPair at h
    generalize_proofs hcop hcat hmap at h
    revert hmap h
    rw [Set.image_singleton]
    intro hmap h
    exact h
  have hcomp : SSetPair.homologyMap F reducedSingularIntegralCoefficients n ≫
      SSetPair.homologyMap I reducedSingularIntegralCoefficients n =
        euclideanCompactificationLocalInclusion n := by
    rw [← SSetPair.homologyMap_comp]
    congr 1
  rw [← hcomp]
  infer_instance

end HolomorphicAnosov

