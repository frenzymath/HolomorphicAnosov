import HolomorphicAnosov.Topology.EuclideanConstantFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanCompactificationLocalInclusionIso

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
open CategoryTheory TopologicalSpace Set
namespace HolomorphicAnosov

private theorem pair_projection_image_congr
    (X Y : TopCat) (f : X ⟶ Y) (C : Set X) (A B : Set Y) (hAB : A = B)
    (hA : MapsTo f C A) (hB : MapsTo f C B) (n : ℕ)
    (x : ((singularSubspacePair X C).homology reducedSingularIntegralCoefficients n : ModuleCat ℤ))
    (μ : ((TopCat.toSSet.obj Y).homology reducedSingularIntegralCoefficients n : ModuleCat ℤ))
    (h : (SSetPair.homologyMap (singularSubspacePairMap f C A hA)
      reducedSingularIntegralCoefficients n).hom x =
      ((singularSubspacePair Y A).homologyπ reducedSingularIntegralCoefficients n).hom μ) :
    (SSetPair.homologyMap (singularSubspacePairMap f C B hB)
      reducedSingularIntegralCoefficients n).hom x =
      ((singularSubspacePair Y B).homologyπ reducedSingularIntegralCoefficients n).hom μ := by
  subst B
  exact h

/-- The zero constant has displacement equal to the domain inclusion. Its supported
orientation maps to the positive local class at the origin, in every dimension.
Source: Dold (1965), §1.1 and §1.4, pp.1–2. Compose with finite inclusion into the
one-point compactification: the support orientation definition cancels the excision
inverse, and compactification normalization identifies its image with the positive
local class. Finite inclusion is an excision isomorphism, so equality reflects back. -/
theorem euclidean_zero_displacement_positive_class
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U) :
    let f : C(U, EuclideanSpace ℝ (Fin n)) := ContinuousMap.const U 0
    let K : Set (EuclideanSpace ℝ (Fin n)) := euclideanAmbientFixedSet f
    let hK : IsCompact K := (constant_fixedSet_compact 0 h0).image continuous_subtype_val
    let hKU : K ⊆ (U : Set (EuclideanSpace ℝ (Fin n))) := by
      rintro x ⟨u, _hu, rfl⟩
      exact u.property
    (euclideanDisplacementHomologyMap f).hom
      (euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) K U.isOpen hK hKU) =
        euclideanPositiveLocalClass n := by
  dsimp only
  let f : C(U, EuclideanSpace ℝ (Fin n)) := ContinuousMap.const U 0
  have hK : euclideanAmbientFixedSet f = {0} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu.symm
    · intro hx
      subst x
      exact ⟨⟨0, h0⟩, rfl, rfl⟩
  have hJ := euclideanCompactificationLocalInclusion_isIso n
  apply (ModuleCat.mono_iff_injective (euclideanCompactificationLocalInclusion n)).mp
    (inferInstance : Mono (euclideanCompactificationLocalInclusion n))
  rw [← euclidean_positive_compactification_class.1 n]
  unfold euclideanDisplacementHomologyMap euclideanDisplacementPairMap
  generalize_proofs p1 p2 p3 p4 p5 p6
  unfold euclideanSupportPair
  revert p3 p5 p6
  rw [show euclideanAmbientFixedSet (ContinuousMap.const U 0) = {0} from hK]
  intro hmap hcompact hcontained
  have hnorm : (euclideanSupportHomologyInclusion n (U : Set (EuclideanSpace ℝ (Fin n))) {0}).hom
      (euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) {0} p4 hcompact hcontained) =
        (euclideanSupportCompactificationProjection n {0}).hom
          (euclideanPositiveCompactificationClass n) := by
    have := euclideanSupportHomologyInclusion_isIso n (U : Set (EuclideanSpace ℝ (Fin n))) {0}
      p4 hcompact hcontained
    change (inv (euclideanSupportHomologyInclusion n (U : Set (EuclideanSpace ℝ (Fin n))) {0}) ≫
      euclideanSupportHomologyInclusion n (U : Set (EuclideanSpace ℝ (Fin n))) {0}).hom _ = _
    simp
  dsimp only [euclideanSupportHomologyInclusion, euclideanSupportPairInclusion,
    euclideanSupportCompactificationProjection, euclideanCompactificationSupportPair,
    euclideanSupportPair] at hnorm
  have hfinite : MapsTo (euclideanSupportFiniteInclusion n (U : Set (EuclideanSpace ℝ (Fin n))))
      {u : U | (u : EuclideanSpace ℝ (Fin n)) ∉ ({0} : Set (EuclideanSpace ℝ (Fin n)))}
      ({OnePoint.some (0 : EuclideanSpace ℝ (Fin n))} : Set _)ᶜ := by
    intro u hu hz
    exact hu (OnePoint.coe_injective hz)
  have hn := pair_projection_image_congr (TopCat.of U)
    (TopCat.of (EuclideanCompactification n)) (euclideanSupportFiniteInclusion n (U : Set (EuclideanSpace ℝ (Fin n))))
    _ _ _ (congrArg Set.compl Set.image_singleton) _ hfinite n _ _ hnorm
  let D := singularSubspacePairMap (TopCat.ofHom (euclideanDisplacement
    (ContinuousMap.const U 0))) {u : U | (u : EuclideanSpace ℝ (Fin n)) ∉ ({0} : Set (EuclideanSpace ℝ (Fin n)))}
    ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ hmap
  have hcomp : SSetPair.homologyMap D reducedSingularIntegralCoefficients n ≫
      euclideanCompactificationLocalInclusion n =
        SSetPair.homologyMap (singularSubspacePairMap
          (euclideanSupportFiniteInclusion n (U : Set (EuclideanSpace ℝ (Fin n)))) _ _ hfinite)
          reducedSingularIntegralCoefficients n := by
    unfold euclideanCompactificationLocalInclusion
    rw [← SSetPair.homologyMap_comp]
    congr 1
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      simp [ singularSubspaceMap, euclideanDisplacement,
        euclideanCompactificationFiniteInclusion, euclideanSupportFiniteInclusion]
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      apply congrArg (fun k ↦ TopCat.toSSet.map k)
      ext x
      simp [ euclideanDisplacement,
        euclideanCompactificationFiniteInclusion, euclideanSupportFiniteInclusion]
  change (SSetPair.homologyMap D reducedSingularIntegralCoefficients n ≫
    euclideanCompactificationLocalInclusion n).hom _ = _
  rw [hcomp]
  exact hn

end HolomorphicAnosov
