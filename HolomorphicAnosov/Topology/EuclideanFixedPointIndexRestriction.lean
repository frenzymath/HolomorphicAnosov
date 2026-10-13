import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.EuclideanSupportOrientationNaturality
import HolomorphicAnosov.Topology.EuclideanRestrictedMap
import HolomorphicAnosov.Topology.EuclideanSupportInclusion
import HolomorphicAnosov.Topology.EuclideanRestrictedAmbientFixedSet

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- Source: Dold (1965), §§1.1–1.3, p.1.
Dold restriction/empty-support calculation. The pair square commutes and supported orientations are natural under inclusion; the empty class maps to zero. -/
theorem restriction_index {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U, EuclideanSpace ℝ (Fin n))) (hK : IsCompact (euclideanFixedSet f))
    (V : Opens (EuclideanSpace ℝ (Fin n))) (hVU : V ≤ U)
    (hV : ∀ x ∈ euclideanFixedSet f, x.1 ∈ V)
    (hK' : IsCompact (euclideanFixedSet (restrictedMap f V hVU))) :
    euclideanFixedPointIndex (restrictedMap f V hVU) hK' = euclideanFixedPointIndex f hK := by
  let g := restrictedMap f V hVU
  have hA : euclideanAmbientFixedSet g = euclideanAmbientFixedSet f :=
    restricted_ambient_fixedSet_eq f V hVU hV
  let j := supportInclusion n (V : Set _) (U : Set _)
    (euclideanAmbientFixedSet g) (euclideanAmbientFixedSet f) hVU hA
  have hj : j ≫ euclideanDisplacementPairMap f = euclideanDisplacementPairMap g := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      rfl
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      rfl
  have hcomp : SSetPair.homologyMap j reducedSingularIntegralCoefficients n ≫
      euclideanDisplacementHomologyMap f = euclideanDisplacementHomologyMap g := by
    unfold euclideanDisplacementHomologyMap
    rw [← SSetPair.homologyMap_comp, hj]
  have hc' : IsCompact (euclideanAmbientFixedSet g) := hK'.image continuous_subtype_val
  have hc : IsCompact (euclideanAmbientFixedSet f) := hK.image continuous_subtype_val
  have hs' : euclideanAmbientFixedSet g ⊆ (V : Set _) := by
    rintro x ⟨u, hu, rfl⟩
    exact u.property
  have hs : euclideanAmbientFixedSet f ⊆ (U : Set _) := by
    rintro x ⟨u, hu, rfl⟩
    exact u.property
  have ho := (show ∀ (V U K' K : Set (EuclideanSpace ℝ (Fin n)))
      (hVU : V ⊆ U) (hKK : K' = K)
      (hV : IsOpen V) (hU : IsOpen U) (hc' : IsCompact K') (hc : IsCompact K)
      (hs' : K' ⊆ V) (hs : K ⊆ U),
      (SSetPair.homologyMap (supportInclusion n V U K' K hVU hKK)
        reducedSingularIntegralCoefficients n).hom
        (euclideanSupportOrientation n V K' hV hc' hs') =
        euclideanSupportOrientation n U K hU hc hs from by
      intro V U K' K hVU hKK hV hU hc' hc hs' hs
      subst K'
      exact euclideanSupportOrientation_subset_naturality n V U K hV hU hc hs' hVU)
    (V : Set _) (U : Set _)
    (euclideanAmbientFixedSet g) (euclideanAmbientFixedSet f) hVU hA
    V.isOpen U.isOpen hc' hc hs' hs
  let o := euclideanSupportOrientation n (V : Set _) (euclideanAmbientFixedSet g)
    V.isOpen hc' hs'
  have he := congrArg (fun q => q.hom o) hcomp
  have ho' := congrArg (fun x => (euclideanDisplacementHomologyMap f).hom x) ho
  have hval := he.symm.trans ho'
  exact congrArg (euclideanPositiveLocalCoordinate n) hval

end HolomorphicAnosov
