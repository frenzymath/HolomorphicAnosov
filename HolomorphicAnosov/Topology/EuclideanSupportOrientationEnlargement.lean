import HolomorphicAnosov.Topology.EuclideanSupportOrientation

/-!
# Naturality when a compact support is enlarged

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts* (1965), Proposition 1.3, p.1. The identity map on the domain, regarded
as a map from the larger-support pair to the smaller-support pair, preserves
the canonical supported orientation. This is the support part of Dold's formula
used in his homotopy-invariance proof, Proposition 1.7, p.2.
-/

noncomputable section
namespace HolomorphicAnosov
open CategoryTheory Set

/-- Dold Proposition 1.3, p.1: if `K ⊆ L ⊆ U`, the relative map induced by the
identity on `U` carries `o(U,L)` to `o(U,K)`.

Proof: let `eL,eK` be finite compactification inclusion and let `r,s` be support
restriction in the domain and compactification. The literal inclusion square
gives `r ≫ eK = eL ≫ s`. Naturality of the relative quotient gives `qL ≫ s = qK`.
Both inclusions induce isomorphisms by excision. Thus
`eK(r(eL⁻¹(qL μ))) = s(qL μ) = qK μ`, which equals `eK(o(U,K))`.
Cancel `eK`. This includes zero dimension and empty supports without change.
-/
theorem euclideanSupportOrientation_enlargement
    (n : ℕ) (U K L : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hK : IsCompact K) (hL : IsCompact L)
    (hKL : K ⊆ L) (hLU : L ⊆ U) :
    SSetPair.homologyMap
        (singularSubspacePairMap (𝟙 (TopCat.of U))
          {u : U | u.val ∉ L} {u : U | u.val ∉ K}
          (by intro u hu hk; exact hu (hKL hk)))
        reducedSingularIntegralCoefficients n
        (euclideanSupportOrientation n U L hU hL hLU) =
      euclideanSupportOrientation n U K hU hK (hKL.trans hLU) := by
  let r : euclideanSupportPair n U L ⟶ euclideanSupportPair n U K :=
    singularSubspacePairMap (𝟙 (TopCat.of U))
      {u : U | u.val ∉ L} {u : U | u.val ∉ K}
      (by intro u hu hk; exact hu (hKL hk))
  let s : euclideanCompactificationSupportPair n L ⟶
      euclideanCompactificationSupportPair n K :=
    singularSubspacePairMap (𝟙 (TopCat.of (EuclideanCompactification n)))
      (OnePoint.some '' L)ᶜ (OnePoint.some '' K)ᶜ
      (by intro x hx hxK; exact hx (image_mono hKL hxK))
  have hsquare : r ≫ euclideanSupportPairInclusion n U K =
      euclideanSupportPairInclusion n U L ≫ s := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
        TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
  let eK := euclideanSupportHomologyInclusion n U K
  let eL := euclideanSupportHomologyInclusion n U L
  let R := SSetPair.homologyMap r reducedSingularIntegralCoefficients n
  let S := SSetPair.homologyMap s reducedSingularIntegralCoefficients n
  have heq : R ≫ eK = eL ≫ S := by
    change SSetPair.homologyMap r _ _ ≫ SSetPair.homologyMap _ _ _ =
      SSetPair.homologyMap _ _ _ ≫ SSetPair.homologyMap s _ _
    rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp, hsquare]
  have hprojection : euclideanSupportCompactificationProjection n L ≫ S =
      euclideanSupportCompactificationProjection n K := by
    have h := (((SSetPair.chainComplexFunctorπ (ModuleCat ℤ)).app
      reducedSingularIntegralCoefficients).naturality s)
    change SSet.chainComplexMap s.hom.right reducedSingularIntegralCoefficients ≫
        (euclideanCompactificationSupportPair n K).chainComplexπ
          reducedSingularIntegralCoefficients =
      (euclideanCompactificationSupportPair n L).chainComplexπ
          reducedSingularIntegralCoefficients ≫
        SSetPair.chainComplexMap s reducedSingularIntegralCoefficients at h
    have hright : s.hom.right = 𝟙 _ := by
      change TopCat.toSSet.map (𝟙 _) = _
      exact TopCat.toSSet.map_id _
    have hcid : SSet.chainComplexMap s.hom.right reducedSingularIntegralCoefficients =
        𝟙 _ := by
      rw [hright]
      exact ((SSet.chainComplexFunctor (ModuleCat ℤ)).obj
        reducedSingularIntegralCoefficients).map_id _
    change HomologicalComplex.homologyMap _ n ≫
        HomologicalComplex.homologyMap _ n = HomologicalComplex.homologyMap _ n
    rw [← HomologicalComplex.homologyMap_comp]
    have hc : (euclideanCompactificationSupportPair n L).chainComplexπ
        reducedSingularIntegralCoefficients ≫
        SSetPair.chainComplexMap s reducedSingularIntegralCoefficients =
        (euclideanCompactificationSupportPair n K).chainComplexπ
          reducedSingularIntegralCoefficients := by
      rw [hcid] at h
      change 𝟙 ((euclideanCompactificationSupportPair n K).right.chainComplex
          reducedSingularIntegralCoefficients) ≫ _ = _ at h
      rw [Category.id_comp] at h
      exact h.symm
    rw [hc]
  let : IsIso eK := euclideanSupportHomologyInclusion_isIso n U K hU hK (hKL.trans hLU)
  let : IsIso eL := euclideanSupportHomologyInclusion_isIso n U L hU hL hLU
  have hinv : inv eL ≫ R = S ≫ inv eK := by
    apply (cancel_mono eK).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [heq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  change R.hom ((inv eL).hom
      ((euclideanSupportCompactificationProjection n L).hom
        (euclideanPositiveCompactificationClass n))) =
    (inv eK).hom ((euclideanSupportCompactificationProjection n K).hom
      (euclideanPositiveCompactificationClass n))
  change (inv eL ≫ R).hom _ = _
  rw [hinv]
  change (inv eK).hom ((euclideanSupportCompactificationProjection n L ≫ S).hom _) = _
  rw [hprojection]

end HolomorphicAnosov
