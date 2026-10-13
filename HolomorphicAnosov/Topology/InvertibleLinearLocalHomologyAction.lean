import HolomorphicAnosov.Topology.SimplexSwapLocalHomology

/-!
# Determinant sign on Euclidean local homology

Source: Hatcher, Algebraic Topology pp.108,115–118,125,134,233,269;
Vector Bundles and K-Theory pp.23–24.
-/
noncomputable section
open CategoryTheory
namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- An invertible real linear map acts on integral local homology by the sign
of its determinant, independently of the chosen generator.

Source: Hatcher, Algebraic Topology pp.108,115–118,125,134,233,269;
Vector Bundles and K-Theory pp.23–24.
Node: `topo.invertible_real_linear_local_homology_action_g16`.

For positive determinant, the existing general-linear-group component path
joins the map to the identity through injective operators. Relative homotopy
invariance equates their actions, and functoriality makes the latter identity.
For negative determinant, the dimension is positive, since the determinant in
zero dimension is one. Swap the first two vertices of the explicit simplex
with vertices (-1,…,-1), e₁,…,eₙ. The resulting linear involution has lower
triangular matrix with diagonal (-1,1,…,1), hence determinant -1. Composing
the original map with this involution gives positive determinant; a positive
component path, multiplied again by the involution, joins the original map to
the swap. To compute its local action, use the singular simplex with vertex
list (v₀,v₁,v₀,v₂,…,vₙ). Its zeroth and second faces are respectively the
swapped and original simplex, both with positive boundary sign. Each other
face omits an original vertex and therefore avoids zero, so vanishes in the
relative chain quotient. The boundary identity makes the two local classes
negatives. Hatcher's primitive simplex generator theorem, transported by the
punctured-simplex comparison and excision, says the original simplex class
generates all local homology. Thus the swap acts by -1 on every class, and
relative homotopy invariance gives the same action for the original map.
The argument includes dimension one: the three-vertex singular simplex is
(v₀,v₁,v₀), with its middle face constant away from zero.
-/
theorem invertible_real_linear_local_homology_action (n : ℕ)
    (L : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let X := TopCat.of (EuclideanSpace ℝ (Fin n))
    let A : Set X := {x | x ≠ 0}
    let P := singularSubspacePair X A
    let H := P.homology singularIntegralCoefficients n
    let f : X ⟶ X := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
    let F := SSetPair.homologyMap
      (singularSubspacePairMap f A A
        (fun _x hx h ↦ hx (L.injective (h.trans L.map_zero.symm))))
      singularIntegralCoefficients n
    ∀ c : H, F.hom c = (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) • c := by
  let E := EuclideanSpace ℝ (Fin n)
  have hdet_ne : LinearMap.det L.toLinearMap ≠ 0 := by
    intro hdet
    have hker : LinearMap.ker L.toLinearMap ≠ ⊥ := by
      rw [← LinearMap.det_eq_zero_iff_ker_ne_bot]
      exact hdet
    exact hker (by simp)
  rcases lt_or_gt_of_ne hdet_ne with hneg | hpos
  · cases n with
    | zero =>
      have hdet : LinearMap.det L.toLinearMap = 1 := LinearMap.det_eq_one_of_subsingleton _
      linarith
    | succ m =>
      dsimp only
      rw [sign_neg hneg]
      intro c
      simpa only [SignType.coe_neg, SignType.coe_one, neg_one_zsmul] using
        negative_linear_local_homology_action m L hneg c
  · obtain ⟨D, hD, hI, h0, h1⟩ := exists_positive_linear_equiv_injective_path n L hpos
    have hmaps := linear_path_local_homology D hD hI n
    have hsign := linear_path_det_sign D hD hI
    simp only [h0, h1] at hmaps hsign
    have hp : singularSubspacePairMap
        (TopCat.ofHom (toContinuousMap (ContinuousLinearMap.id ℝ E)))
        {x | x ≠ 0} {x | x ≠ 0} (fun x hx h ↦ hx h) =
        𝟙 (singularSubspacePair (TopCat.of E) {x | x ≠ 0}) := by
      apply MorphismProperty.Arrow.Hom.ext
      · change TopCat.toSSet.map _ = 𝟙 _
        rw [← TopCat.toSSet.map_id]
        congr 1
      · change TopCat.toSSet.map _ = 𝟙 _
        rw [← TopCat.toSSet.map_id]
        congr 1
    rw [hp, SSetPair.homologyMap_id] at hmaps
    have hf : toContinuousMap L.toContinuousLinearEquiv.toContinuousLinearMap =
        toContinuousMap L.toContinuousLinearEquiv := by
      ext x
      rfl
    simp only [hf] at hmaps
    change SignType.sign (LinearMap.det L.toLinearMap) =
      SignType.sign (LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)) at hsign
    have hs : SignType.sign (LinearMap.det L.toLinearMap) = 1 := by
      simpa using hsign
    dsimp only
    rw [hmaps, hs]
    intro c
    simp only [SignType.coe_one, one_smul]
    rfl

end HolomorphicAnosov

