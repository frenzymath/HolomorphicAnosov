import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Topology.EuclideanSupportOrientationProduct
import HolomorphicAnosov.Topology.InvertibleLinearLocalHomologyAction
import HolomorphicAnosov.Topology.DerivativeStraightLineAvoidance

open Filter
open scoped _root_.Topology

namespace HolomorphicAnosov.FranksLocalIndex

/-- A differentiable map with invertible derivative at its zero is homotopic to
that derivative in a ball, through maps having that same unique zero. Source:
Franks (1969), Lemma 1.2, pp.118–119, local linearization argument. The derivative
remainder is at most `‖x‖/(2K)`, where `K` bounds the inverse derivative. A zero
of any interpolant would imply `‖x‖ ≤ ‖x‖/2`, hence `x=0`. -/
theorem local_linearization_zero_set {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E → E) (L : E ≃L[ℝ] E) (h0 : h 0 = 0)
    (hd : HasFDerivAt h L.toContinuousLinearMap 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : E, ‖x‖ < r → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      (L x + t • (h x - L x) = 0 ↔ x = 0) := by
  obtain ⟨r, hr, hne⟩ :=
    HolomorphicAnosov.Topology.exists_radius_derivative_straightLine_ne_zero L hd
  refine ⟨r, hr, fun x hx t ht ↦ ⟨fun hz ↦ ?_, fun hx0 ↦ ?_⟩⟩
  · by_contra hx0
    exact hne x hx hx0 ⟨t, ht⟩ (by simpa only [zero_add, h0, sub_zero] using hz)
  · simp [hx0, h0]

end HolomorphicAnosov.FranksLocalIndex


open CategoryTheory TopologicalSpace

namespace HolomorphicAnosov.FranksLocalIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Dold's actual Euclidean fixed-point index for a map with invertible linear
displacement is the determinant sign. Factor its displacement pair map through
localization at zero and the actual linear punctured-pair map. The supported
orientation localizes to the positive generator; the linear homology action
multiplies this generator by the determinant sign. -/
theorem index_of_linear_displacement {n : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin n))) (hU : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (f : C(U, EuclideanSpace ℝ (Fin n))) (hK : IsCompact (euclideanFixedSet f))
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : ∀ x : U, x.val - f x = L x.val) :
    euclideanFixedPointIndex f hK = (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := by
  let x : U := ⟨0, hU⟩
  have hx : x ∈ euclideanFixedSet f := by
    have h := hL x
    change 0 - f x = L 0 at h
    change f x = 0
    simpa using h
  let K := euclideanAmbientFixedSet f
  have hxK : x.val ∈ K := ⟨x, hx, rfl⟩
  let j := EuclideanIndexProduct.localizationPairMap U K x hxK
  let a := singularSubspacePairMap
    (TopCat.ofHom (toContinuousMap L)) ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ
    ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ
    (by intro y hy hz; exact hy (L.injective (hz.trans L.map_zero.symm)))
  have hfactor : j ≫ a = euclideanDisplacementPairMap f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      congr 1
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro y
      apply Subtype.ext
      change L (y.val.val - 0) = y.val.val - f y.val
      simpa only [sub_zero] using (hL y.val).symm
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
      rw [← Functor.map_comp]
      congr 1
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro y
      change L (y.val - 0) = y.val - f y
      simpa only [sub_zero] using (hL y).symm
  have ha := invertible_real_linear_local_homology_action n L.toLinearEquiv
  dsimp only at ha
  unfold euclideanFixedPointIndex euclideanDisplacementHomologyMap
  rw [← hfactor, SSetPair.homologyMap_comp]
  change euclideanPositiveLocalCoordinate n
    ((SSetPair.homologyMap a reducedSingularIntegralCoefficients n).hom
      ((SSetPair.homologyMap j reducedSingularIntegralCoefficients n).hom _)) = _
  have ho := EuclideanIndexProduct.localization_orientation U K
    (hK.image continuous_subtype_val)
    (show K ⊆ (U : Set _) from by rintro y ⟨z, _, rfl⟩; exact z.property) x hxK
  change (SSetPair.homologyMap j reducedSingularIntegralCoefficients n).hom _ =
    euclideanPositiveLocalClass n at ho
  rw [ho]
  have haction : (SSetPair.homologyMap a reducedSingularIntegralCoefficients n).hom
      (euclideanPositiveLocalClass n) =
      (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) • euclideanPositiveLocalClass n := by
    exact ha _
  rw [haction, map_zsmul, (euclideanPositiveLocalCoordinate_characterization n).1]
  simp

/-- The local index at a nondegenerate zero of the displacement is its derivative's
sign. The common-zero interpolation is admissible on a sufficiently small ball.
Dold homotopy invariance and the linear displacement calculation give the value. -/
theorem local_index_of_invertible_displacement {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsOpen S) (h0S : 0 ∈ S)
    (hf : ContinuousOn f S) (hf0 : f 0 = 0)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hd : HasFDerivAt (fun x ↦ x - f x) L.toContinuousLinearMap 0) :
    ∃ r : ℝ, ∃ _hr : 0 < r, Metric.ball 0 r ⊆ S ∧
      let U : Opens (EuclideanSpace ℝ (Fin n)) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
      ∃ F : C(U, EuclideanSpace ℝ (Fin n)), (∀ x, F x = f x.val) ∧
        ∃ hK : IsCompact (euclideanFixedSet F),
          euclideanFixedPointIndex F hK =
            (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := by
  obtain ⟨r, hr, hz⟩ := local_linearization_zero_set (fun x ↦ x - f x) L
    (by simp [hf0]) hd
  obtain ⟨s, hs, hsS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds h0S)
  let R := min r s
  have hR : 0 < R := lt_min hr hs
  have hRS : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆ S :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans hsS
  let U : Opens (EuclideanSpace ℝ (Fin n)) := ⟨Metric.ball 0 R, Metric.isOpen_ball⟩
  let F : C(U, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x ↦ f x.val, continuousOn_iff_continuous_domRestrict.mp (hf.mono hRS)⟩
  let x₀ : U := ⟨0, Metric.mem_ball_self hR⟩
  let H : C(U × unitInterval, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun z ↦ z.1.val - (L z.1.val + (z.2 : ℝ) •
        ((z.1.val - F z.1) - L z.1.val)), by fun_prop⟩
  have hz' (x : U) (t : unitInterval) : H (x,t) = x.val ↔ x = x₀ := by
    change x.val - (L x.val + (t:ℝ) • ((x.val - f x.val) - L x.val)) = x.val ↔ x = x₀
    rw [sub_eq_self]
    have hxR : ‖x.val‖ < R := by
      simpa only [dist_zero_right] using (show dist x.val 0 < R from x.property)
    rw [hz x.val (lt_of_lt_of_le hxR (min_le_left r s)) t t.property]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  have hcompact : IsCompact {z : U × unitInterval | H z = z.1.val} := by
    have heq : {z : U × unitInterval | H z = z.1.val} =
        Set.range (fun t : unitInterval ↦ (x₀,t)) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_range]
      constructor
      · intro h
        exact ⟨z.2, Prod.ext ((hz' z.1 z.2).mp h).symm rfl⟩
      · rintro ⟨t, rfl⟩
        exact (hz' x₀ t).mpr rfl
    rw [heq]
    exact isCompact_range (continuous_const.prodMk continuous_id)
  have hb := euclidean_fixed_point_index_basic_laws
  dsimp only at hb
  obtain ⟨hK0, hK1, heq⟩ := hb.2.1 n U H hcompact
  let F0 : C(U, EuclideanSpace ℝ (Fin n)) :=
    H.comp ⟨fun x ↦ (x,0), continuous_id.prodMk continuous_const⟩
  let F1 : C(U, EuclideanSpace ℝ (Fin n)) :=
    H.comp ⟨fun x ↦ (x,1), continuous_id.prodMk continuous_const⟩
  have hF1 : F1 = F := by
    apply ContinuousMap.ext
    intro x
    change x.val - (L x.val + (1:ℝ) • ((x.val - F x) - L x.val)) = F x
    simp only [one_smul]
    abel
  have hind : euclideanFixedPointIndex F0 hK0 =
      (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) :=
    index_of_linear_displacement U x₀.property F0 hK0 L (by
      intro x
      change x.val - (x.val - (L x.val + (0:ℝ) • _)) = L x.val
      simp)
  refine ⟨R, hR, hRS, F, fun _ ↦ rfl, ?_⟩
  have hK : IsCompact (euclideanFixedSet F) := hF1 ▸ hK1
  refine ⟨hK, ?_⟩
  have heq' : euclideanFixedPointIndex F1 hK1 =
      (SignType.sign (LinearMap.det L.toLinearMap) : ℤ) := heq.symm.trans hind
  have hindexeq : ∀ (g : C(U, EuclideanSpace ℝ (Fin n)))
      (hg : IsCompact (euclideanFixedSet g)), g = F →
      euclideanFixedPointIndex g hg = euclideanFixedPointIndex F hK := by
    intro g hg h
    subst g
    rfl
  exact (hindexeq F1 hK1 hF1).symm.trans heq'

end
end HolomorphicAnosov.FranksLocalIndex
