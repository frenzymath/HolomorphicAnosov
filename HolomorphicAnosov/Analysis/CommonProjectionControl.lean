import Mathlib.Analysis.Calculus.MeanValue

/-!
# Common local bounds for parameter-dependent projections

Fisher–Hasselblatt, *Hyperbolic flows* (2018 author text), Proposition 12.1.3
and Remark 12.1.4, pp.578–579, provide the uniform-contraction perturbation
context. The local neighborhood construction below specializes continuity
at the marked parameter and origin. Its difference bound is the precise
convex mean-value inequality from Mathlib's `MeanValue` module.
-/

namespace HolomorphicAnosov.Analysis

open Set Topology _root_.Topology

set_option backward.isDefEq.respectTransparency false in
/-- Joint continuity of the spatial derivative gives the common closed-ball
estimates for a normalized family of plaque projections.

Source: Fisher–Hasselblatt, *Hyperbolic flows* (2018), Proposition 12.1.3 and
Remark 12.1.4, pp.578–579, the uniform contraction construction under C¹
perturbations; pinned Mathlib's convex mean-value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` supplies its difference estimate.

Proof: continuity of the derivative at the marked parameter and zero, where
it is the identity, gives a product neighborhood with derivative error less
than one half. Choose a positive closed-ball radius strictly inside both its
spatial factor and the given differentiability domain. Continuity of the
center value, which is zero at the marked parameter, allows the parameter
neighborhood to be shrunk until every center displacement is less than r/8.
Apply the convex mean-value inequality relative to the identity on that same
closed ball. The parameter carrier, family and spatial coordinates are never
changed, and no derivative in the parameter is assumed. -/
theorem common_projection_control
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : P → E → E) (p₀ : P) (R : ℝ) (hR : 0 < R)
    (hcenter : ContinuousAt (fun p ↦ H p 0) p₀) (hzero : H p₀ 0 = 0)
    (hdiff : ∀ p, ∀ v ∈ Metric.ball (0 : E) R, DifferentiableAt ℝ (H p) v)
    (hjet : ContinuousAt (fun z : P × E ↦ fderiv ℝ (H z.1) z.2) (p₀, 0))
    (hidentity : fderiv ℝ (H p₀) 0 = ContinuousLinearMap.id ℝ E) :
    ∃ N : TopologicalSpace.Opens P, p₀ ∈ N ∧ ∃ r : ℝ, 0 < r ∧ r < R ∧
      (∀ p ∈ N, ‖H p 0‖ < r / 8) ∧
      (∀ p ∈ N, ∀ v ∈ Metric.closedBall (0 : E) r,
        ‖fderiv ℝ (H p) v - ContinuousLinearMap.id ℝ E‖ < 1 / 2) ∧
      (∀ p ∈ N, ∀ v ∈ Metric.closedBall (0 : E) r,
        ∀ w ∈ Metric.closedBall (0 : E) r,
        ‖H p v - H p w - (v - w)‖ ≤ (1 / 2 : ℝ) * ‖v - w‖) := by
  have hnorm : ContinuousAt (fun z : P × E ↦
      ‖fderiv ℝ (H z.1) z.2 - ContinuousLinearMap.id ℝ E‖) (p₀, 0) :=
    (hjet.sub continuousAt_const).norm
  have hsmall : {z : P × E | ‖fderiv ℝ (H z.1) z.2 -
      ContinuousLinearMap.id ℝ E‖ < 1 / 2} ∈ 𝓝 (p₀, 0) := by
    apply hnorm.preimage_mem_nhds (t := Iio (1 / 2))
    apply Iio_mem_nhds
    simp only [hidentity, sub_self, norm_zero]
    norm_num
  obtain ⟨A, B, hA, hpA, hB, h0B, hAB⟩ := mem_nhds_prod_iff'.mp hsmall
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds h0B)
  let r := min (ε / 2) (R / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hR)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hcenterSmall : {p | ‖H p 0‖ < r / 8} ∈ 𝓝 p₀ := by
    apply hcenter.norm.preimage_mem_nhds (t := Iio (r / 8))
    apply Iio_mem_nhds
    rw [hzero, norm_zero]
    positivity
  obtain ⟨C, hCsub, hC, hpC⟩ := mem_nhds_iff.mp hcenterSmall
  refine ⟨⟨A ∩ C, hA.inter hC⟩, ⟨hpA, hpC⟩, r, hr, hrR, ?_, ?_, ?_⟩
  · intro p hp
    change p ∈ A ∩ C at hp
    exact hCsub hp.2
  · intro p hp v hv
    change p ∈ A ∩ C at hp
    exact @hAB (p, v) (show (p, v) ∈ A ×ˢ B from
      ⟨hp.1, hεB (Metric.closedBall_subset_ball hrε hv)⟩)
  · intro p hp v hv w hw
    change p ∈ A ∩ C at hp
    have hbound (z : E) (hz : z ∈ Metric.closedBall (0 : E) r) :
        ‖fderiv ℝ (H p) z - ContinuousLinearMap.id ℝ E‖ ≤ 1 / 2 :=
      (@hAB (p, z) (show (p, z) ∈ A ×ˢ B from
        ⟨hp.1, hεB (Metric.closedBall_subset_ball hrε hz)⟩)).le
    have hderiv (z : E) (hz : z ∈ Metric.closedBall (0 : E) r) :=
      hdiff p z (Metric.closedBall_subset_ball hrR hz)
    simpa only [ContinuousLinearMap.id_apply] using
      (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun z hz ↦ (hderiv z hz).hasFDerivAt.hasFDerivWithinAt) hbound hw hv

end HolomorphicAnosov.Analysis

