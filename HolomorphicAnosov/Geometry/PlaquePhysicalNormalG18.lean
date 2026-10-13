import HolomorphicAnosov.Geometry.Riemannian.PositiveBilinearCoercivity
import Mathlib.Analysis.Normed.Group.Bounded
import HolomorphicAnosov.Geometry.ExponentialDerivativeZeroG18
import HolomorphicAnosov.Geometry.NativePlaqueSecondDerivativeG18
import HolomorphicAnosov.Geometry.MetricChartTensorG18
import HolomorphicAnosov.Geometry.ParametricMetricNormalFrameG18
import HolomorphicAnosov.Geometry.MetricChartTensorG18
import HolomorphicAnosov.Geometry.PlaqueMetricNormalProjectionG18

noncomputable section
open Set Manifold Bundle
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov
variable {E K : Type*} {r : ℕ} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup K] [NormedSpace ℝ K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
local instance physicalNormalInstanceG18_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance physicalNormalInstanceG18_2 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

omit [FiniteDimensional ℝ E] in
/-- The chart tensor is the metric pulled back through the inverse tangent trivialization. (Lee, Ch.
13) -/
theorem originalMetricChartTensor_trivialization_g18
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (anchor x : M) (hx : x ∈ (extChartAt 𝓘(ℝ,E) anchor).source) (v w : E) :
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let hx' : x ∈ tr.baseSet := by
      simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
    let J := tr.continuousLinearEquivAt ℝ x hx'
    originalMetricChartTensor_g18 g anchor ((extChartAt 𝓘(ℝ,E) anchor) x) v w =
      g.inner x (J.symm v) (J.symm w) := by
  dsimp only
  let ca := extChartAt 𝓘(ℝ,E) anchor
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
  have hx' : x ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  let J := tr.continuousLinearEquivAt ℝ x hx'
  have hJi : J.symm.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca.symm (ca x) := by
    rw [show J.symm.toContinuousLinearMap = tr.symmL ℝ x from
      tr.symm_continuousLinearEquivAt_eq' hx']
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ,mfderivWithin_univ] using
      (TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ,E))
        (by simpa only [extChartAt_source] using hx))
  unfold originalMetricChartTensor_g18
  simp only [ContinuousLinearMap.bilinearComp_apply]
  rw [← hJi]
  rw [ca.left_inv hx]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Chart metric-normal vectors remain normal after the inverse tangent trivialization. (Lee, Ch.
13; HPS, proof of (6.1), pp. 94–95) -/
theorem plaque_physical_normal_g18 (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (anchor : M) (P : (Fin r → ℝ) → M) (u : Fin r → ℝ)
    (hP : MDifferentiableAt 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u)
    (hPi : Function.Injective (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u))
    (hx : P u ∈ (extChartAt 𝓘(ℝ,E) anchor).source)
    (N₀ : K →L[ℝ] E) (k : K) :
    let ca := extChartAt 𝓘(ℝ,E) anchor
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let hx' : P u ∈ tr.baseSet := by
      simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
    let J := tr.continuousLinearEquivAt ℝ (P u) hx'
    let D := fderiv ℝ (ca ∘ P) u
    let β := originalMetricChartTensor_g18 g anchor (ca (P u))
    ∀ v ∈ (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u).range,
      g.inner (P u) (J.symm (plaqueNormalFrame β D N₀ k)) v = 0 := by
  dsimp only
  let ca := extChartAt 𝓘(ℝ,E) anchor
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
  have hx' : P u ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  let J := tr.continuousLinearEquivAt ℝ (P u) hx'
  let D := fderiv ℝ (ca ∘ P) u
  let β := originalMetricChartTensor_g18 g anchor (ca (P u))
  have hJ : J.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca (P u) := by
    rw [show J.toContinuousLinearMap = tr.continuousLinearMapAt ℝ (P u) from
      tr.coe_continuousLinearEquivAt_eq' hx']
    exact TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hx)
  have hJi : J.symm.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca.symm (ca (P u)) := by
    rw [show J.symm.toContinuousLinearMap = tr.symmL ℝ (P u) from
      tr.symm_continuousLinearEquivAt_eq' hx']
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ,mfderivWithin_univ] using
      (TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ,E))
        (by simpa only [extChartAt_source] using hx))
  have hD : D = J.toContinuousLinearMap.comp (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u) := by
    rw [hJ]
    have hh := mfderiv_comp u (mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using hx)) hP
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hDi : Function.Injective D := by
    rw [hD]
    exact J.injective.comp hPi
  have hβpos : ∀ w, w ≠ 0 → 0 < β w w :=
    originalMetricChartTensor_pos_g18 g anchor (ca (P u)) (ca.map_source hx)
  have hβ (a b : E) : β a b = g.inner (P u) (J.symm a) (J.symm b) := by
    unfold β originalMetricChartTensor_g18
    simp only [ContinuousLinearMap.bilinearComp_apply]
    rw [← hJi]
    rw [ca.left_inv hx]
    rfl
  intro v hv
  obtain ⟨v₀,rfl⟩ := hv
  have hh := plaqueMetricProjection_normal β hβpos D hDi (N₀ k) v₀
  have hN : plaqueNormalFrame β D N₀ k = N₀ k - plaqueMetricProjection β D (N₀ k) := rfl
  rw [← hN,hβ] at hh
  have hc : J.symm (D v₀) = mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u v₀ := by
    rw [hD]
    exact J.symm_apply_apply _
  rw [hc] at hh
  exact hh
omit [FiniteDimensional ℝ E] in
/-- Metric-normal vectors remain normal in every receiving chart, with the same quadratic norm.
(Lee, Ch. 13) -/
theorem plaque_physical_to_coordinate_normal_g18 (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (anchor : M) (P : (Fin r → ℝ) → M) (u : Fin r → ℝ)
    (hP : MDifferentiableAt 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u)
    (hx : P u ∈ (extChartAt 𝓘(ℝ,E) anchor).source)
    (ν : TangentSpace 𝓘(ℝ,E) (P u))
    (hν : ∀ v ∈ (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u).range, g.inner (P u) ν v = 0) :
    let ca := extChartAt 𝓘(ℝ,E) anchor
    let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
    let hx' : P u ∈ tr.baseSet := by
      simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
    let J := tr.continuousLinearEquivAt ℝ (P u) hx'
    let D := fderiv ℝ (ca ∘ P) u
    let β := originalMetricChartTensor_g18 g anchor (ca (P u))
    (∀ v : Fin r → ℝ, β (J ν) (D v) = 0) ∧
      β (J ν) (J ν) = g.inner (P u) ν ν := by
  dsimp only
  let ca := extChartAt 𝓘(ℝ,E) anchor
  let tr := trivializationAt E (TangentSpace 𝓘(ℝ,E)) anchor
  have hx' : P u ∈ tr.baseSet := by
    simpa only [tr,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hx
  let J := tr.continuousLinearEquivAt ℝ (P u) hx'
  let D := fderiv ℝ (ca ∘ P) u
  let β := originalMetricChartTensor_g18 g anchor (ca (P u))
  have hJ : J.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca (P u) := by
    rw [show J.toContinuousLinearMap = tr.continuousLinearMapAt ℝ (P u) from
      tr.coe_continuousLinearEquivAt_eq' hx']
    exact TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa only [extChartAt_source] using hx)
  have hJi : J.symm.toContinuousLinearMap = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) ca.symm (ca (P u)) := by
    rw [show J.symm.toContinuousLinearMap = tr.symmL ℝ (P u) from
      tr.symm_continuousLinearEquivAt_eq' hx']
    simpa only [ModelWithCorners.Boundaryless.range_eq_univ,mfderivWithin_univ] using
      (TangentBundle.symmL_trivializationAt (I := 𝓘(ℝ,E))
        (by simpa only [extChartAt_source] using hx))
  have hD : D = J.toContinuousLinearMap.comp (mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u) := by
    rw [hJ]
    have hh := mfderiv_comp u (mdifferentiableAt_extChartAt
      (by simpa only [extChartAt_source] using hx)) hP
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hβ (a b : E) : β a b = g.inner (P u) (J.symm a) (J.symm b) := by
    unfold β originalMetricChartTensor_g18
    simp only [ContinuousLinearMap.bilinearComp_apply]
    rw [← hJi]
    rw [ca.left_inv hx]
    rfl
  constructor
  · intro v
    rw [hβ,J.symm_apply_apply]
    have hc : J.symm (D v) = mfderiv 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,E) P u v := by
      rw [hD]
      exact J.symm_apply_apply _
    rw [hc]
    exact hν _ ⟨v,rfl⟩
  · rw [hβ,J.symm_apply_apply]

omit [FiniteDimensional ℝ E] in
/-- A metric-normal vector has unique normal-frame coefficients bounded by the inverse full frame
and the metric norm. (HPS, proof of (6.1), pp. 94–95) -/
theorem plaque_normal_frame_coefficients_g18 (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v)
    (D : (Fin r → ℝ) →L[ℝ] E) (hD : Function.Injective D)
    (N₀ : K →L[ℝ] E)
    (hA : (D.coprod (plaqueNormalFrame b D N₀)).IsInvertible)
    (w : E) (hw : ∀ v, b w (D v) = 0)
    (C : ℝ) (hmetric : ∀ z : E, ‖z‖ ≤ C * Real.sqrt (b z z)) :
    let N := plaqueNormalFrame b D N₀
    let A := D.coprod N
    (A.inverse w).1 = 0 ∧ N (A.inverse w).2 = w ∧
      ‖(A.inverse w).2‖ ≤ ‖A.inverse‖ * C * Real.sqrt (b w w) := by
  let N := plaqueNormalFrame b D N₀
  let A := D.coprod N
  have hPw : plaqueMetricProjection b D w = 0 := by
    apply plaqueMetricProjection_unique b hb D hD w 0
    · exact ⟨0,D.map_zero⟩
    · intro v
      simpa only [sub_zero] using hw v
  have hcw : plaqueMetricCoordinates b D w = 0 := by
    apply hD
    exact hPw.trans D.map_zero.symm
  have hcN (k : K) : plaqueMetricCoordinates b D (N k) = 0 := by
    change plaqueMetricCoordinates b D (N₀ k - D (plaqueMetricCoordinates b D (N₀ k))) = 0
    rw [map_sub, plaqueMetricCoordinates_derivative b hb D hD, sub_self]
  have hsplit : D (A.inverse w).1 + N (A.inverse w).2 = w :=
    hA.self_apply_inverse w
  have hfirst : (A.inverse w).1 = 0 := by
    have hh := congrArg (plaqueMetricCoordinates b D) hsplit
    rwa [map_add,plaqueMetricCoordinates_derivative b hb D hD,hcN,hcw,add_zero] at hh
  refine ⟨hfirst,?_,?_⟩
  · simpa only [hfirst,D.map_zero,zero_add] using hsplit
  · calc
      ‖(A.inverse w).2‖ ≤ ‖A.inverse‖ * ‖w‖ :=
        (norm_snd_le (A.inverse w)).trans (A.inverse.le_opNorm w)
      _ ≤ ‖A.inverse‖ * (C * Real.sqrt (b w w)) :=
        mul_le_mul_of_nonneg_left (hmetric w) (norm_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
end HolomorphicAnosov


noncomputable section
open Set Bundle
open scoped Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
namespace HolomorphicAnosov
variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance physicalNormalInstanceG18_101 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance physicalNormalInstanceG18_102 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

/-- The coordinate norm is uniformly bounded by the norm of a continuous positive tensor on a
compact parameter set. (Lee, Ch. 13) -/
theorem compact_tensor_norm_comparison_g18 (b : P → E →L[ℝ] E →L[ℝ] ℝ) (K : Set P) (hK : IsCompact K)
    (hb : ContinuousOn b K) (hpos : ∀ p ∈ K, ∀ v : E, v ≠ 0 → 0 < b p v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ K, ∀ v : E, ‖v‖ ≤ C * Real.sqrt (b p v v) := by
  have hcont : ContinuousOn (fun z : P × E ↦ b z.1 z.2 z.2)
      (K ×ˢ sphere (0 : E) 1) :=
    ((hb.comp continuousOn_fst (fun z hz ↦ hz.1)).clm_apply continuousOn_snd).clm_apply continuousOn_snd
  obtain ⟨m,hm,hbound⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_forall_le'
    hcont (a := 0) (fun z hz ↦ hpos z.1 hz.1 z.2 (by
      intro heq
      simp [heq] at hz))
  have hquad (p : P) (hp : p ∈ K) (v : E) : m * ‖v‖ ^ 2 ≤ b p v v := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hs : (‖v‖⁻¹ : ℝ) • v ∈ sphere (0 : E) 1 := by simp [norm_smul,hn]
    have hh := mul_le_mul_of_nonneg_right (hbound (p,(‖v‖⁻¹ : ℝ) • v) ⟨hp,hs⟩) (sq_nonneg ‖v‖)
    convert hh using 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  have hmroot : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  refine ⟨(Real.sqrt m)⁻¹,inv_pos.2 hmroot,?_⟩
  intro p hp v
  have h := Real.sqrt_le_sqrt (hquad p hp v)
  rw [Real.sqrt_mul hm.le,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] at h
  calc
    ‖v‖ = (Real.sqrt m)⁻¹ * (Real.sqrt m * ‖v‖) := by field_simp
    _ ≤ (Real.sqrt m)⁻¹ * Real.sqrt (b p v v) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.2 hmroot.le)
end HolomorphicAnosov
namespace HolomorphicAnosov.HPS
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {Dist : RealTangentDistribution 𝓘(ℝ,E) M}
  {ι : Type u} {L : ι → Type u} {r : ι → ℕ}
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin (r i) → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin (r i) → ℝ) ∞ (L i)]
  {F : LeafPartition Dist ι L r} {x : M} {d : ℕ}
  {Φ : FiniteC1NativePlaqueFamily F x d} {n : ℕ}

local instance physicalNormalInstanceG18_3 : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance physicalNormalInstanceG18_4 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance physicalNormalInstanceG18_5 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)
local instance physicalNormalInstanceG18_6 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance physicalNormalInstanceG18_7 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance physicalNormalInstanceG18_8 : NormedAddCommGroup ((Fin d → ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := Fin d → ℝ)
    (F := E →L[ℝ] E →L[ℝ] ℝ) (σ₁₂ := RingHom.id ℝ)

/-- The metric norm of a plaque normal-frame vector is continuous at the zero center and vanishes
there. (HPS, proof of (6.1), pp. 94–95) -/
theorem FiniteOrderNativePlaqueCoherence.original_normal_size_continuous_g18 (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ : Φ.family.centerDomain) :
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    let size := fun z : (Φ.family.centerDomain × (Fin d → ℝ)) × K ↦
      Real.sqrt (b z.1 (N z.1 z.2) (N z.1 z.2))
    ContinuousAt size ((p₀,0),0) ∧ size ((p₀,0),0) = 0 := by
  let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
  let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
  let q := H.coordinate
  let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (q z.1) z.2
  let β := originalMetricChartTensor_g18 g Φ.family.receivingAnchor
  let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ β (q z.1 z.2)
  let T := (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).target
  have hΩ : IsOpen Ω := isOpen_univ.prod Metric.isOpen_ball
  have hpΩ : (p₀,0) ∈ Ω := ⟨mem_univ _,Metric.mem_ball_self Φ.family.radius_pos⟩
  have hq : ContinuousOn (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := (continuousOn_extChartAt (I := 𝓘(ℝ,E)) Φ.family.receivingAnchor).comp_continuous
      Φ.family.jointly_continuous (fun z ↦ Φ.family.receiving_domain z.1 z.2 z.2.property)
    have hc' := hc.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    exact hc'.congr (fun z ↦ (H.coordinate_eq z.1.1 z.property.2).symm)
  have hmaps : MapsTo (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω T := by
    intro z hz
    change q z.1 z.2 ∈ T
    rw [show q z.1 z.2 = extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param z.2) from H.coordinate_eq z.1 hz.2]
    exact (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).map_source
      (Φ.family.receiving_domain z.1 z.2 hz.2)
  have hD : ContinuousOn D Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := Φ.family.jointly_continuous_derivative.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    apply hc.congr
    intro z
    have heq : q z.1.1 =ᶠ[nhds z.1.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds z.property.2] with v hv
      exact H.coordinate_eq z.1.1 hv
    exact heq.fderiv_eq.symm
  have hDin : ∀ z ∈ Ω, Function.Injective (D z) := by
    intro z hz
    have hv : z.2 ∈ (Φ.family.plaque z.1).domain := by
      rw [Φ.family.domain_eq]; exact hz.2
    have hφ := ((Φ.family.plaque z.1).smooth z.2 hv).contMDiffAt
      ((Φ.family.plaque z.1).domain_open.mem_nhds hv)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E))
      (by simpa only [extChartAt_source] using Φ.family.receiving_domain z.1 z.2 hz.2)
    have hchain := mfderiv_comp z.2 hc (hφ.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hchain
    change fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param v)) z.2 = _ at hchain
    have heq : q z.1 =ᶠ[nhds z.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with v hv
      exact H.coordinate_eq z.1 hv
    change Function.Injective (fderiv ℝ (q z.1) z.2)
    rw [heq.fderiv_eq, hchain]
    apply Function.Injective.comp _ ((Φ.family.plaque z.1).immersed z.2 hv)
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
      (Φ.family.receiving_domain z.1 z.2 hz.2)
    rw [← hA]
    exact A.injective
  have hβ := originalMetricChartTensor_contDiffOn_g18 g Φ.family.receivingAnchor
  have hb : ContinuousOn b Ω := hβ.continuousOn.comp hq hmaps
  have hbpos : ∀ z ∈ Ω, ∀ v, v ≠ 0 → 0 < b z v v := by
    intro z hz v hv
    exact originalMetricChartTensor_pos_g18 g Φ.family.receivingAnchor _ (hmaps hz) v hv
  let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
  let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
  have hbc : ContinuousAt b (p₀,0) := hb.continuousAt (hΩ.mem_nhds hpΩ)
  have hDc : ContinuousAt D (p₀,0) := hD.continuousAt (hΩ.mem_nhds hpΩ)
  have hProj : ContinuousAt (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      plaqueMetricProjection (b z) (D z)) (p₀,0) :=
    ((contDiffAt_plaqueMetricProjection (b (p₀,0)) (hbpos _ hpΩ)
      (D (p₀,0)) (hDin _ hpΩ) 0).continuousAt).comp (f := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ (b z,D z)) (hbc.prodMk hDc)
  have hN : ContinuousAt N (p₀,0) :=
    (continuousAt_const.sub hProj).clm_comp continuousAt_const
  have hNv : ContinuousAt (fun z : (Φ.family.centerDomain × (Fin d → ℝ)) × K ↦
      N z.1 z.2) ((p₀,0),0) :=
    (hN.comp (x := ((p₀,0), (0 : K))) (f := fun z : (Φ.family.centerDomain × (Fin d → ℝ)) × K ↦ z.1) continuousAt_fst).clm_apply continuousAt_snd
  constructor
  · exact Real.continuous_sqrt.continuousAt.comp
      (((hbc.comp (x := ((p₀,0), (0 : K))) (f := fun z : (Φ.family.centerDomain × (Fin d → ℝ)) × K ↦ z.1) continuousAt_fst).clm_apply hNv).clm_apply hNv)
  · simp only [map_zero,Real.sqrt_zero]
/-- Metric-normal coefficients are uniformly bounded by the metric norm near a plaque center. (HPS,
proof of (6.1), pp. 94–95) -/
theorem FiniteOrderNativePlaqueCoherence.original_normal_coefficients_locally_bounded_g18 (H : FiniteOrderNativePlaqueCoherence Φ n)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E (TangentSpace 𝓘(ℝ,E) : M → Type _))
    (p₀ : Φ.family.centerDomain) :
    let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (H.coordinate z.1) z.2
    let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
      originalMetricChartTensor_g18 g Φ.family.receivingAnchor (H.coordinate z.1 z.2)
    let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
    let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
    ∃ Q ∈ 𝓝 p₀, ∃ R : ℝ, 0 < R ∧ ∃ C : ℝ, 0 < C ∧
      ∀ p ∈ Q, ∀ u ∈ Metric.ball (0 : Fin d → ℝ) R,
        u ∈ Metric.ball (0 : Fin d → ℝ) Φ.family.radius ∧
        ((D (p,u)).coprod (N (p,u))).IsInvertible ∧
        ∀ w : E, (∀ v, b (p,u) w (D (p,u) v) = 0) →
          ∃ k : K, N (p,u) k = w ∧ ‖k‖ ≤ C * Real.sqrt (b (p,u) w w) := by
  let B := Metric.ball (0 : Fin d → ℝ) Φ.family.radius
  let Ω := (univ : Set Φ.family.centerDomain) ×ˢ B
  let q := H.coordinate
  let D := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ fderiv ℝ (q z.1) z.2
  let β := originalMetricChartTensor_g18 g Φ.family.receivingAnchor
  let b := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ β (q z.1 z.2)
  let T := (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).target
  have hΩ : IsOpen Ω := isOpen_univ.prod Metric.isOpen_ball
  have hpΩ : (p₀,0) ∈ Ω := ⟨mem_univ _,Metric.mem_ball_self Φ.family.radius_pos⟩
  have hq : ContinuousOn (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := (continuousOn_extChartAt (I := 𝓘(ℝ,E)) Φ.family.receivingAnchor).comp_continuous
      Φ.family.jointly_continuous (fun z ↦ Φ.family.receiving_domain z.1 z.2 z.2.property)
    have hc' := hc.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    exact hc'.congr (fun z ↦ (H.coordinate_eq z.1.1 z.property.2).symm)
  have hmaps : MapsTo (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ q z.1 z.2) Ω T := by
    intro z hz
    change q z.1 z.2 ∈ T
    rw [show q z.1 z.2 = extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param z.2) from H.coordinate_eq z.1 hz.2]
    exact (extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor).map_source
      (Φ.family.receiving_domain z.1 z.2 hz.2)
  have hD : ContinuousOn D Ω := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc := Φ.family.jointly_continuous_derivative.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun z : Ω ↦ z.property.2)))
    apply hc.congr
    intro z
    have heq : q z.1.1 =ᶠ[nhds z.1.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds z.property.2] with v hv
      exact H.coordinate_eq z.1.1 hv
    exact heq.fderiv_eq.symm
  have hDin : ∀ z ∈ Ω, Function.Injective (D z) := by
    intro z hz
    have hv : z.2 ∈ (Φ.family.plaque z.1).domain := by
      rw [Φ.family.domain_eq]; exact hz.2
    have hφ := ((Φ.family.plaque z.1).smooth z.2 hv).contMDiffAt
      ((Φ.family.plaque z.1).domain_open.mem_nhds hv)
    have hc := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E))
      (by simpa only [extChartAt_source] using Φ.family.receiving_domain z.1 z.2 hz.2)
    have hchain := mfderiv_comp z.2 hc (hφ.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hchain
    change fderiv ℝ (fun v ↦ extChartAt 𝓘(ℝ,E) Φ.family.receivingAnchor
      ((Φ.family.plaque z.1).param v)) z.2 = _ at hchain
    have heq : q z.1 =ᶠ[nhds z.2] (fun v ↦ extChartAt 𝓘(ℝ,E)
        Φ.family.receivingAnchor ((Φ.family.plaque z.1).param v)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with v hv
      exact H.coordinate_eq z.1 hv
    change Function.Injective (fderiv ℝ (q z.1) z.2)
    rw [heq.fderiv_eq, hchain]
    apply Function.Injective.comp _ ((Φ.family.plaque z.1).immersed z.2 hv)
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
      (Φ.family.receiving_domain z.1 z.2 hz.2)
    rw [← hA]
    exact A.injective
  have hβ := originalMetricChartTensor_contDiffOn_g18 g Φ.family.receivingAnchor
  have hb : ContinuousOn b Ω := hβ.continuousOn.comp hq hmaps
  have hbpos : ∀ z ∈ Ω, ∀ v, v ≠ 0 → 0 < b z v v := by
    intro z hz v hv
    exact originalMetricChartTensor_pos_g18 g Φ.family.receivingAnchor _ (hmaps hz) v hv
  let K := plaqueNormalSpace (b (p₀,0)) (D (p₀,0))
  let N := fun z ↦ plaqueNormalFrame (b z) (D z) K.subtypeL
  have hbc : ContinuousAt b (p₀,0) := hb.continuousAt (hΩ.mem_nhds hpΩ)
  have hDc : ContinuousAt D (p₀,0) := hD.continuousAt (hΩ.mem_nhds hpΩ)
  let A := fun z ↦ (D z).coprod (N z)
  have hi : ∀ᶠ z in 𝓝 (p₀,0), (A z).IsInvertible :=
    (hbc.prodMk hDc).eventually
      (eventually_invertible_plaque_normal_frame_g18 (b (p₀,0)) (hbpos _ hpΩ)
        (D (p₀,0)) (hDin _ hpΩ))
  have hAc : ContinuousOn A Ω := by
    intro z hz
    have hpc : ContinuousAt (fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦
        plaqueMetricProjection (b z) (D z)) z :=
      ((contDiffAt_plaqueMetricProjection (b z) (hbpos _ hz)
        (D z) (hDin _ hz) 0).continuousAt).comp
          (f := fun z : Φ.family.centerDomain × (Fin d → ℝ) ↦ (b z,D z))
          ((hb.continuousAt (hΩ.mem_nhds hz)).prodMk (hD.continuousAt (hΩ.mem_nhds hz)))
    exact ((hD.continuousAt (hΩ.mem_nhds hz)).continuousLinearMapCoprod
      ((continuousAt_const.sub hpc).clm_comp continuousAt_const)).continuousWithinAt
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have : LocallyCompactSpace Φ.family.centerDomain := Φ.family.centerDomain_open.locallyCompactSpace
  obtain ⟨S,hSn,hS,hSc⟩ := local_compact_nhds (Filter.inter_mem (hΩ.mem_nhds hpΩ) hi)
  have hSΩ : S ⊆ Ω := fun z hz ↦ (hS hz).1
  have hSinv : ∀ z ∈ S, (A z).IsInvertible := fun z hz ↦ (hS hz).2
  obtain ⟨C₀,hC₀,hmetric⟩ := compact_tensor_norm_comparison_g18 b S hSc (hb.mono hSΩ)
    (fun z hz ↦ hbpos z (hSΩ hz))
  have hAi : ContinuousOn (fun z ↦ (A z).inverse) S := by
    intro z hz
    exact (((hSinv z hz).contDiffAt_map_inverse (n := 0)).continuousAt.comp
      (hAc.continuousAt (hΩ.mem_nhds (hSΩ hz)))).continuousWithinAt
  obtain ⟨C₁,hC₁⟩ := hSc.exists_bound_of_continuousOn (f := fun z ↦ (A z).inverse) hAi
  let C₂ := max C₁ 0 + 1
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  obtain ⟨Q,hQ,V,hV,hQV⟩ := mem_nhds_prod_iff.mp hSn
  obtain ⟨R,hR,hRV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨Q,hQ,R,hR,C₂*C₀,mul_pos hC₂ hC₀,?_⟩
  intro p hp u hu
  have hpu : (p,u) ∈ S := hQV ⟨hp,hRV hu⟩
  refine ⟨(hSΩ hpu).2,hSinv _ hpu,?_⟩
  intro w hw
  have hh := plaque_normal_frame_coefficients_g18 (b (p,u)) (hbpos _ (hSΩ hpu))
    (D (p,u)) (hDin _ (hSΩ hpu)) K.subtypeL (hSinv _ hpu) w hw C₀
    (hmetric _ hpu)
  refine ⟨((A (p,u)).inverse w).2,hh.2.1,hh.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_right
    ((hC₁ _ hpu).trans ((le_max_left C₁ 0).trans (le_add_of_nonneg_right zero_le_one))) hC₀.le
end HolomorphicAnosov.HPS



