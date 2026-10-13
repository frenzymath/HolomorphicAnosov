import HolomorphicAnosov.Geometry.PositiveBilinearOpenCone
import HolomorphicAnosov.Geometry.SmoothConvexBundleSelection
import HolomorphicAnosov.Paper.Zhang.StableFoliationsPositiveFormUnitSublevelBounded

/-! This file constructs smooth positive bilinear tensors approximating a continuous positive tensor on a closed set (Wockel, Thm. 11). -/

open Set Bundle Filter
open scoped Topology Manifold ContDiff Bundle
noncomputable section
namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

set_option maxHeartbeats 600000 in
/-- A continuous positive tensor on a closed set admits a smooth positive bilinear approximation with prescribed relative quadratic bounds. -/
theorem exists_smooth_positive_bilinear_comparison
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (Λ : Set M) (hΛ : IsClosed Λ)
    (Q : ∀ x : Λ, TangentSpace 𝓘(ℝ, E) (x : M) →L[ℝ]
      TangentSpace 𝓘(ℝ, E) (x : M) →L[ℝ] ℝ)
    (hQ : Continuous (fun x : Λ ↦
      (⟨(x : M), Q x⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
          TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ))))
    (hQpos : ∀ (x : Λ) v, v ≠ 0 → 0 < Q x v v)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : Cₛ^∞⟮𝓘(ℝ, E); (E →L[ℝ] E →L[ℝ] ℝ),
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
        TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)⟯,
      (∀ (x : M) v, v ≠ 0 → 0 < s x v v) ∧
      ∀ (x : Λ) v, (1 - δ) * Q x v v ≤ s x v v ∧
        s x v v ≤ (1 + δ) * Q x v v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let V := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ
  let P : Set (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) V) :=
    {z | ∀ v, v ≠ 0 → 0 < z.snd v v}
  let K : Set (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) V) :=
    {z | z.proj ∈ Λ}
  let b : K → Λ := fun z ↦ ⟨z.val.proj, z.property⟩
  have hb : Continuous b :=
    ((FiberBundle.continuous_proj (F := E →L[ℝ] E →L[ℝ] ℝ) (E := V)).comp
      continuous_subtype_val).subtype_mk _
  have hQc : Continuous (fun z : K ↦
      (⟨z.val.proj, Q (b z)⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) V)) := hQ.comp hb
  have hP : IsOpen P := isOpen_positive_bilinear_tensors
  have hK : IsClosed K := hΛ.preimage
    (FiberBundle.continuous_proj (F := E →L[ℝ] E →L[ℝ] ℝ) (E := V))
  let U : Set K := {z |
    (⟨z.val.proj, z.val.snd - (1 - δ) • Q (b z)⟩ :
      TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) V) ∈ P ∧
    (⟨z.val.proj, (1 + δ) • Q (b z) - z.val.snd⟩ :
      TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) V) ∈ P}
  have hU : IsOpen U := by
    have hlo := continuous_bundle_linear_combination V (fun z : K ↦ z.val.proj)
      (fun z ↦ z.val.snd) (fun z ↦ Q (b z)) continuous_subtype_val hQc 1 (1 - δ)
    have hhi := continuous_bundle_linear_combination V (fun z : K ↦ z.val.proj)
      (fun z ↦ Q (b z)) (fun z ↦ z.val.snd) hQc continuous_subtype_val (1 + δ) 1
    convert (hP.preimage hlo).inter (hP.preimage hhi) using 1
    ext z
    simp only [U, mem_inter_iff, mem_preimage, mem_ofPred_eq, one_smul]
  let O : Set (TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) V) :=
    P ∩ {z | ∀ hz : z ∈ K, (⟨z, hz⟩ : K) ∈ U}
  have hO : IsOpen O := hP.inter (isOpen_constraint_on_closed hK hU)
  have hconv : ∀ x, Convex ℝ {A : V x | (⟨x, A⟩ : TotalSpace _ V) ∈ O} := by
    intro x A hA B hB a c ha hc hac
    obtain ⟨hAp, hAc⟩ := hA
    obtain ⟨hBp, hBc⟩ := hB
    constructor
    · intro v hv
      have hpa := hAp v hv
      have hpb := hBp v hv
      change 0 < a * A v v + c * B v v
      have hna := mul_nonneg ha hpa.le
      have hnc := mul_nonneg hc hpb.le
      rcases eq_or_lt_of_le ha with he | he
      · have heq : a = 0 := he.symm
        have hc1 : c = 1 := by linarith
        simpa [heq, hc1] using hpb
      · exact add_pos_of_pos_of_nonneg (mul_pos he hpa) hnc
    · intro hx
      obtain ⟨hAl, hAu⟩ := hAc hx
      obtain ⟨hBl, hBu⟩ := hBc hx
      constructor <;> intro v hv
      · have h1 := hAl v hv
        have h2 := hBl v hv
        change 0 < a * A v v + c * B v v - (1 - δ) * Q ⟨x, hx⟩ v v
        change 0 < A v v - (1 - δ) * Q ⟨x, hx⟩ v v at h1
        change 0 < B v v - (1 - δ) * Q ⟨x, hx⟩ v v at h2
        have heq := congrArg (fun z : ℝ ↦ z * ((1 - δ) * Q ⟨x, hx⟩ v v)) hac
        rcases eq_or_lt_of_le ha with he | he
        · have ha0 : a = 0 := he.symm
          have hc1 : c = 1 := by linarith
          simpa [ha0, hc1] using h2
        · nlinarith [mul_pos he h1, mul_nonneg hc h2.le]
      · have h1 := hAu v hv
        have h2 := hBu v hv
        change 0 < (1 + δ) * Q ⟨x, hx⟩ v v - (a * A v v + c * B v v)
        change 0 < (1 + δ) * Q ⟨x, hx⟩ v v - A v v at h1
        change 0 < (1 + δ) * Q ⟨x, hx⟩ v v - B v v at h2
        have heq := congrArg (fun z : ℝ ↦ z * ((1 + δ) * Q ⟨x, hx⟩ v v)) hac
        rcases eq_or_lt_of_le ha with he | he
        · have ha0 : a = 0 := he.symm
          have hc1 : c = 1 := by linarith
          simpa [ha0, hc1] using h2
        · nlinarith [mul_pos he h1, mul_nonneg hc h2.le]
  have hne : ∀ x, ∃ A : V x, (⟨x, A⟩ : TotalSpace _ V) ∈ O := by
    intro x
    by_cases hx : x ∈ Λ
    · refine ⟨Q ⟨x, hx⟩, hQpos ⟨x, hx⟩, ?_⟩
      intro hx'
      constructor <;> intro v hv
      · change 0 < Q ⟨x, hx⟩ v v - (1 - δ) * Q ⟨x, hx⟩ v v
        nlinarith [mul_pos hδ (hQpos ⟨x, hx⟩ v hv)]
      · change 0 < (1 + δ) * Q ⟨x, hx⟩ v v - Q ⟨x, hx⟩ v v
        nlinarith [mul_pos hδ (hQpos ⟨x, hx⟩ v hv)]
    · refine ⟨g.inner x, g.pos x, ?_⟩
      intro hx'
      exact (hx hx').elim
  have : ∀ x : M, ContinuousAdd (TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) :=
    fun _ ↦ inferInstance
  let : ∀ x, AddCommGroup (V x) := fun x ↦ inferInstanceAs
    (AddCommGroup (TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ))
  let : ∀ x, TopologicalSpace (V x) := fun x ↦ inferInstanceAs
    (TopologicalSpace (TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ))
  let : ∀ x, Module ℝ (V x) := fun x ↦ inferInstanceAs
    (Module ℝ (TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ))
  obtain ⟨s, hs⟩ := exists_smooth_section_mem_open_convex (E := E) (M := M)
    (F := E →L[ℝ] E →L[ℝ] ℝ) V O hO hconv hne
  refine ⟨s, fun x ↦ (hs x).1, ?_⟩
  intro x v
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨hl, hu⟩ := (hs (x : M)).2 x.property
  have hl' := hl v hv
  have hu' := hu v hv
  change 0 < s x v v - (1 - δ) * Q x v v at hl'
  change 0 < (1 + δ) * Q x v v - s x v v at hu'
  constructor <;> linarith

/-- Symmetrization preserves smoothness and diagonal values of a bilinear tensor. -/
theorem contMDiff_bilinear_flip
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (s : ∀ x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ]
      TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
    (hs : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (s x))) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨g.toRiemannianMetric⟩
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (s x).flip) := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  intro x₀
  rw [contMDiffAt_section]
  have hsc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x ↦ bilinearCoordinates x₀ x (s x)) x₀ :=
    (contMDiffAt_section x₀).mp (hs x₀)
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hf : ContMDiff 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ L :=
    ContinuousLinearMap.contMDiff (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) L
  apply (hf.contMDiffAt.comp x₀ hsc).congr_of_eventuallyEq
  have hx : ∀ᶠ x in 𝓝 x₀,
      x ∈ (trivializationAt E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) x₀).baseSet :=
    (trivializationAt E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  filter_upwards [hx] with x hx
  change bilinearCoordinates x₀ x (s x).flip =
    (bilinearCoordinates x₀ x (s x)).flip
  ext v w
  rw [ContinuousLinearMap.flip_apply, bilinearCoordinates_apply _ _ _ hx,
    bilinearCoordinates_apply _ _ _ hx, ContinuousLinearMap.flip_apply]

/-- Every positive continuous quadratic tensor on a closed subset admits smooth Riemannian approximations with any prescribed positive relative error. -/
theorem exists_smooth_metric_quadratic_comparison
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    (Λ : Set M) (hΛ : IsClosed Λ)
    (Q : ∀ x : Λ, TangentSpace 𝓘(ℝ, E) (x : M) →L[ℝ]
      TangentSpace 𝓘(ℝ, E) (x : M) →L[ℝ] ℝ)
    (hQ : Continuous (fun x : Λ ↦
      (⟨(x : M), Q x⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
          TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ))))
    (hQpos : ∀ (x : Λ) v, v ≠ 0 → 0 < Q x v v)
    (g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x),
      ∀ (x : Λ) v, (1 - δ) * Q x v v ≤ h.inner x v v ∧
        h.inner x v v ≤ (1 + δ) * Q x v v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨s, hspos, hsbound⟩ :=
    exists_smooth_positive_bilinear_comparison Λ hΛ Q hQ hQpos g δ hδ
  let A (x : M) := (1 / 2 : ℝ) • (s x + (s x).flip)
  have hdiag (x : M) (v : TangentSpace 𝓘(ℝ, E) x) : A x v v = s x v v := by
    simp only [A, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  have hpos (x : M) (v : TangentSpace 𝓘(ℝ, E) x) (hv : v ≠ 0) : 0 < A x v v := by
    rw [hdiag]
    exact hspos x v hv
  refine ⟨{
    inner := A
    symm := ?_
    pos := hpos
    isVonNBounded := fun x ↦ StableFoliationsSupport.positive_form_unit_sublevel_bounded
      (A x) (hpos x)
    contMDiff := ?_ }, ?_⟩
  · intro x v w
    simp only [A, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  · exact (s.contMDiff.add_section (contMDiff_bilinear_flip g s s.contMDiff)).const_smul_section
  · intro x v
    simpa only [hdiag] using hsbound x v

end HolomorphicAnosov
