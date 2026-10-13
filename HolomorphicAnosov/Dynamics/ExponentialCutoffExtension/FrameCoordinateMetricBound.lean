import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff

open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-!
# Uniform comparison of frame coordinates and the given metric

Source: Lee (2003), Lemma 11.19, p. 278. The explicit compact-frame version
uses the existing uniform seminorm comparison, which normalizes vectors on a
compact unit sphere. These estimates retain the original tangent frames.
-/

/-- Coordinate norms are uniformly bounded by the metric norm on a compact
frame core. Source: Lee (2003), Lemma 11.19. Pull back the metric seminorm along
the inverse frame on the compact subtype A ∩ K and compare it with the fixed
coordinate norm. Continuity follows from the inverse bundle trivialization;
positivity follows from its injectivity. Apply uniform_seminorm_upper_bound,
then express its inverse-frame value as symmL. Empty cores and zero-dimensional
fibres are covered by that seminorm theorem. -/
theorem coordinate_metric_upper_bound
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A)
    (K : Set M) (hK : IsCompact K)
    (e : Bundle.Trivialization E
      (TotalSpace.proj (F := E) (E := fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)))
    (he : e.IsLinear ℝ) (hKe : K ⊆ e.baseSet) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : A), (p : M) ∈ K → ∀ u : E,
      ‖u‖ ≤ C * metricNorm g (p : M)
        (e.symmL ℝ (p : M) u) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let metricSeminorm : ∀ p : A, Seminorm ℝ (TangentSpace 𝓘(ℝ, E) (p : M)) :=
    fun p ↦ Seminorm.of (fun v ↦ ‖v‖)
      (fun v w ↦ norm_add_le _ _) (fun a v ↦ norm_smul _ _)
  have hmetric : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦
      metricNorm g z.proj z.snd) := by
    unfold metricNorm
    have h := Continuous.inner_bundle (F := E)
      (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
      (b := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.proj)
      (v := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd)
      (w := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd) continuous_id continuous_id
    exact Real.continuous_sqrt.comp h
  let : e.IsLinear ℝ := he
  let X := {p : M // p ∈ A ∩ K}
  let : CompactSpace X := isCompact_iff_compactSpace.mp (hA.inter_right hK.isClosed)
  let frame (y : X) : E →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (y.1 : M) :=
    (e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm.toLinearMap
  have hf : Continuous (fun z : X × E ↦
      (⟨(z.1 : M), frame z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    let coords : X × E → M × E := fun z ↦ (z.1, z.2)
    have hc : Continuous coords := by
      simpa [coords] using (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact e.continuousOn_symm.comp_continuous hc
      (fun z ↦ ⟨hKe z.1.2.2, mem_univ _⟩)
  let coordSeminorm : Seminorm ℝ E := Seminorm.of (fun u ↦ ‖u‖)
    (fun u v ↦ norm_add_le _ _) (fun a u ↦ norm_smul _ _)
  let pX : X → Seminorm ℝ E := fun _ ↦ coordSeminorm
  let qX : X → Seminorm ℝ E := fun y ↦
    (metricSeminorm ⟨y.1, y.2.1⟩).comp (frame y)
  have hpX : Continuous (fun z : X × E ↦ pX z.1 z.2) := by
    change Continuous (fun z : X × E ↦ ‖z.2‖)
    exact continuous_norm.comp continuous_snd
  have hqX : Continuous (fun z : X × E ↦ qX z.1 z.2) := by
    have hmc := hmetric.comp hf
    change Continuous (fun z : X × E ↦ ‖frame z.1 z.2‖)
    convert hmc using 1
    ext z
    rfl
  have hqXpos : ∀ y v, v ≠ 0 → 0 < qX y v := by
    intro y v hv
    have hframe : frame y v ≠ 0 := by
      intro hz
      apply hv
      exact (e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm.injective (by
        simpa [frame, map_zero] using hz)
    exact norm_pos_iff.mpr hframe
  obtain ⟨C, hC, hbound⟩ := Preparation.uniform_seminorm_upper_bound
    pX qX hpX hqX hqXpos
  refine ⟨C, hC, ?_⟩
  intro p hp u
  let y : X := ⟨p, ⟨p.property, hp⟩⟩
  have hbound' := hbound y u
  have hframe_eq : frame y u = e.symmL ℝ (p : M) u := by
    rw [e.symmL_apply (R := ℝ) (hKe hp)]
    simp [y, frame, e.linearEquivAt_symm_apply]
  change ‖u‖ ≤ C * ‖frame y u‖ at hbound'
  rw [hframe_eq] at hbound'
  change ‖u‖ ≤ C * ‖e.symmL ℝ (p : M) u‖
  simpa only [show metricNorm g (p : M) (e.symmL ℝ (p : M) u) =
      ‖e.symmL ℝ (p : M) u‖ by rfl] using hbound'

/-- The metric norm is uniformly bounded by coordinate norm on a compact frame
core. Source: Lee (2003), Lemma 11.19. Apply the same compact seminorm comparison
with the roles of the metric pullback and coordinate norm reversed. This is the
estimate transporting a coordinate ball into the intrinsic metric tube. -/
theorem coordinate_metric_lower_bound
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A)
    (K : Set M) (hK : IsCompact K)
    (e : Bundle.Trivialization E
      (TotalSpace.proj (F := E) (E := fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)))
    (he : e.IsLinear ℝ) (hKe : K ⊆ e.baseSet) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : A), (p : M) ∈ K → ∀ u : E,
      metricNorm g (p : M) (e.symmL ℝ (p : M) u) ≤ C * ‖u‖ := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let metricSeminorm : ∀ p : A, Seminorm ℝ (TangentSpace 𝓘(ℝ, E) (p : M)) :=
    fun p ↦ Seminorm.of (fun v ↦ ‖v‖)
      (fun v w ↦ norm_add_le _ _) (fun a v ↦ norm_smul _ _)
  have hmetric : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦
      metricNorm g z.proj z.snd) := by
    unfold metricNorm
    have h := Continuous.inner_bundle (F := E)
      (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
      (b := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.proj)
      (v := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd)
      (w := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd) continuous_id continuous_id
    exact Real.continuous_sqrt.comp h
  let : e.IsLinear ℝ := he
  let X := {p : M // p ∈ A ∩ K}
  let : CompactSpace X := isCompact_iff_compactSpace.mp (hA.inter_right hK.isClosed)
  let frame (y : X) : E →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (y.1 : M) :=
    (e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm.toLinearMap
  have hf : Continuous (fun z : X × E ↦
      (⟨(z.1 : M), frame z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    let coords : X × E → M × E := fun z ↦ (z.1, z.2)
    have hc : Continuous coords := by
      simpa [coords] using (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact e.continuousOn_symm.comp_continuous hc
      (fun z ↦ ⟨hKe z.1.2.2, mem_univ _⟩)
  let coordSeminorm : Seminorm ℝ E := Seminorm.of (fun u ↦ ‖u‖)
    (fun u v ↦ norm_add_le _ _) (fun a u ↦ norm_smul _ _)
  let pX : X → Seminorm ℝ E := fun y ↦
    (metricSeminorm ⟨y.1, y.2.1⟩).comp (frame y)
  let qX : X → Seminorm ℝ E := fun _ ↦ coordSeminorm
  have hpX : Continuous (fun z : X × E ↦ pX z.1 z.2) := by
    have hmc := hmetric.comp hf
    change Continuous (fun z : X × E ↦ ‖frame z.1 z.2‖)
    convert hmc using 1
    ext z
    rfl
  have hqX : Continuous (fun z : X × E ↦ qX z.1 z.2) := by
    change Continuous (fun z : X × E ↦ ‖z.2‖)
    exact continuous_norm.comp continuous_snd
  have hqXpos : ∀ y v, v ≠ 0 → 0 < qX y v := by
    intro y v hv
    exact norm_pos_iff.mpr hv
  obtain ⟨C, hC, hbound⟩ := Preparation.uniform_seminorm_upper_bound
    pX qX hpX hqX hqXpos
  refine ⟨C, hC, ?_⟩
  intro p hp u
  let y : X := ⟨p, ⟨p.property, hp⟩⟩
  have hbound' := hbound y u
  have hframe_eq : frame y u = e.symmL ℝ (p : M) u := by
    rw [e.symmL_apply (R := ℝ) (hKe hp)]
    simp [y, frame, e.linearEquivAt_symm_apply]
  change ‖frame y u‖ ≤ C * ‖u‖ at hbound'
  rw [hframe_eq] at hbound'
  change ‖e.symmL ℝ (p : M) u‖ ≤ C * ‖u‖
  simpa only [show metricNorm g (p : M) (e.symmL ℝ (p : M) u) =
      ‖e.symmL ℝ (p : M) u‖ by rfl] using hbound'

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- A coordinate operator estimate converts to the prescribed fibre norms with
factor M₀ Ctar Csrc / m. Source: the norm-comparison calculation in HPS (1977),
proof of Theorem 5.5, p. 62, using Lee (2003), Lemma 11.19. Bound the receiving
ν norm by the receiving metric norm, then by coordinates and the operator bound;
use the source coordinate/metric estimate and m |v| ≤ ν(v) to finish. -/
theorem coordinate_derivative_to_nu_bound
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (ν : ContinuousRestrictedTangentNorm (E := E) A)
    {m M₀ Csrc Ctar θ : ℝ}
    (hm : 0 < m) (hM₀ : 0 ≤ M₀) (hCsrc : 0 ≤ Csrc)
    (hCtar : 0 ≤ Ctar) (hθ : 0 ≤ θ)
    (hlower : ∀ (p : A) (v), m * metricNorm g (p : M) v ≤ ν.value p v)
    (hupper : ∀ (p : A) (v), ν.value p v ≤ M₀ * metricNorm g (p : M) v)
    (p q : A)
    (es et : Bundle.Trivialization E
      (TotalSpace.proj (F := E) (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)))
    (hes : es.IsLinear ℝ) (het : et.IsLinear ℝ)
    {L : E →L[ℝ] E}
    (hL : ∀ u, ‖L u‖ ≤ θ * ‖u‖)
    (hsrc : ∀ u, ‖u‖ ≤ Csrc * metricNorm g (p : M)
      (es.symmL ℝ (p : M) u))
    (htar : ∀ u, metricNorm g (q : M)
      (et.symmL ℝ (q : M) u) ≤ Ctar * ‖u‖) :
    ∀ u, ν.value q (et.symmL ℝ (q : M) (L u)) ≤
      (M₀ * Ctar * θ * Csrc / m) *
        ν.value p (es.symmL ℝ (p : M) u) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let : es.IsLinear ℝ := hes
  let : et.IsLinear ℝ := het
  intro u
  have hmetric_in : metricNorm g (p : M)
      (es.symmL ℝ (p : M) u) ≤
      (1 / m) * ν.value p (es.symmL ℝ (p : M) u) := by
    calc
      metricNorm g (p : M) (es.symmL ℝ (p : M) u) ≤
          ν.value p (es.symmL ℝ (p : M) u) / m := by
        exact (le_div_iff₀ hm).2 (by
          simpa [mul_comm] using hlower p (es.symmL ℝ (p : M) u))
      _ = (1 / m) * ν.value p (es.symmL ℝ (p : M) u) := by ring
  have hcoord_in : ‖u‖ ≤ (Csrc / m) *
      ν.value p (es.symmL ℝ (p : M) u) := by
    calc
      ‖u‖ ≤ Csrc * metricNorm g (p : M)
          (es.symmL ℝ (p : M) u) := hsrc u
      _ ≤ Csrc * ((1 / m) * ν.value p (es.symmL ℝ (p : M) u)) := by
        exact mul_le_mul_of_nonneg_left hmetric_in hCsrc
      _ = (Csrc / m) * ν.value p (es.symmL ℝ (p : M) u) := by ring
  calc
    ν.value q (et.symmL ℝ (q : M) (L u)) ≤
        M₀ * metricNorm g (q : M)
          (et.symmL ℝ (q : M) (L u)) := hupper q _
    _ ≤ M₀ * (Ctar * ‖L u‖) := by
      exact mul_le_mul_of_nonneg_left (htar (L u)) hM₀
    _ ≤ M₀ * (Ctar * (θ * ‖u‖)) := by
      gcongr
      exact hL u
    _ ≤ (M₀ * Ctar * θ) * ((Csrc / m) *
        ν.value p (es.symmL ℝ (p : M) u)) := by
      rw [show M₀ * (Ctar * (θ * ‖u‖)) =
        (M₀ * Ctar * θ) * ‖u‖ by ring]
      exact mul_le_mul_of_nonneg_left hcoord_in (by positivity)
    _ = (M₀ * Ctar * θ * Csrc / m) *
        ν.value p (es.symmL ℝ (p : M) u) := by ring

end HolomorphicAnosov.ExponentialCutoff

