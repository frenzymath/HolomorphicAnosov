import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base

/-!
# Open metric tubes in paired tangent frames

Source: Lee (2003), local bundle trivializations and Lemma 11.19; the paired
frame restriction in HPS (1977), proof of Theorem 5.5, pp. 61–62.
-/

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The fixed-frame metric tube is open. Pull back the open metric tube in the
original tangent bundle along the inverse trivialization, restricted to its open
base domain. Source: continuity in Lee's local bundle trivializations. -/
theorem isOpen_fixed_frame_metric_domain
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (s : M) {R : ℝ} :
    IsOpen {z : A × E |
      (z.1 : M) ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).baseSet ∧
      metricNorm g (z.1 : M)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2) < R} := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  let φ : A × E → TangentBundle 𝓘(ℝ, E) M := fun z ↦
    ⟨(z.1 : M), e.symm (z.1 : M) z.2⟩
  let B : Set (TangentBundle 𝓘(ℝ, E) M) :=
    {z | z.proj ∈ e.baseSet ∧ metricNorm g z.proj z.snd < R}
  have hB : IsOpen B := by
    have hbase : IsOpen {z : TangentBundle 𝓘(ℝ, E) M | z.proj ∈ e.baseSet} :=
      e.open_baseSet.preimage (FiberBundle.continuous_proj E
        (TangentSpace 𝓘(ℝ, E)))
    have hnorm : IsOpen {z : TangentBundle 𝓘(ℝ, E) M |
        metricNorm g z.proj z.snd < R} := by
      exact isOpen_lt (ExponentialLift.continuous_metricNorm g) continuous_const
    exact hbase.inter hnorm
  have hbase : IsOpen {z : A × E | (z.1 : M) ∈ e.baseSet} := by
    exact e.open_baseSet.preimage
      (continuous_subtype_val.comp continuous_fst)
  have hcoords : Continuous (fun z : A × E ↦ ((z.1 : M), z.2)) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hφ : ContinuousOn φ {z : A × E | (z.1 : M) ∈ e.baseSet} := by
    have h := e.continuousOn_symm.comp hcoords.continuousOn
      (fun z hz ↦ ⟨hz, mem_univ _⟩)
    change ContinuousOn (fun z : A × E ↦
      (⟨(z.1 : M), e.symm (z.1 : M) z.2⟩ :
        TangentBundle 𝓘(ℝ, E) M))
      {z : A × E | (z.1 : M) ∈ e.baseSet} at h
    exact h
  have hsubset : φ ⁻¹' B ⊆ {z : A × E | (z.1 : M) ∈ e.baseSet} := by
    intro z hz
    change φ z ∈ B at hz
    exact hz.1
  have hopen : IsOpen (φ ⁻¹' B) :=
    hφ.isOpen_preimage hbase hsubset hB
  have hEq : φ ⁻¹' B = {z : A × E |
      (z.1 : M) ∈ e.baseSet ∧
      metricNorm g (z.1 : M) (e.symmL ℝ (z.1 : M) z.2) < R} := by
    ext z
    constructor
    · intro hz
      change φ z ∈ B at hz
      refine ⟨hz.1, ?_⟩
      rw [e.symmL_apply (R := ℝ) hz.1]
      exact hz.2
    · intro hz
      change φ z ∈ B
      refine ⟨hz.1, ?_⟩
      change metricNorm g (z.1 : M) (e.symm (z.1 : M) z.2) < R
      rw [← e.symmL_apply (R := ℝ) hz.1]
      exact hz.2
  rw [← hEq]
  exact hopen


omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The paired frame metric tube is open. Intersect the source-frame metric
tube with the inverse image under f of the receiving frame's open base domain.
Source: paired tangent frames in HPS (1977), proof of Theorem 5.5, pp. 61–62. -/
theorem isOpen_fixed_paired_frame_metric_domain
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (f : M → M) (hf : Continuous f) (s t : M)
    {R : ℝ} :
    IsOpen {z : A × E |
      (z.1 : M) ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).baseSet ∧
      f (z.1 : M) ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) t).baseSet ∧
      metricNorm g (z.1 : M)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2) < R} := by
  let et := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
  have hs := isOpen_fixed_frame_metric_domain (E := E) (R := R) g A s
  have ht : IsOpen {z : A × E | f (z.1 : M) ∈ et.baseSet} := by
    exact et.open_baseSet.preimage
      (hf.comp (continuous_subtype_val.comp continuous_fst))
  have hset :
      {z : A × E |
        (z.1 : M) ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).baseSet ∧
        f (z.1 : M) ∈ et.baseSet ∧
        metricNorm g (z.1 : M)
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2) < R} =
      {z : A × E | (z.1 : M) ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).baseSet ∧
        metricNorm g (z.1 : M)
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2) < R} ∩
        {z : A × E | f (z.1 : M) ∈ et.baseSet} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [hset]
  exact hs.inter ht

end HolomorphicAnosov.ExponentialCutoff
