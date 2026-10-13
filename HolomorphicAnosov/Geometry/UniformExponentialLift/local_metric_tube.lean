import HolomorphicAnosov.Geometry.UniformExponentialLift.base

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialLift

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- An open neighborhood of a zero tangent vector contains a positive-radius metric tube over an
open neighborhood of its base point. (HPS, p. 62) -/
theorem local_metric_tube
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {Ω : Set (TangentBundle 𝓘(ℝ, E) M)} (hΩ : IsOpen Ω) (p : M)
    (hp : (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ Ω) :
    ∃ (U : Opens M) (ε : ℝ), p ∈ U ∧ 0 < ε ∧ normalTube g U ε ⊆ Ω := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  have hpe : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hs : ContinuousAt e.toOpenPartialHomeomorph.symm (p, (0 : E)) :=
    e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hpe)
  have he0 : e.toOpenPartialHomeomorph.symm (p, (0 : E)) =
      (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, E) M) := by
    rw [e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) p hpe]
    rw [map_zero]
  have hn : e.toOpenPartialHomeomorph.symm ⁻¹' Ω ∈ 𝓝 (p, (0 : E)) :=
    hs.preimage_mem_nhds (by simpa [he0] using hΩ.mem_nhds hp)
  obtain ⟨u, hu, w, hw, huw⟩ := mem_nhds_prod_iff.mp hn
  obtain ⟨δ, hδ, hwδ⟩ := Metric.mem_nhds_iff.mp hw
  obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt E
    (TangentSpace 𝓘(ℝ, E)) p
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hu (Filter.inter_mem (e.open_baseSet.mem_nhds hpe) hbound))
  refine ⟨⟨U, hUopen⟩, δ / C, hpU, div_pos hδ hC, ?_⟩
  intro z hz
  have hzU := hUsub hz.1
  have hzbase := hzU.2.1
  have hznorm : ‖z.snd‖ = metricNorm g z.proj z.snd := rfl
  have hcoord : ‖e.continuousLinearMapAt ℝ z.proj z.snd‖ < δ := by
    calc
      _ ≤ ‖e.continuousLinearMapAt ℝ z.proj‖ * ‖z.snd‖ :=
        (e.continuousLinearMapAt ℝ z.proj).le_opNorm z.snd
      _ ≤ C * ‖z.snd‖ := mul_le_mul_of_nonneg_right hzU.2.2.le (norm_nonneg _)
      _ < δ := by rw [hznorm]; exact (lt_div_iff₀' hC).mp hz.2
  have hin := huw (a := (z.proj, e.continuousLinearMapAt ℝ z.proj z.snd))
    ⟨hzU.1, hwδ (by simpa using hcoord)⟩
  have hez : (z.proj, e.continuousLinearMapAt ℝ z.proj z.snd) = e z := by
    apply Prod.ext
    · exact (e.coe_fst hzbase).symm
    · simp [Trivialization.continuousLinearMapAt_apply,
        Trivialization.linearMapAt_apply, hzbase]
  rw [hez] at hin
  change e.toOpenPartialHomeomorph.symm (e.toOpenPartialHomeomorph z) ∈ Ω at hin
  rwa [e.toOpenPartialHomeomorph.left_inv (e.mem_source.mpr hzbase)] at hin


end ExponentialLift
end HolomorphicAnosov
