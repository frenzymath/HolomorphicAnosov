import Mathlib.Geometry.Manifold.Immersion

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- Precomposing an immersed inclusion by a diffeomorphism preserves its actual immersion charts. -/
theorem immersion_precompose_diffeomorph_g15 {r : ℕ}
    {L N : Type*} [TopologicalSpace L] [TopologicalSpace N]
    [ChartedSpace (Fin r → ℝ) L] [ChartedSpace (Fin r → ℝ) N]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (ι : L → M) (e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) N L ∞)
    (x : N) (h : Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) I ∞ ι (e x)) :
    Manifold.IsImmersionAt 𝓘(ℝ, Fin r → ℝ) I ∞ (ι ∘ e) x := by
  have hc := h.isImmersionAtOfComplement_complement
  have hdom : e.toHomeomorph.transOpenPartialHomeomorph hc.domChart ∈
      IsManifold.maximalAtlas 𝓘(ℝ, Fin r → ℝ) ∞ N := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas).comp
        e.contMDiff.contMDiffOn (fun z hz ↦ hz)
    · exact e.symm.contMDiff.comp_contMDiffOn
        (contMDiffOn_symm_of_mem_maximalAtlas hc.domChart_mem_maximalAtlas)
  refine ⟨h.complement, inferInstance, inferInstance, ?_⟩
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (hc.continuousAt.comp e.contMDiff.continuous.continuousAt) hc.equiv
    (e.toHomeomorph.transOpenPartialHomeomorph hc.domChart) hc.codChart
    (by simpa using hc.mem_domChart_source) hc.mem_codChart_source hdom
    hc.codChart_mem_maximalAtlas
  intro y hy
  simpa [OpenPartialHomeomorph.extend, Function.comp_def] using hc.writtenInCharts hy


end HolomorphicAnosov
