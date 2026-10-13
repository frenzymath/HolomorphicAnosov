import HolomorphicAnosov.Geometry.ConnectionChartTransitionGerm
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChartMapSmooth

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Induced tangent coordinates transform by `(x, v) ↦ (h(x), Dh(x)v)` on a chart overlap. (Lee,
Lemma 4.1, pp.81–82; Gallier–Quaintance, §10.1, p.291) -/
theorem connectionTangentChart_transition
    (c c' : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (hc' : c' ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (z : TangentBundle 𝓘(ℝ, E) M)
    (hp : (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c.source)
    (hp' : (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c'.source) :
    let h := connectionChartMap c' ∘ connectionChartInverse c
    connectionTangentChart c' z =
      (h (connectionTangentChart c z).1,
        fderiv ℝ h (connectionTangentChart c z).1 (connectionTangentChart c z).2) := by
  let h := connectionChartMap c' ∘ connectionChartInverse c
  have hh : ContDiffAt ℝ ∞ h (connectionChartMap c z.proj) := by
    have hinv := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hp)
    have hout := contMDiffAt_of_mem_maximalAtlas hc' hp'
    exact (hout.comp_of_eq hinv (c.left_inv hp)).contDiffAt
  have heq := connectionChart_transition_eventuallyEq c c' z.proj hp
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
  have hchain := mfderiv_comp_apply z.proj
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    (hh.contMDiffAt.mdifferentiableAt (by simp))
    ((gauss_connectionChartMap_smooth c hc z.proj hp).mdifferentiableAt (by simp)) z.snd
  dsimp only [connectionTangentChart]
  apply Prod.ext
  · exact (congrArg (connectionChartMap c') (congrArg Subtype.val (c.left_inv hp))).symm
  · dsimp only
    rw [hd] at hchain
    rw [mfderiv_eq_fderiv] at hchain
    have hhchain := congrArg (tangentSpaceCastModel 𝓘(ℝ, E)
      (h (connectionChartMap c z.proj))) hchain
    exact hhchain

end
end HolomorphicAnosov
