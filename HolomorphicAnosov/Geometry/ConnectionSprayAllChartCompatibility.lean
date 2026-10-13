import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Transition
import HolomorphicAnosov.Geometry.ConnectionTangentChartTransitionGerm
import HolomorphicAnosov.Geometry.ConnectionTangentChartSmooth

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A tangent vector with the canonical spray coordinate formula has that formula in every
admissible induced tangent chart. (Andrews, Ex. 8.11.3, p.84; Ex. 8.3.2, p.74) -/
theorem connectionSprayVector_allChartCoordinates [T2Space M] (nabla : SmoothAffineConnection E M)
    (z : TangentBundle 𝓘(ℝ, E) M) (W : TangentSpace (𝓘(ℝ, E)).tangent z)
    (hW : let c := chartAt E (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
      let hc := chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
        (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
      let v := (connectionTangentChart c z).2
      tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart c z)
        (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c) z W) =
          (v, -connectionChristoffelBilinear nabla (Module.finBasis ℝ E) c hc z.proj v v))
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c' : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc' : c' ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (hp' : (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c'.source) :
    let v := (connectionTangentChart c' z).2
    tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart c' z)
      (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c') z W) =
        (v, -connectionChristoffelBilinear nabla b c' hc' z.proj v v) := by
  let c := chartAt E (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  have hc := chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  have hp : (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M) ∈ c.source :=
    mem_chart_source E _
  let h := connectionChartMap c' ∘ connectionChartInverse c
  let H := fun q : E × E ↦ (h q.1, fderiv ℝ h q.1 q.2)
  have hh : ContDiffAt ℝ ∞ h (connectionChartMap c z.proj) := by
    have hinv := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hp)
    have hout := contMDiffAt_of_mem_maximalAtlas hc' hp'
    exact (hout.comp_of_eq hinv (c.left_inv hp)).contDiffAt
  have hfirst := hh.differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hsecond := (hh.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ H (connectionTangentChart c z) := by
    have hbase := hfirst.hasFDerivAt.comp (connectionTangentChart c z)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := connectionTangentChart c z))
    have hlinear := (hsecond.hasFDerivAt.comp (connectionTangentChart c z)
      (hasFDerivAt_fst (𝕜 := ℝ) (p := connectionTangentChart c z))).clm_apply
      (hasFDerivAt_snd (𝕜 := ℝ) (p := connectionTangentChart c z))
    exact (hbase.prodMk hlinear).differentiableAt
  have heq := connectionTangentChart_transition_eventuallyEq c c' hc hc' z hp hp'
  change connectionTangentChart c' =ᶠ[𝓝 z] (H ∘ connectionTangentChart c) at heq
  have hchain := mfderiv_comp_apply z
    (I := (𝓘(ℝ, E)).tangent) (I' := 𝓘(ℝ, E × E)) (I'' := 𝓘(ℝ, E × E))
    hH.mdifferentiableAt
    ((connectionTangentChart_chartAt_contMDiffAt z).mdifferentiableAt (by simp)) W
  rw [heq.symm.mfderiv_eq (I := (𝓘(ℝ, E)).tangent) (I' := 𝓘(ℝ, E × E))] at hchain
  rw [mfderiv_eq_fderiv] at hchain
  have hchainModel := congrArg (tangentSpaceCastModel 𝓘(ℝ, E × E)
    (H (connectionTangentChart c z))) hchain
  change tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart c' z)
      (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c') z W) =
      fderiv ℝ H (connectionTangentChart c z)
        (tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart c z)
          (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c) z W))
    at hchainModel
  rw [hchainModel]
  dsimp only at hW
  rw [hW]
  have hcov := connectionSpray_transition nabla (Module.finBasis ℝ E) b c c' hc hc'
    z.proj hp hp' (connectionTangentChart c z).2
  have hvelocity := congrArg Prod.snd (connectionTangentChart_transition c c' hc hc' z hp hp')
  dsimp only at hvelocity
  rw [hvelocity]
  exact hcov


end
end HolomorphicAnosov

