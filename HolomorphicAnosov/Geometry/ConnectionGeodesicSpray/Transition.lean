import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.SelectedTransition
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic
import HolomorphicAnosov.Geometry.TangentTransitionDerivative
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChart
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChartAtlas

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- On a chart overlap, the Christoffel bilinear expressions satisfy `Γ̃(Dh u, Dh v) = Dh Γ(u, v) -
D²h(u, v)`. (Andrews, Ex. 8.3.2, p.74) -/
theorem connectionChristoffel_transition (nabla : SmoothAffineConnection E M)
    {n m : ℕ} (b : Basis (Fin n) ℝ E) (d : Basis (Fin m) ℝ E)
    (c c' : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (hc' : c' ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : M) (hp : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c.source)
    (hp' : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c'.source) (u v : E) :
    let h := connectionChartMap c' ∘ connectionChartInverse c
    let x := connectionChartMap c p
    connectionChristoffelBilinear nabla d c' hc' p
        (fderiv ℝ h x u) (fderiv ℝ h x v) =
      fderiv ℝ h x (connectionChristoffelBilinear nabla b c hc p u v) -
        fderiv ℝ (fun y ↦ fderiv ℝ h y) x u v := by
  have hpc : p ∈ (ConnectionChristoffelLocal.wholeChart c).source := ⟨mem_univ _, hp⟩
  have hpc' : p ∈ (ConnectionChristoffelLocal.wholeChart c').source := ⟨mem_univ _, hp'⟩
  exact ConnectionChristoffelLocal.localCoefficientBilinear_transition nabla b d
    (ConnectionChristoffelLocal.wholeChart c) (ConnectionChristoffelLocal.wholeChart c')
    (ConnectionChristoffelLocal.wholeChart_mem_maximalAtlas c hc)
    (ConnectionChristoffelLocal.wholeChart_mem_maximalAtlas c' hc') p hpc hpc' u v

/-- The derivative of the induced tangent transition carries the spray vector `(v, -Γ(v, v))` to its
expression in the new chart. (Andrews, Ex. 8.3.2, p.74; Ex. 8.11.3, p.84) -/
theorem connectionSpray_transition (nabla : SmoothAffineConnection E M)
    {n m : ℕ} (b : Basis (Fin n) ℝ E) (d : Basis (Fin m) ℝ E)
    (c c' : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (hc' : c' ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : M) (hp : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c.source)
    (hp' : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c'.source) (v : E) :
    let h := connectionChartMap c' ∘ connectionChartInverse c
    let x := connectionChartMap c p
    fderiv ℝ (fun z : E × E ↦ (h z.1, fderiv ℝ h z.1 z.2)) (x, v)
        (v, -connectionChristoffelBilinear nabla b c hc p v v) =
      (fderiv ℝ h x v,
        -connectionChristoffelBilinear nabla d c' hc' p
          (fderiv ℝ h x v) (fderiv ℝ h x v)) := by
  have hsmooth : ContDiffAt ℝ ∞ (connectionChartMap c' ∘ connectionChartInverse c)
      (connectionChartMap c p) := by
    have hinv := contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hp)
    have hout := contMDiffAt_of_mem_maximalAtlas hc' hp'
    exact (hout.comp_of_eq hinv (c.left_inv hp)).contDiffAt
  have hfirst : DifferentiableAt ℝ (connectionChartMap c' ∘ connectionChartInverse c)
      (connectionChartMap c p) := hsmooth.differentiableAt (by simp)
  have hsecond : DifferentiableAt ℝ
      (fderiv ℝ (connectionChartMap c' ∘ connectionChartInverse c))
      (connectionChartMap c p) :=
    (hsmooth.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  exact tangentTransition_spray_covariance hfirst hsecond
    (connectionChristoffelBilinear nabla b c hc p)
    (connectionChristoffelBilinear nabla d c' hc' p) v
    (connectionChristoffel_transition nabla b d c c' hc hc' p hp hp' v v)

end
end HolomorphicAnosov

