import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.LinearCombination

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- The local Koszul identity follows from the actual torsion and compatibility laws. Source: Andrews, Lecture10, Proposition10.3.1, p.97. -/
theorem SmoothAffineConnection.koszul_of_torsionFree_metricCompatible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (nabla : SmoothAffineConnection E M) (ht : nabla.IsTorsionFree)
    (hg : nabla.IsMetricCompatible g)
    (U : Opens M) (X Y Z : LocalSmoothVectorField E M U) (p : U) :
    let B := fun (v w : TangentSpace 𝓘(ℝ, E) p) ↦
      let dι := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p
      g.inner p.1 (dι v) (dι w)
    2 * B (nabla.cov U X Y p) (Z p) =
      mvfderiv 𝓘(ℝ, E) (fun q : U ↦
        let dι := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q
        g.inner q.1 (dι (Y q)) (dι (Z q))) p (X p) +
      mvfderiv 𝓘(ℝ, E) (fun q : U ↦
        let dι := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q
        g.inner q.1 (dι (Z q)) (dι (X q))) p (Y p) -
      mvfderiv 𝓘(ℝ, E) (fun q : U ↦
        let dι := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun r : U ↦ (r : M)) q
        g.inner q.1 (dι (X q)) (dι (Y q))) p (Z p) +
      B (Z p) (VectorField.mlieBracket 𝓘(ℝ, E) X Y p) +
      B (Y p) (VectorField.mlieBracket 𝓘(ℝ, E) Z X p) +
      B (X p) (VectorField.mlieBracket 𝓘(ℝ, E) Z Y p) := by
  dsimp only
  have h1 := hg U X Y Z p
  have h2 := hg U Y Z X p
  have h3 := hg U Z X Y p
  rw [← ht U X Y p, ← ht U Z X p, ← ht U Z Y p]
  simp only [map_sub] at *
  rw [g.symm p.1 _ _] at h2
  rw [g.symm p.1 _ _] at h3
  have hsym := g.symm p.1
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p (nabla.cov U X Y p))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun q : U ↦ (q : M)) p (Z p))
  rw [hsym] at h1 ⊢
  linear_combination -h1 - h2 + h3


end
end HolomorphicAnosov
