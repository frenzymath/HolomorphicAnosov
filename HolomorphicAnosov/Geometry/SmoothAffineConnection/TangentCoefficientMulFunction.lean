import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Tangent coordinates commute with smooth scalar multiplication. Source: Andrews, Lecture 8, §8.3, p.74; linearity of the chart derivative and basis representation. -/
theorem LocalSmoothVectorField.tangentCoefficient_mulFunction
    {U : Opens M} {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph U E) (X : LocalSmoothVectorField E M U)
    (f : U → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (p : U) (k : Fin n) :
    (X.mulFunction f hf).tangentCoefficient b c p k =
      f p * X.tangentCoefficient b c p k := by
  simp [LocalSmoothVectorField.tangentCoefficient,
    LocalSmoothVectorField.mulFunction, map_smul]


end

end HolomorphicAnosov

