import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Chart coordinate functions commute with smooth scalar multiplication. Source: Andrews, Lecture 8, §8.3, p.74; linearity of the chart derivative and basis representation. -/
theorem LocalSmoothVectorField.coordinateCoefficient_mulFunction
    {U : Opens M} {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph U E) (X : LocalSmoothVectorField E M U)
    (f : U → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (k : Fin n) (z : E) :
    (X.mulFunction f hf).coordinateCoefficient b c k z =
      f (c.symm z) * X.coordinateCoefficient b c k z := by
  simp [LocalSmoothVectorField.coordinateCoefficient,
    LocalSmoothVectorField.tangentCoefficient,
    LocalSmoothVectorField.mulFunction, map_smul]


end

end HolomorphicAnosov

