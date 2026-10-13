import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic

/-!
# Reconstruction of a smooth field from its coordinate components


-/ 

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- A vector field is reconstructed by its chart coefficients and the inverse-derivative coordinate frame. Source: Andrews, Lecture 8, proof of Proposition 8.3.1, p.74. -/
theorem LocalSmoothVectorField.coordinate_frame_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {U : Opens M} {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph U E)
    (hc : c.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E))
    (X : LocalSmoothVectorField E M U) (p : U) (hp : p ∈ c.source)
    (W : Fin n → TangentSpace 𝓘(ℝ, E) p)
    (hW : ∀ i, mvfderiv 𝓘(ℝ, E) c p (W i) = b i) :
    X p = ∑ i, X.tangentCoefficient b c p i • W i := by
  apply hc.mfderiv_injective hp
  change mvfderiv 𝓘(ℝ, E) c p (X p) =
    mvfderiv 𝓘(ℝ, E) c p (∑ i, X.tangentCoefficient b c p i • W i)
  simp only [map_sum, map_smul, hW, LocalSmoothVectorField.tangentCoefficient]
  exact (b.sum_repr _).symm

end
end HolomorphicAnosov

