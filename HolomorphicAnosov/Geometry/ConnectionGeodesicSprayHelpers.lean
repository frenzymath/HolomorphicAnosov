import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Scaling both inputs of the Christoffel bilinear expression by `a` scales its value by `a²`. -/
theorem connectionChristoffelBilinear_smul_smul
    (nabla : SmoothAffineConnection E M) {n : ℕ}
    (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : M) (a : ℝ) (u v : E) :
    connectionChristoffelBilinear nabla b c hc p (a • u) (a • v) =
      (a * a) • connectionChristoffelBilinear nabla b c hc p u v := by
  simp only [connectionChristoffelBilinear, map_smul, Finsupp.smul_apply,
    smul_eq_mul, Finset.smul_sum, smul_smul]
  congr 1
  funext k
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end HolomorphicAnosov

