import Mathlib.Tactic.Ring
import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChristoffelSymmetric

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The Christoffel bilinear expression of the Levi-Civita connection is symmetric in its two model
vectors. (Gallier–Quaintance, Prop. 16.7) -/
theorem gauss_connectionChristoffelBilinear_symmetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : M) (hp : (⟨p, mem_univ p⟩ : ConnectionWhole M) ∈ c.source) (u v : E) :
    connectionChristoffelBilinear (E := E) (riemannianConnection g) b c hc p u v =
      connectionChristoffelBilinear (E := E) (riemannianConnection g) b c hc p v u := by
  classical
  unfold connectionChristoffelBilinear
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [gauss_connectionChristoffel_symmetric g b c hc _ hp i j k]
  ring

end HolomorphicAnosov

