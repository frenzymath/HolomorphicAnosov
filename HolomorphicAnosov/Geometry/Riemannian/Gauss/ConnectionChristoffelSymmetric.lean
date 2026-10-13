import HolomorphicAnosov.Geometry.Riemannian.Gauss.ConnectionChristoffelMetricFormula

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- The Christoffel coefficients of the Levi-Civita connection are symmetric in their first two
indices. (Gallier–Quaintance, Prop. 16.7) -/
theorem gauss_connectionChristoffel_symmetric
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (p : ConnectionWhole M) (hp : p ∈ c.source) (i j k : Fin n) :
    connectionChristoffel (riemannianConnection g) b c hc i j k p =
      connectionChristoffel (riemannianConnection g) b c hc j i k p := by
  rw [gauss_connectionChristoffel_metric_formula g b c hc p hp i j k,
    gauss_connectionChristoffel_metric_formula g b c hc p hp j i k]
  have hsym : (fun z ↦ g.inner (c.symm z : M)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ (c.symm z : M)) z (b i))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ (c.symm z : M)) z (b j))) =
      (fun z ↦ g.inner (c.symm z : M)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ (c.symm z : M)) z (b j))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z ↦ (c.symm z : M)) z (b i))) :=
    funext fun z ↦ g.symm _ _ _
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [hsym]
  congr 2
  exact add_comm _ _

end HolomorphicAnosov

