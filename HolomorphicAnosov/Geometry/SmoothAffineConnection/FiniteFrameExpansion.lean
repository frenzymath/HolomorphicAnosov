import HolomorphicAnosov.Geometry.SmoothAffineConnection.Basic

/-!
# Covariant differentiation of finite smooth frame expansions


-/ 

open Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

/-- Expanding two fields as finite smooth linear combinations gives the Christoffel term and the derivative-of-coefficients term before choosing coordinates. Source: Andrews, Lecture 8, Proposition 8.3.1, p.74. -/
theorem covariantDerivative_finite_frame_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (cov : LocalBilinearCovariantDerivative E M) (hcov : IsSmoothAffineConnectionOperator cov)
    {U : Opens M} {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (X : ι → LocalSmoothVectorField E M U) (Y : κ → LocalSmoothVectorField E M U)
    (f : ι → U → ℝ) (g : κ → U → ℝ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f i))
    (hg : ∀ j, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (g j)) (p : U) :
    cov U (∑ i ∈ s, (X i).mulFunction (f i) (hf i))
      (∑ j ∈ t, (Y j).mulFunction (g j) (hg j)) p =
      (∑ i ∈ s, ∑ j ∈ t, (f i p * g j p) • cov U (X i) (Y j) p) +
      ∑ i ∈ s, ∑ j ∈ t,
        (f i p * mvfderiv 𝓘(ℝ, E) (g j) p (X i p)) • Y j p := by
  classical
  have hs (u : Finset ι) (Z : ι → LocalSmoothVectorField E M U) :
      (∑ a ∈ u, Z a) p = ∑ a ∈ u, Z a p := by
    induction u using Finset.induction_on with
    | empty => rfl
    | @insert a u ha ih =>
      simp only [Finset.sum_insert ha, ContMDiffSection.coe_add, Pi.add_apply, ih]
  have ht (u : Finset κ) (Z : κ → LocalSmoothVectorField E M U) :
      (∑ a ∈ u, Z a) p = ∑ a ∈ u, Z a p := by
    induction u using Finset.induction_on with
    | empty => rfl
    | @insert a u ha ih =>
      simp only [Finset.sum_insert ha, ContMDiffSection.coe_add, Pi.add_apply, ih]
  have hsingle (i : ι) (j : κ) :
      cov U ((X i).mulFunction (f i) (hf i)) ((Y j).mulFunction (g j) (hg j)) p =
        (f i p * g j p) • cov U (X i) (Y j) p +
        (f i p * mvfderiv 𝓘(ℝ, E) (g j) p (X i p)) • Y j p := by
    rw [hcov.function_linear]
    change f i p • cov U (X i) ((Y j).mulFunction (g j) (hg j)) p = _
    rw [hcov.leibniz]
    simp only [smul_add, smul_smul]
  simp only [map_sum, LinearMap.sum_apply]
  simp_rw [ht, hs, hsingle]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]


end
end HolomorphicAnosov
