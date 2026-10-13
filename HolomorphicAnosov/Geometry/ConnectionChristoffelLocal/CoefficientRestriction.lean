import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.MaximalAtlasRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.FullSourceFrame
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.RestrictField
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.RestrictFieldLaw
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.CoordinateRestriction
import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
/-- Coordinate representations on nested domains agree on the smaller domain. (Andrews, Prop. 8.3.1) -/
theorem christoffel_coefficients_restrict (nabla : SmoothAffineConnection E M)
    {U V : Opens M} (hUV : U ≤ V) (hU : Nonempty U) (hV : Nonempty V)
    (c : OpenPartialHomeomorph M E) (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hVc : (V : Set M) ⊆ c.source) {n : ℕ} (b : Basis (Fin n) ℝ E)
    (ΓV : Fin n → Fin n → Fin n → V → ℝ)
    (ΓU : Fin n → Fin n → Fin n → U → ℝ)
    (hΓV : ∀ (X Y : LocalSmoothVectorField E M V) (p : V),
      p ∈ (c.subtypeRestr hV).source → ∀ k,
      (nabla.cov V X Y).tangentCoefficient b (c.subtypeRestr hV) p k =
        (∑ i, X.tangentCoefficient b (c.subtypeRestr hV) p i *
          fderiv ℝ (Y.coordinateCoefficient b (c.subtypeRestr hV) k)
            (c.subtypeRestr hV p) (b i)) +
        ∑ i, ∑ j, X.tangentCoefficient b (c.subtypeRestr hV) p i *
          Y.tangentCoefficient b (c.subtypeRestr hV) p j * ΓV i j k p)
    (hΓU : ∀ (X Y : LocalSmoothVectorField E M U) (p : U),
      p ∈ (c.subtypeRestr hU).source → ∀ k,
      (nabla.cov U X Y).tangentCoefficient b (c.subtypeRestr hU) p k =
        (∑ i, X.tangentCoefficient b (c.subtypeRestr hU) p i *
          fderiv ℝ (Y.coordinateCoefficient b (c.subtypeRestr hU) k)
            (c.subtypeRestr hU p) (b i)) +
        ∑ i, ∑ j, X.tangentCoefficient b (c.subtypeRestr hU) p i *
          Y.tangentCoefficient b (c.subtypeRestr hU) p j * ΓU i j k p)
    (i j k : Fin n) (p : U) : ΓV i j k (Opens.inclusion hUV p) = ΓU i j k p := by
  have hfull : (c.subtypeRestr hV).source = univ := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    ext q
    exact iff_of_true (hVc q.property) (mem_univ q)
  obtain ⟨X, hX⟩ := HolomorphicAnosov.exists_coordinate_frame_of_source_eq_univ
    (c.subtypeRestr hV) (HolomorphicAnosov.maximalAtlas_subtypeRestr c hc V hV) hfull (b i)
  obtain ⟨Y, hY⟩ := HolomorphicAnosov.exists_coordinate_frame_of_source_eq_univ
    (c.subtypeRestr hV) (HolomorphicAnosov.maximalAtlas_subtypeRestr c hc V hV) hfull (b j)
  have hXU (q : U) : mvfderiv 𝓘(ℝ, E) (c.subtypeRestr hU) q
      (restrictField hUV X q) = b i :=
    (chartVector_isRestriction hUV hU hV c hc X (restrictField hUV X)
      (restrictField_isRestriction hUV X) q (hVc (hUV q.property))).trans
      (hX (Opens.inclusion hUV q))
  have hYU (q : U) : mvfderiv 𝓘(ℝ, E) (c.subtypeRestr hU) q
      (restrictField hUV Y q) = b j :=
    (chartVector_isRestriction hUV hU hV c hc Y (restrictField hUV Y)
      (restrictField_isRestriction hUV Y) q (hVc (hUV q.property))).trans
      (hY (Opens.inclusion hUV q))
  have hpU : p ∈ (c.subtypeRestr hU).source := by
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hVc (hUV p.property)
  have hpV : Opens.inclusion hUV p ∈ (c.subtypeRestr hV).source := by rw [hfull]; trivial
  have hlarge := HolomorphicAnosov.christoffel_coefficient_of_coordinate_germs nabla.cov V b
    (c.subtypeRestr hV) ΓV hΓV (Opens.inclusion hUV p) hpV i j k X Y
    (Filter.Eventually.of_forall hX) (Filter.Eventually.of_forall hY)
  have hsmall := HolomorphicAnosov.christoffel_coefficient_of_coordinate_germs nabla.cov U b
    (c.subtypeRestr hU) ΓU hΓU p hpU i j k (restrictField hUV X) (restrictField hUV Y)
    (Filter.Eventually.of_forall hXU) (Filter.Eventually.of_forall hYU)
  have htransport := chartVector_isRestriction hUV hU hV c hc
    (nabla.cov V X Y) (nabla.cov U (restrictField hUV X) (restrictField hUV Y))
    (nabla.laws.restriction hUV X Y (restrictField hUV X) (restrictField hUV Y)
      (restrictField_isRestriction hUV X) (restrictField_isRestriction hUV Y)) p (hVc (hUV p.property))
  have hcoeff := congrArg (fun z ↦ b.repr z k) htransport
  exact hlarge.symm.trans (hcoeff.symm.trans hsmall)

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
