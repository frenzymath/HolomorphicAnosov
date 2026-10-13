import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.MaximalAtlasRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ChartSource
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Coefficients
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ExtendedCoefficients
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.CoefficientRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Representation
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
/-- The selected coefficients agree with any representation on a smaller chart domain. (Andrews, §8.3) -/
theorem extendedLocalChristoffel_eq_restricted (nabla : SmoothAffineConnection E M)
    {n : ℕ} (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (U : Opens M) (hU : Nonempty U)
    (hUc : U ≤ chartSource c) (ΓU : Fin n → Fin n → Fin n → U → ℝ)
    (hΓU : RepresentsCoefficients nabla U b (c.subtypeRestr hU) ΓU)
    (i j k : Fin n) (p : U) : extendedLocalChristoffel nabla b c hc i j k p = ΓU i j k p := by
  have hV : Nonempty (chartSource c) := ⟨Opens.inclusion hUc p⟩
  have hΓV : RepresentsCoefficients nabla (chartSource c) b (c.subtypeRestr hV)
      (localChristoffel nabla b c hc hV) :=
    (Classical.choose_spec
      (((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2
        (chartSource c) n b (c.subtypeRestr hV)
        (HolomorphicAnosov.maximalAtlas_subtypeRestr c hc (chartSource c) hV))).2
  have hres := christoffel_coefficients_restrict nabla hUc hU hV c hc
    (fun _ hp ↦ hp) b (localChristoffel nabla b c hc hV) ΓU hΓV hΓU i j k p
  unfold extendedLocalChristoffel
  split
  · exact hres
  · rename_i hn
    exact (hn (hUc p.property)).elim

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
