import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

/-- The continuous linear map sending a coordinate vector `v` to `∑ i, v i • H i`.
(Bochner–Montgomery, eq. (27), p. 692) -/
noncomputable def partialDerivativeMap
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : Fin n → F) : (Fin n → ℝ) →L[ℝ] F :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (H i)


end HolomorphicAnosov.Paper.Zhang
