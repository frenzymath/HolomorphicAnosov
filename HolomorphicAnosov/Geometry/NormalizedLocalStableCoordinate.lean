import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! This file defines the restricted transverse differential and the normalized local stable
coordinate. (Zhang, Eq. (14), p. 7, and Lemma 2.5, p. 8) -/

open scoped Manifold ContDiff

namespace HolomorphicAnosov

noncomputable section

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]

/-- The scalar complex differential of the transverse function `t`, restricted to the stable tangent
fibre at `x`. (Zhang, Eq. (14), p. 7) -/
def localStableCoordinateDerivative
    (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (t : X → ℂ) (x : X) : S x →L[ℂ] ℂ :=
  ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t x)).toContinuousLinearMap.comp
    (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t x)).comp (S x).subtypeL

/-- The normalized stable coordinate obtained by applying the inverse restricted transverse
differential at `x` to `t p - t x`. The inverse is zero when the restricted differential is not
invertible. (Zhang, Eq. (14), p. 7, and Lemmas 2.4–2.5) -/
def normalizedLocalStableCoordinate
    (S : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (t : X → ℂ) (x p : X) : S x :=
  (localStableCoordinateDerivative S t x).inverse (t p - t x)

end

end HolomorphicAnosov
