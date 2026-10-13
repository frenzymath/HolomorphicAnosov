import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
A derivative of a curve in a real normed vector space gives its manifold derivative in the
identity model.
-/

open scoped Manifold

namespace HolomorphicAnosov

/-- A curve with derivative `v` at zero has manifold derivative `t ↦ t • v` in the identity model. -/
theorem euclidean_orbit_mfderiv_g1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ → E) (v : E) (h : HasDerivAt c v 0) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) c 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  exact h.hasFDerivAt.hasMFDerivAt

end HolomorphicAnosov

