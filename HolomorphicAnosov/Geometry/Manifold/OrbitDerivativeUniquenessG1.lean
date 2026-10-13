import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
The manifold derivative of a real curve at zero is unique.
-/

open scoped Manifold

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]

theorem orbit_mfderiv_unique_g1
    (γ : ℝ → M) (_x : M)
    (L L' : TangentSpace 𝓘(ℝ, ℝ) 0 →L[ℝ] TangentSpace 𝓘(ℝ, E) (γ 0))
    (hL : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0 L)
    (hL' : HasMFDerivAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ 0 L') :
    L = L' := by
  rw [← hL.mfderiv, ← hL'.mfderiv]

end HolomorphicAnosov

