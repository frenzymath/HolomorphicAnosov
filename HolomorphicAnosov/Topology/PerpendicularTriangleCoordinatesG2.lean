import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace HolomorphicAnosov

/-- Nonzero perpendicular complex vectors give real affine plane coordinates.
The linear map (u,v) ↦ u e+v p is injective: take its two real dot products
with e and p and divide by their positive squared lengths. Equal finite real
dimensions make it bijective, and finite-dimensional continuity provides the
continuous affine equivalence after translation by the apex. This is the
coordinate construction in Cairns (1951), §3 Case II, p.863. -/
theorem perpendicular_triangle_coordinates_g2 (M e p : ℂ) (he : e ≠ 0) (hp : p ≠ 0)
    (hep : e.re*p.re+e.im*p.im=0) :
    ∃ F : (ℝ × ℝ) ≃ᴬ[ℝ] ℂ, ∀ x : ℝ × ℝ, F x = M + x.1 • e + x.2 • p := by
  let L : (ℝ × ℝ) →ₗ[ℝ] ℂ :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight e + (LinearMap.snd ℝ ℝ ℝ).smulRight p
  have hnorm (z : ℂ) (hz : z ≠ 0) : 0 < z.re^2+z.im^2 := by
    have h : z.re ≠ 0 ∨ z.im ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hz (Complex.ext hn.1 hn.2)
    rcases h with h | h <;> nlinarith [sq_pos_of_ne_zero h]
  have hL : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hxre : x.1*e.re+x.2*p.re=0 := by simpa [L] using congrArg Complex.re hx
    have hxim : x.1*e.im+x.2*p.im=0 := by simpa [L] using congrArg Complex.im hx
    have hx1 : x.1*(e.re^2+e.im^2)=0 := by
      linear_combination e.re*hxre+e.im*hxim-x.2*hep
    have hx2 : x.2*(p.re^2+p.im^2)=0 := by
      linear_combination p.re*hxre+p.im*hxim-x.1*hep
    exact Prod.ext ((mul_eq_zero.mp hx1).resolve_right (hnorm e he).ne')
      ((mul_eq_zero.mp hx2).resolve_right (hnorm p hp).ne')
  let E := (L.linearEquivOfInjective hL (by simp)).toContinuousLinearEquiv
  refine ⟨E.toContinuousAffineEquiv.trans (ContinuousAffineEquiv.vaddConst ℝ M), ?_⟩
  intro x
  change x.1 • e+x.2 • p+M=M+x.1 • e+x.2 • p
  abel

end HolomorphicAnosov
