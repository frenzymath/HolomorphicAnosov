import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.Module

/-!
This file studies closed parameter sets defined by uniform directional derivative bounds (Montgomery, 1945).
-/ 

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Regularity

/-- A uniform directional derivative bound on an open convex spatial domain defines a closed set of parameters. (Montgomery, 1945) -/
theorem montgomery_isClosed_derivative_bound
    {P E : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (hUc : Convex ℝ U) (e : E)
    (F H : P → E → ℝ)
    (hF : ∀ y ∈ U, Continuous (fun v ↦ F v y))
    (hderiv : ∀ v y, y ∈ U → HasDerivAt (fun t : ℝ ↦ F v (y + t • e)) (H v y) 0)
    (c C : ℝ) (hC : 0 ≤ C) :
    IsClosed {v | ∀ y ∈ U, ‖H v y - c‖ ≤ C} := by
  let A : Set P := {v | ∀ y ∈ U, ‖H v y - c‖ ≤ C}
  apply closure_subset_iff_isClosed.mp
  intro v hv y hy
  have hinc (t : ℝ) (ht : y + t • e ∈ U) :
      ‖F v (y + t • e) - t * c - F v y‖ ≤ C * ‖t‖ := by
    have hc : IsClosed {w : P | ‖F w (y + t • e) - t * c - F w y‖ ≤ C * ‖t‖} :=
      isClosed_le (((hF _ ht).sub continuous_const).sub (hF _ hy)).norm continuous_const
    apply closure_minimal (s := A) ?_ hc hv
    intro w hw
    let S : Set ℝ := {s | y + s • e ∈ U}
    have hS : Convex ℝ S := by
      intro x hx z hz a b ha hb hab
      have h := hUc hx hz ha hb hab
      change y + (a • x + b • z) • e ∈ U
      have hb' : b = 1 - a := by linarith
      rw [hb'] at h ⊢
      convert h using 1; module
    have hd (s : ℝ) (hs : s ∈ S) :
        HasDerivAt (fun t : ℝ ↦ F w (y + t • e) - t * c)
          (H w (y + s • e) - c) s := by
      have h := (hderiv w (y + s • e) hs)
      have h' : HasDerivAt (fun t : ℝ ↦ F w ((y + s • e) + (t - s) • e))
          (H w (y + s • e)) s := by
        exact HasDerivAt.comp_sub_const s s (by simpa using h)
      have heq : (fun t : ℝ ↦ F w ((y + s • e) + (t - s) • e)) =
          (fun t : ℝ ↦ F w (y + t • e)) := by
        funext t
        congr 1
        module
      rw [heq] at h'
      convert h'.sub ((hasDerivAt_id s).mul_const c) using 1 <;> simp; rfl
    have hm := hS.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs ↦ (hd s hs).hasDerivWithinAt) (fun s hs ↦ hw _ hs)
      (x := 0) (y := t) (by simpa [S] using hy) ht
    simpa using hm
  have hd : HasDerivAt (fun t : ℝ ↦ F v (y + t • e) - t * c)
      (H v y - c) 0 := by
    convert (hderiv v y hy).sub ((hasDerivAt_id (0 : ℝ)).mul_const c) using 1 <;> simp; rfl
  have hn : ∀ᶠ t : ℝ in 𝓝 0, y + t • e ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      (hU.mem_nhds (by simpa using hy))
  have hl := norm_deriv_le_of_lip' (f := fun t : ℝ ↦ F v (y + t • e) - t * c)
    hC (hn.mono fun t ht ↦ by simpa using hinc t ht)
  simpa [hd.deriv] using hl

end HolomorphicAnosov.Analysis.Regularity

