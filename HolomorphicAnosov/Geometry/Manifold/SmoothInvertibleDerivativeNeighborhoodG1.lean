import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open scoped Topology _root_.Topology ContDiff
open Set Filter
noncomputable section
namespace HolomorphicAnosov

/-- A smooth map whose derivative at x is an equivalence has an open neighborhood of x on which its derivatives form a smooth family of equivalences (Montgomery, Lemma 2, pp.688–689). -/
theorem smooth_invertible_derivative_neighborhood_g1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (S : Set E) (hS : IsOpen S) (x : E) (hx : x ∈ S)
    (hf : ContDiffOn ℝ ∞ f S) (B : E ≃L[ℝ] E)
    (hB : HasFDerivAt f B.toContinuousLinearMap x) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧
      ∃ C : E → E ≃L[ℝ] E,
        ContDiffOn ℝ ∞ (fun y ↦ (C y).toContinuousLinearMap) U ∧
        ∀ y ∈ U, HasFDerivAt f (C y).toContinuousLinearMap y := by
  classical
  have hfx : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hS.mem_nhds hx)
  have hi : (fderiv ℝ f x).IsInvertible := by
    rw [hB.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  have hev : ∀ᶠ y in 𝓝 x, (fderiv ℝ f y).IsInvertible :=
    (hfx.continuousAt_fderiv (by simp)).eventually hi.eventually_nhds
  obtain ⟨U, hU, ho, hxU⟩ := mem_nhds_iff.mp (inter_mem (hS.mem_nhds hx) hev)
  let C : E → E ≃L[ℝ] E := fun y ↦
    if hy : y ∈ U then Classical.choose (hU hy).2 else ContinuousLinearEquiv.refl ℝ E
  have hC : ∀ y ∈ U, (C y).toContinuousLinearMap = fderiv ℝ f y := by
    intro y hy
    simpa only [C, dite_eq_left hy] using Classical.choose_spec (hU hy).2
  refine ⟨U, ho, hxU, fun y hy ↦ (hU hy).1, C, ?_, ?_⟩
  · have hs : ContDiffOn ℝ ∞ (fderiv ℝ f) U := by
      intro y hy
      exact ((hf.contDiffAt (hS.mem_nhds (hU hy).1)).fderiv_right (by simp)).contDiffWithinAt
    exact hs.congr hC
  · intro y hy
    rw [hC y hy]
    exact (hf.contDiffAt (hS.mem_nhds (hU hy).1)).differentiableAt (by simp) |>.hasFDerivAt

end HolomorphicAnosov
