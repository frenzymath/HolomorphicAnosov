import HolomorphicAnosov.Geometry.Manifold.CompactParameterIntegralDerivative
import Mathlib.Analysis.Calculus.ContDiff.Defs
open scoped ContDiff Interval Topology _root_.Topology
namespace HolomorphicAnosov
set_option backward.isDefEq.respectTransparency false in
/-- All averaged spatial-jet identities imply smoothness of the averaged map and identify its derivative. (Bochner–Montgomery, Lemma 2, equation (13).) -/
theorem average_map_smooth_from_jets_g1
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : ℝ → E → F) (h : ℝ) (S : Set E)
    (havg : ∀ y ∈ S, ∀ k : ℕ,
      HasFDerivAt (fun z ↦ ∫ t in 0..h, iteratedFDeriv ℝ k (f t) z)
        (∫ t in 0..h, fderiv ℝ (iteratedFDeriv ℝ k (f t)) y) y) :
    ContDiffOn ℝ ∞ (fun y ↦ ∫ t in 0..h, f t y) S ∧
      ∀ y, S ∈ 𝓝 y → HasFDerivAt (fun z ↦ ∫ t in 0..h, f t z)
        (∫ t in 0..h, fderiv ℝ (f t) y) y := by
  let P : E → FormalMultilinearSeries ℝ E F :=
    fun y k ↦ ∫ t in 0..h, iteratedFDeriv ℝ k (f t) y
  have hP : HasFTaylorSeriesUpToOn ∞ (fun y ↦ ∫ t in 0..h, f t y) P S := by
    constructor
    · intro y hy
      change (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry (∫ t in 0..h,
        iteratedFDeriv ℝ 0 (f t) y) = _
      have hi := LinearIsometry.intervalIntegral_comp_comm
        (𝕜 := ℝ) (E := E [×0]→L[ℝ] F) (F := F)
        (a := 0) (b := h) (μ := MeasureTheory.volume)
        (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry
        (fun t ↦ iteratedFDeriv ℝ 0 (f t) y)
      rw [← hi]
      simp
    · intro k hk y hy
      have hd := (havg y hy k).hasFDerivWithinAt (s := S)
      convert hd using 1
      change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F).toLinearIsometry
        (∫ t in 0..h, iteratedFDeriv ℝ (k + 1) (f t) y) = _
      have hi := LinearIsometry.intervalIntegral_comp_comm
        (𝕜 := ℝ) (E := E [×(k + 1)]→L[ℝ] F) (F := E →L[ℝ] E [×k]→L[ℝ] F)
        (a := 0) (b := h) (μ := MeasureTheory.volume)
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (k + 1) ↦ E) F).toLinearIsometry
        (fun t ↦ iteratedFDeriv ℝ (k + 1) (f t) y)
      rw [← hi]
      simp only [fderiv_iteratedFDeriv, Function.comp_apply]
      rfl
    · intro k hk y hy
      exact (havg y hy k).continuousAt.continuousWithinAt
  refine ⟨hP.contDiffOn, ?_⟩
  intro y hy
  have hd := hP.hasFDerivAt (by simp) hy
  convert hd using 1
  change (∫ t in 0..h, fderiv ℝ (f t) y) =
    (continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry
      (∫ t in 0..h, iteratedFDeriv ℝ 1 (f t) y)
  have hi := LinearIsometry.intervalIntegral_comp_comm
    (𝕜 := ℝ) (E := E [×1]→L[ℝ] F) (F := E →L[ℝ] F)
    (a := 0) (b := h) (μ := MeasureTheory.volume)
    (continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry
    (fun t ↦ iteratedFDeriv ℝ 1 (f t) y)
  rw [← hi]
  congr 1
  ext t z
  simp

end HolomorphicAnosov
