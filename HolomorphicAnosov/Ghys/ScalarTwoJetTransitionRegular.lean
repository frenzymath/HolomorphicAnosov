import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic

/-! Normalized scalar jet transitions are complex smooth on open scalar domains. (Ghys, §3) -/
open Set
open scoped ContDiff
namespace HolomorphicAnosov.Ghys

/-- On an open scalar domain, a complex smooth map induces complex smooth first and normalized second coefficient transitions. (Ghys, §3) -/
theorem scalar_two_jet_transition_regular {h : ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hh : ContDiffOn ℂ ∞ h s) :
    ContDiffOn ℂ ∞ (fun w : ℂ × ℂ ↦ (h w.1, deriv h w.1 * w.2))
      {w | w.1 ∈ s} ∧
    ContDiffOn ℂ ∞ (fun w : (ℂ × ℂ) × ℂ ↦
      ((h w.1.1, deriv h w.1.1 * w.1.2),
        deriv h w.1.1 * w.2 + iteratedDeriv 2 h w.1.1 * w.1.2 ^ 2 / 2))
      {w | w.1.1 ∈ s} := by
  have hd : ContDiffOn ℂ ∞ (deriv h) s := hh.deriv_of_isOpen hs (by simp)
  have hdd : ContDiffOn ℂ ∞ (iteratedDeriv 2 h) s := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      hd.deriv_of_isOpen hs (show ∞ + 1 ≤ ∞ by simp)
  constructor
  · have hp : ContDiffOn ℂ ∞ (fun w : ℂ × ℂ ↦ w.1) {w | w.1 ∈ s} :=
      contDiff_fst.contDiffOn
    have hf := hh.comp hp (fun w hw ↦ hw)
    have hdf := hd.comp hp (fun w hw ↦ hw)
    exact hf.prodMk (hdf.mul contDiff_snd.contDiffOn)
  · have hp : ContDiffOn ℂ ∞ (fun w : (ℂ × ℂ) × ℂ ↦ w.1.1) {w | w.1.1 ∈ s} :=
      contDiff_fst.fst.contDiffOn
    have hf := hh.comp hp (fun w hw ↦ hw)
    have hdf := hd.comp hp (fun w hw ↦ hw)
    have hddf := hdd.comp hp (fun w hw ↦ hw)
    exact (hf.prodMk (hdf.mul contDiff_fst.snd.contDiffOn)).prodMk
      ((hdf.mul contDiff_snd.contDiffOn).add
        ((hddf.mul (contDiff_fst.snd.contDiffOn.pow 2)).div_const 2))

end HolomorphicAnosov.Ghys
