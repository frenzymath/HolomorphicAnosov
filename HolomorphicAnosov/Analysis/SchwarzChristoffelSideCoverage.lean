import Mathlib.Analysis.Calculus.Deriv.MeanValue

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Order.IntermediateValue

/-! Source-backed boundary segment adapter for the Schwarz–Christoffel proof.
Bak–Newman, *Complex Analysis*, third edition (2010), pp.189–190, states that
constant derivative argument sends each real interval to a straight segment and uses
`f(z)-f(z₀)=∫ f'`. This module formalizes the positive-real phase-zero case with
Mathlib's derivative monotonicity and intermediate-value lemmas. -/

open Set
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The constant-argument boundary step of Bak–Newman p.189, normalized to phase
zero: a continuous curve on a closed real interval whose interior derivative is a
strictly positive real number traverses the entire horizontal segment between its
endpoints, monotonically and injectively. No derivative at either endpoint is needed. -/
theorem positive_real_derivative_whole_segment
    {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℂ) (p : ℝ → ℝ)
    (hcont : ContinuousOn F (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt F (p t : ℂ) t)
    (hp : ∀ t ∈ Ioo a b, 0 < p t) :
    StrictMonoOn (fun t ↦ (F t).re) (Icc a b) ∧
    (∀ t ∈ Icc a b, (F t).im = (F a).im) ∧
    F '' Icc a b = Complex.reProdIm (Icc (F a).re (F b).re) {(F a).im} := by
  have hcR : ContinuousOn (fun t ↦ (F t).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn hcont
  have hcI : ContinuousOn (fun t ↦ (F t).im) (Icc a b) :=
    Complex.continuous_im.comp_continuousOn hcont
  have hdR (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun t ↦ (F t).re) (p t) t := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t ht)
  have hdI (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun t ↦ (F t).im) 0 t := by
    simpa only [Function.comp_def, Complex.imCLM_apply, Complex.ofReal_im] using Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hder t ht)
  have hm : StrictMonoOn (fun t ↦ (F t).re) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcR
    intro t ht
    rw [interior_Icc] at ht
    rw [(hdR t ht).deriv]
    exact hp t ht
  have hmI : MonotoneOn (fun t ↦ (F t).im) (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hcI
      (fun t ht ↦ (hdI t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    intro t ht
    exact le_rfl
  have haI : AntitoneOn (fun t ↦ (F t).im) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hcI
      (fun t ht ↦ (hdI t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    intro t ht
    exact le_rfl
  have hconst (t : ℝ) (ht : t ∈ Icc a b) : (F t).im = (F a).im :=
    le_antisymm (haI (left_mem_Icc.mpr hab) ht ht.1)
      (hmI (left_mem_Icc.mpr hab) ht ht.1)
  refine ⟨hm, hconst, Set.Subset.antisymm ?_ ?_⟩
  · rintro w ⟨t, ht, rfl⟩
    refine ⟨⟨hm.monotoneOn (left_mem_Icc.mpr hab) ht ht.1,
      hm.monotoneOn ht (right_mem_Icc.mpr hab) ht.2⟩, ?_⟩
    exact hconst t ht
  · intro w hw
    obtain ⟨t, ht, htr⟩ := intermediate_value_Icc hab hcR hw.1
    refine ⟨t, ht, Complex.ext htr ?_⟩
    exact (hconst t ht).trans hw.2.symm

end HolomorphicAnosov.Analysis.MarkedRectangle
