import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
Public DAG node: `analysis.mashreghi_finite_radial_estimate_g3` (statement).
Source origin: Mashreghi Theorem 4.3 forward proof, printed p.442, finite radial integral before (4.6). Exact constant-exponent specialization.
Document: Javad Mashreghi, Generalized Lipschitz Functions, CMFT 5(2) (2005), 431-444.
Local source: literature/mashreghi-generalized-lipschitz-2005-author-fulltext.txt.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology _root_.Topology
namespace HolomorphicAnosov.MashreghiRadial
/-- Finite radial displacement estimate with the fixed constant from the hypothesis.
Source: Mashreghi Theorem 4.3, printed p.442, the radial integral preceding (4.6).
Proof: differentiate r↦F(rη) over the real scalars. Since η is unit and
0≤u≤v<1, its derivative norm is bounded by C(1-r)^(α-1) throughout the
interval. The majorant is continuous and genuinely interval-integrable.
Apply the norm-versus-integral inequality and evaluate the majorant using
−(C/α)(1-r)^α as an antiderivative. This yields the displayed exact difference
of powers. The paper absorbs constants; C/α here is the constant-exponent
integral, not a literal numerical constant quoted from the paper. -/
theorem finite_radial_estimate
    (α C : ℝ) (hα : 0 < α) (_hC : 0 ≤ C)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F {z : ℂ | ‖z‖ < 1})
    (hderiv : ∀ z : ℂ, ‖z‖ < 1 → ‖deriv F z‖ ≤ C * (1 - ‖z‖) ^ (α - 1))
    (η : ℂ) (hη : ‖η‖ = 1) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) :
    ‖F ((v : ℂ) * η) - F ((u : ℂ) * η)‖ ≤
      (C / α) * ((1 - u) ^ α - (1 - v) ^ α) := by
  have hnorm (t : ℝ) (ht : t ∈ Icc u v) : ‖(t : ℂ) * η‖ = t := by
    rw [norm_mul, hη, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hu.trans ht.1)]
  have hinside (t : ℝ) (ht : t ∈ Icc u v) : ‖(t : ℂ) * η‖ < 1 := by
    rw [hnorm t ht]
    exact lt_of_le_of_lt ht.2 hv
  have hpath (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (s : ℂ) * η) η t := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const η).comp_ofReal
  have hdiff (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivAt (fun s : ℝ ↦ F ((s : ℂ) * η))
        (η * deriv F ((t : ℂ) * η)) t := by
    have hf := (hF.differentiableAt
      ((isOpen_lt continuous_norm continuous_const).mem_nhds (hinside t ht))).hasDerivAt
    simpa only [Function.comp_def, smul_eq_mul] using hf.scomp t (hpath t)
  have hcont : ContinuousOn (fun t : ℝ ↦ F ((t : ℂ) * η)) (Icc u v) := by
    intro t ht
    exact (hdiff t ht).continuousAt.continuousWithinAt
  have hB : ContinuousOn (fun t : ℝ ↦ C * (1 - t) ^ (α - 1)) (Icc u v) := by
    apply continuousOn_const.mul
    apply ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
    intro t ht
    exact Or.inl (ne_of_gt (by change 0 < 1 - t; linarith [ht.2]))
  have hBi : IntervalIntegrable (fun t : ℝ ↦ C * (1 - t) ^ (α - 1)) volume u v := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le huv] using hB
  have hbound : ‖F ((v : ℂ) * η) - F ((u : ℂ) * η)‖ ≤
      ∫ t in u..v, C * (1 - t) ^ (α - 1) := by
    apply norm_sub_le_integral_of_norm_deriv_le_of_le huv hcont
    · intro t ht
      exact (hdiff t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
    · apply Filter.Eventually.of_forall
      intro t ht
      rw [(hdiff t ⟨ht.1.le, ht.2.le⟩).deriv, norm_mul, hη, one_mul]
      simpa only [hnorm t ⟨ht.1.le, ht.2.le⟩] using hderiv _ (hinside t ⟨ht.1.le, ht.2.le⟩)
    · exact hBi
  have hanti (t : ℝ) (ht : t ∈ Icc u v) :
      HasDerivAt (fun s : ℝ ↦ -(C / α) * (1 - s) ^ α)
        (C * (1 - t) ^ (α - 1)) t := by
    have hr := ((hasDerivAt_id t).const_sub 1).rpow_const
      (p := α) (Or.inl (ne_of_gt (by change 0 < 1 - t; linarith [ht.2])))
    convert hr.const_mul (-(C / α)) using 1
    · rfl
    · dsimp only [id_eq]
      field_simp
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hanti t (by simpa only [uIcc_of_le huv] using ht)) hBi
  refine hbound.trans_eq (hint.trans ?_)
  ring
end HolomorphicAnosov.MashreghiRadial
