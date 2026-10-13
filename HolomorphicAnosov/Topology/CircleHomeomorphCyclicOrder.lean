import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.ProjIcc
/-! # Degree-one circle homeomorphisms preserve cyclic order

Source: Lyubich, Conformal Geometry, §1.11 pp.53–54 for positive finite
cyclic order; §3.3 pp.107–108 for winding. The lift argument is an
agent-written expansion of the comparison needed by the Carathéodory theorem.

Rotate the source by the chosen cut a; rotation is a homotopy, so winding
remains one. A continuous logarithm lift L has increment 2πi. Its real
part is zero because its exponential has norm one. Thus A=Im L/(2π)
is a continuous real lift with A(1)=A(0)+1. Equality A(s)=A(t) for s<t
would contradict source phase injectivity when t<s+1. The only remaining
case is s=0,t=1, contradicted by the unit increment. Hence A is injective
on [0,1]; continuity and its increasing endpoint values imply strict
increase. Cut at the first of four ordered angles t_i. All t_i−t_0 lie
in [0,1), so their A-values are strictly increasing and span less than
one. These are the required angle representatives of their images.
-/
open Set Metric
open scoped Topology
namespace HolomorphicAnosov
noncomputable section
lemma phase_period (t : ℝ) : Circle.exp (2 * Real.pi * (t + 1)) =
    Circle.exp (2 * Real.pi * t) := by
  rw [mul_add, Circle.exp_add]
  have hh : Circle.exp (2 * Real.pi) = 1 := by
    apply Subtype.ext
    simp only [Circle.coe_exp]
    convert Complex.exp_two_pi_mul_I using 1 <;> push_cast <;> ring
  simp [hh]
lemma phase_inj_short {a b : ℝ} (hab : a < b) (hshort : b < a + 1) :
    Circle.exp (2 * Real.pi * a) ≠ Circle.exp (2 * Real.pi * b) := by
  intro he
  have h := Circle.exp_injOn_Icc (by nlinarith [Real.pi_pos])
    (show 2 * Real.pi * a ∈ Icc (2 * Real.pi * a) (2 * Real.pi * b) from
      ⟨le_rfl, mul_le_mul_of_nonneg_left hab.le (by positivity)⟩)
    (show 2 * Real.pi * b ∈ Icc (2 * Real.pi * a) (2 * Real.pi * b) from
      ⟨mul_le_mul_of_nonneg_left hab.le (by positivity), le_rfl⟩) he
  nlinarith [Real.pi_pos]
/-- A continuous real lift of a circle injection whose increment is one is
strictly increasing on the closed unit interval. -/
lemma strictMono_lift_increment_one (h : Circle ≃ₜ Circle) (a : ℝ) (A : ℝ → ℝ)
    (hA : ContinuousOn A (Icc 0 1))
    (he : ∀ t ∈ Icc (0 : ℝ) 1,
      Circle.exp (2 * Real.pi * A t) = h (Circle.exp (2 * Real.pi * (a + t))))
    (hinc : A 1 = A 0 + 1) : StrictMonoOn A (Icc 0 1) := by
  have hinj : InjOn A (Icc 0 1) := by
    intro s hs t ht heq
    by_contra hne
    wlog hst : s < t generalizing s t
    · exact this ht hs heq.symm (Ne.symm hne) (lt_of_le_of_ne (le_of_not_gt hst) (Ne.symm hne))
    have hexp : Circle.exp (2 * Real.pi * (a + s)) =
        Circle.exp (2 * Real.pi * (a + t)) :=
      h.injective ((he s hs).symm.trans ((congrArg (fun u ↦ Circle.exp (2 * Real.pi * u)) heq).trans (he t ht)))
    by_cases hshort : t < s + 1
    · exact phase_inj_short (by linarith : a + s < a + t) (by linarith) hexp
    · have hs0 : s = 0 := by linarith [hs.1, ht.2]
      have ht1 : t = 1 := by linarith [hs.1, ht.2]
      rw [hs0, ht1, hinc] at heq
      linarith
  exact ContinuousOn.strictMonoOn_of_injOn_Icc (by norm_num) (by linarith) hA hinj
end
end HolomorphicAnosov
namespace HolomorphicAnosov
noncomputable section
/-- Lift a degree-one circle homeomorphism starting at any cut. Rotation is a
free homotopy, so the logarithm lift still has increment 2πi. -/
theorem circle_homeomorph_increasing_lift (h : Circle ≃ₜ Circle)
    (hw : loopWinding ⟨fun z ↦ (h z : ℂ), by fun_prop⟩ 0
      (fun z ↦ Circle.coe_ne_zero _) = 1) (a : ℝ) :
    ∃ A : ℝ → ℝ, ContinuousOn A (Icc 0 1) ∧ StrictMonoOn A (Icc 0 1) ∧
      A 1 = A 0 + 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        Circle.exp (2 * Real.pi * A t) = h (Circle.exp (2 * Real.pi * (a + t))) := by
  let δ : ComplexLoop := ⟨fun z ↦ (h z : ℂ), by fun_prop⟩
  let σ : ComplexLoop := ⟨fun z ↦ (h (Circle.exp (2 * Real.pi * a) * z) : ℂ), by fun_prop⟩
  have hnδ : ∀ z, δ z ≠ 0 := fun z ↦ Circle.coe_ne_zero _
  have hnσ : ∀ z, σ z ≠ 0 := fun z ↦ Circle.coe_ne_zero _
  have hhom : LoopHomotopyAvoids δ σ 0 := by
    refine ⟨⟨fun p ↦ (h (Circle.exp (2 * Real.pi * ((p.1 : ℝ) * a)) * p.2) : ℂ),
      by fun_prop⟩, ?_, ?_, ?_⟩
    · intro z; simp [δ]
    · intro z; simp [σ]
    · intro s z; exact Circle.coe_ne_zero _
  have hwσ : loopWinding σ 0 hnσ = 1 :=
    (loopWinding_homotopy δ σ 0 hnδ hnσ hhom).symm.trans hw
  obtain ⟨L, hL, hinc⟩ := loopWinding_lift σ 0 hnσ
  have hLre (t : unitInterval) : (L t).re = 0 := by
    have hh := congrArg norm (hL t)
    have hexp : Real.exp (L t).re = 1 := by
      simpa [Complex.norm_exp, puncturedLoopPath, σ] using hh
    exact Real.exp_injective (hexp.trans Real.exp_zero.symm)
  let A : ℝ → ℝ := fun t ↦ (L (projIcc 0 1 (by norm_num) t)).im / (2 * Real.pi)
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hAval (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      A t = (L ⟨t, ht⟩).im / (2 * Real.pi) := by
    simp only [A, projIcc_of_mem _ ht]
  have hAe (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Circle.exp (2 * Real.pi * A t) = h (Circle.exp (2 * Real.pi * (a + t))) := by
    apply Subtype.ext
    rw [Circle.coe_exp, hAval t ht]
    have hscalar : 2 * Real.pi * ((L ⟨t, ht⟩).im / (2 * Real.pi)) = (L ⟨t, ht⟩).im := by
      field_simp
    rw [hscalar]
    have hcomplex : ((L ⟨t, ht⟩).im : ℂ) * Complex.I = L ⟨t, ht⟩ := by
      apply Complex.ext <;> simp [hLre]
    rw [hcomplex, hL]
    simp only [puncturedLoopPath, ContinuousMap.coe_mk, sub_zero, σ]
    congr 2
    rw [mul_add, Circle.exp_add]
  have hAinc : A 1 = A 0 + 1 := by
    rw [hAval 1 (by simp), hAval 0 (by simp)]
    rw [hwσ] at hinc
    have hh := congrArg Complex.im hinc
    simp only [Int.cast_one, one_mul, Complex.add_im, Complex.mul_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, add_zero, mul_one] at hh
    norm_num at hh
    change (L (1 : unitInterval)).im / (2 * Real.pi) = (L (0 : unitInterval)).im / (2 * Real.pi) + 1
    rw [hh]
    field_simp
  exact ⟨A, hAc.continuousOn, strictMono_lift_increment_one h a A hAc.continuousOn hAe hAinc,
    hAinc, hAe⟩
end
end HolomorphicAnosov
namespace HolomorphicAnosov
noncomputable section
/-- A circle homeomorphism of degree one preserves a positively ordered finite
list contained in one turn. Cut the source circle at the first point and use
the increasing real lift on that turn. -/
theorem circle_homeomorph_preserves_four (h : Circle ≃ₜ Circle)
    (hw : loopWinding ⟨fun z ↦ (h z : ℂ), by fun_prop⟩ 0
      (fun z ↦ Circle.coe_ne_zero _) = 1)
    (t : Fin 4 → ℝ) (ht : StrictMono t) (hturn : t 3 < t 0 + 1) :
    ∃ v : Fin 4 → ℝ, StrictMono v ∧ v 3 < v 0 + 1 ∧
      ∀ i, h (Circle.exp (2 * Real.pi * t i)) = Circle.exp (2 * Real.pi * v i) := by
  obtain ⟨A, hAc, hAm, hAinc, hAe⟩ := circle_homeomorph_increasing_lift h hw (t 0)
  have hmem (i : Fin 4) : t i - t 0 ∈ Icc (0 : ℝ) 1 := by
    have hlo := ht.monotone (show (0 : Fin 4) ≤ i from Fin.zero_le _)
    have hhi := ht.monotone (show i ≤ (3 : Fin 4) by omega)
    constructor <;> linarith
  refine ⟨fun i ↦ A (t i - t 0), ?_, ?_, ?_⟩
  · intro i j hij
    exact hAm (hmem i) (hmem j) (sub_lt_sub_right (ht hij) _)
  · have hh := hAm (hmem 3) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (show t 3 - t 0 < 1 by linarith)
    simpa [hAinc] using hh
  · intro i
    simpa using (hAe (t i - t 0) (hmem i)).symm
end
end HolomorphicAnosov

