import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set Filter MeasureTheory
open scoped Topology _root_.Topology Interval

namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The finite real-path limit in the Schwarz–Christoffel primitive calculation.

Source: Bak–Newman, *Complex Analysis*, third edition (2010), pp.189–190:
the displayed primitive increment on p.189 and its limiting real-path interpretation
on p.190, restricted here to a closed interval avoiding the prevertices.

Proof: put epsilon_n=1/(n+1). The horizontal path t+i epsilon_n lies in the
upper half-plane. The complex derivative and the real chain rule give derivative
G(t+i epsilon_n) for W along that path. Continuity of G on the compact rectangle
[a,b]+i[0,1] gives a common finite norm bound and integrability on each horizontal
segment. The real fundamental theorem of calculus gives the endpoint difference
as its interval integral. The same compact norm bound is an integrable constant
on [a,b], and continuity of G gives pointwise convergence to G(t). Dominated
convergence therefore gives convergence of the genuine complex interval integrals.
Continuity of the specified extension gives convergence of both endpoint values.
Uniqueness of limits yields the asserted boundary increment. When a=b, all
integrals and differences vanish; no boundary derivative of W is assumed.
-/
theorem holomorphic_boundary_primitive_increment
    (W Wbar G : ℂ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hder : ∀ z : ℂ, 0 < z.im → HasDerivAt W (G z) z)
    (heq : EqOn Wbar W {z : ℂ | 0 < z.im})
    (hWbar : ContinuousOn Wbar {z : ℂ | 0 ≤ z.im})
    (hG : ContinuousOn G {z : ℂ | z.re ∈ Icc a b ∧ z.im ∈ Icc (0 : ℝ) 1}) :
    Wbar (b : ℂ) - Wbar (a : ℂ) = ∫ t in a..b, G (t : ℂ) := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let P : ℝ → ℝ → ℂ := fun t s ↦ (t : ℂ) + (s : ℂ) * Complex.I
  have hPmem {t s : ℝ} (ht : t ∈ Icc a b) (hs : s ∈ Icc (0 : ℝ) 1) :
      (P t s).re ∈ Icc a b ∧ (P t s).im ∈ Icc (0 : ℝ) 1 := by
    simpa [P] using And.intro ht hs
  have hGc : ContinuousOn (fun p : ℝ × ℝ ↦ G (P p.1 p.2))
      (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hG.comp (by dsimp [P]; fun_prop) (fun p hp ↦ hPmem hp.1 hp.2)
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hGc
  have hcont (n : ℕ) : ContinuousOn (fun t : ℝ ↦ G (P t (ε n))) (Icc a b) :=
    hG.comp (by dsimp [P]; fun_prop) (fun t ht ↦ hPmem ht ⟨(hεpos n).le, hεle n⟩)
  have hint (n : ℕ) : IntervalIntegrable (fun t : ℝ ↦ G (P t (ε n))) volume a b :=
    (hcont n).intervalIntegrable_of_Icc hab
  have hpath (n : ℕ) (t : ℝ) :
      HasDerivAt (fun t : ℝ ↦ W (P t (ε n))) (G (P t (ε n))) t := by
    have h := (hder (P t (ε n)) (by simpa [P] using hεpos n)).comp
      (t : ℂ) ((hasDerivAt_id (t : ℂ)).add_const ((ε n : ℂ) * Complex.I))
    simpa [P] using h.comp_ofReal
  have hFTC (n : ℕ) :
      (∫ t in a..b, G (P t (ε n))) = Wbar (P b (ε n)) - Wbar (P a (ε n)) := by
    rw [heq (by simpa [P] using hεpos n), heq (by simpa [P] using hεpos n)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ hpath n t) (hint n)
  have hPlim (t : ℝ) : Tendsto (fun n ↦ P t (ε n)) atTop (𝓝 (t : ℂ)) := by
    simpa [P] using tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0 |>.comp hεlim).mul_const Complex.I)
  have hGlim (t : ℝ) (ht : t ∈ Icc a b) :
      Tendsto (fun n ↦ G (P t (ε n))) atTop (𝓝 (G (t : ℂ))) := by
    apply (hG (t : ℂ) (by simpa using And.intro ht (show (0 : ℝ) ∈ Icc 0 1 by norm_num))).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hPlim t, Eventually.of_forall fun n ↦ hPmem ht ⟨(hεpos n).le, hεle n⟩⟩
  have hIl : Tendsto (fun n ↦ ∫ t in a..b, G (P t (ε n))) atTop
      (𝓝 (∫ t in a..b, G (t : ℂ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ M)
    · exact Eventually.of_forall fun n ↦ by
        simpa only [uIoc_of_le hab] using (hint n).aestronglyMeasurable
    · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun t ht ↦
        hM (t, ε n) ⟨(uIoc_subset_uIcc ht |> (uIcc_of_le hab ▸ ·)), (hεpos n).le, hεle n⟩
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun t ht ↦ hGlim t
        (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht)
  have hWlim (t : ℝ) : Tendsto (fun n ↦ Wbar (P t (ε n))) atTop (𝓝 (Wbar (t : ℂ))) := by
    apply (hWbar (t : ℂ) (by simp)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hPlim t, Eventually.of_forall fun n ↦ by simpa [P] using (hεpos n).le⟩
  exact tendsto_nhds_unique ((hWlim b).sub (hWlim a)) (hIl.congr hFTC)

end HolomorphicAnosov.Analysis.MarkedRectangle
