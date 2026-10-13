import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Set
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- Interior agreement with an interval-integrable function determines the two independent
improper endpoint limits. Source: Mathlib's continuous interval primitive and signed
interval additivity. Both cutoffs eventually lie in the closed carrier; write their
integral as the difference of the two continuous primitive values. -/
theorem intervalIntegralInteriorEndpointLimit {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b) (hfg : EqOn f g (Ioo a b)) :
    Tendsto (fun p : ℝ × ℝ ↦ ∫ x in p.1..p.2, g x)
      ((𝓝[>] a) ×ˢ (𝓝[<] b)) (𝓝 (∫ x in a..b, f x)) := by
  have hu : Tendsto (fun p : ℝ × ℝ ↦ p.1)
      ((𝓝[>] a) ×ˢ (𝓝[<] b)) (𝓝[Icc a b] a) := by
    rw [nhdsWithin_Icc_eq_nhdsGE hab]
    exact tendsto_fst.mono_right (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hv : Tendsto (fun p : ℝ × ℝ ↦ p.2)
      ((𝓝[>] a) ×ˢ (𝓝[<] b)) (𝓝[Icc a b] b) := by
    rw [nhdsWithin_Icc_eq_nhdsLE hab]
    exact tendsto_snd.mono_right (nhdsWithin_mono _ Iio_subset_Iic_self)
  have hc : ContinuousOn (fun y ↦ ∫ x in a..y, f x) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
  have H := ((hc b ⟨hab.le, le_rfl⟩).tendsto.comp hv).sub
    ((hc a ⟨le_rfl, hab.le⟩).tendsto.comp hu)
  simp only [intervalIntegral.integral_same, sub_zero] at H
  apply H.congr'
  have hau : ∀ᶠ p : ℝ × ℝ in ((𝓝[>] a) ×ˢ (𝓝[<] b)), p.1 ∈ Icc a b :=
    hu.eventually self_mem_nhdsWithin
  have hbv : ∀ᶠ p : ℝ × ℝ in ((𝓝[>] a) ×ˢ (𝓝[<] b)), p.2 ∈ Icc a b :=
    hv.eventually self_mem_nhdsWithin
  filter_upwards [hau, hbv] with p hp hq
  have hint : ∀ y ∈ Icc a b, IntervalIntegrable f volume a y := by
    intro y hy
    apply hf.mono_set
    rw [uIcc_of_le hab.le, uIcc_of_le hy.1]
    exact Icc_subset_Icc le_rfl hy.2
  dsimp only [Function.comp_apply]
  rw [intervalIntegral.integral_interval_sub_left (hint _ hq) (hint _ hp)]
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  apply hfg
  rw [uIoo] at hx
  exact ⟨lt_of_le_of_lt (le_min hp.1 hq.1) hx.1,
    lt_of_lt_of_le hx.2 (max_le hp.2 hq.2)⟩

end HolomorphicAnosov.Analysis
