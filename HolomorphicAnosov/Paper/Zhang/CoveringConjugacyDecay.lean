import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology _root_.Topology
open Filter Set

universe u
namespace HolomorphicAnosov

/-- C9's decay identification on the actual normed vector carrier. (Zhang, p. 11) -/
theorem covering_conjugacy_decay_iff_g15
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V ≃L[ℝ] V) (Es Eu : Submodule ℝ V)
    (Ps Pu : V →L[ℝ] V) (Cs Cu rs ru : ℝ)
    (hPs : LinearMap.range Ps.toLinearMap = Es)
    (hPu : LinearMap.range Pu.toLinearMap = Eu)
    (hsum : Ps + Pu = ContinuousLinearMap.id ℝ V)
    (hcomm : ∀ v, Pu (A v) = A (Pu v))
    (hrs : 0 ≤ rs) (hrs1 : rs < 1) (hru : 0 ≤ ru) (hru1 : ru < 1)
    (hstable : ∀ n v, v ∈ Es →
      ‖(A : V → V)^[n] v‖ ≤ Cs * rs ^ n * ‖v‖)
    (hunstable : ∀ n v, v ∈ Eu →
      ‖(A.symm : V → V)^[n] v‖ ≤ Cu * ru ^ n * ‖v‖) (v : V) :
    Tendsto (fun n : ℕ ↦ (A : V → V)^[n] v) atTop (𝓝 0) ↔ v ∈ Es := by
  have hpowers (n : ℕ) (w : V) : Pu ((A : V → V)^[n] w) =
      (A : V → V)^[n] (Pu w) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', hcomm, ih]
  have hzero := tendsto_pow_atTop_nhds_zero_of_lt_one hrs hrs1
  constructor
  · intro hv
    have hproject : Tendsto (fun n : ℕ ↦ Pu ((A : V → V)^[n] v)) atTop (𝓝 0) :=
      by simpa only [Function.comp_def, map_zero] using (Pu.continuous.tendsto 0).comp hv
    have hupper : Tendsto (fun n : ℕ ↦ Cu * ru ^ n *
        ‖Pu ((A : V → V)^[n] v)‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hru hru1)).mul hproject.norm
    have hnorm : Tendsto (fun _ : ℕ ↦ ‖Pu v‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ ↦ norm_nonneg _) _ hupper
      intro n
      have hm : Pu ((A : V → V)^[n] v) ∈ Eu := by
        rw [← hPu]
        exact LinearMap.mem_range_self _ _
      have hb := hunstable n _ hm
      have hcancel : Function.LeftInverse (A.symm : V → V) (A : V → V) :=
        A.symm_apply_apply
      rw [hpowers, hcancel.iterate n] at hb
      simpa only [hpowers] using hb
    have hPv : Pu v = 0 := norm_eq_zero.mp
      (tendsto_nhds_unique tendsto_const_nhds hnorm)
    have hvPs : Ps v = v := by
      have hh := congrArg (fun L : V →L[ℝ] V ↦ L v) hsum
      simpa [hPv] using hh
    rw [← hvPs, ← hPs]
    exact LinearMap.mem_range_self _ _
  · intro hv
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ hstable n v hv)
    simpa using (tendsto_const_nhds.mul hzero).mul_const ‖v‖


end HolomorphicAnosov
