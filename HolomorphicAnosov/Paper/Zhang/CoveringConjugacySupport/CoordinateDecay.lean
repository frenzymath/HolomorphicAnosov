import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacyDecay

open scoped Topology
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- C9 on the published spectral child's finite coordinate carrier. -/
theorem covering_conjugacy_coordinate_decay_g15
    (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) :
    ∃ Es Eu : Submodule ℝ (Fin n → ℝ),
      (Es : Set (Fin n → ℝ)) = {v | Tendsto (fun j : ℕ ↦ A^[j] v) atTop (𝓝 0)} ∧
      (Eu : Set (Fin n → ℝ)) = {v | Tendsto (fun j : ℕ ↦ A.symm^[j] v) atTop (𝓝 0)} ∧
      IsCompl Es Eu := by
  obtain ⟨Es, Eu, Ps, Pu, Cs, Cu, rs, ru, hcompl, _, _, _, _, hPs, hPu,
    _, _, hsum, hPsA, hPuA, _, _, hrs, hrs1, hru, hru1, hs, hu, _⟩ :=
      hyperbolic_real_splitting n A hA
  have hs' : ∀ j v, v ∈ Es → ‖A^[j] v‖ ≤ Cs * rs ^ j * ‖v‖ := by
    simpa only [LinearEquiv.pow_apply] using hs
  have hu' : ∀ j v, v ∈ Eu → ‖A.symm^[j] v‖ ≤ Cu * ru ^ j * ‖v‖ := by
    simpa only [LinearEquiv.pow_apply] using hu
  have hPsAi : ∀ v, Ps (A.symm v) = A.symm (Ps v) := by
    intro v
    have h := congrArg A.symm (hPsA (A.symm v))
    simpa only [A.apply_symm_apply, A.symm_apply_apply] using h.symm
  refine ⟨Es, Eu, ?_, ?_, hcompl⟩
  · ext v
    exact (covering_conjugacy_decay_iff_g15 A.toContinuousLinearEquiv Es Eu Ps Pu
      Cs Cu rs ru hPs hPu hsum hPuA hrs.le hrs1 hru.le hru1 hs' hu' v).symm
  · ext v
    exact (covering_conjugacy_decay_iff_g15 A.symm.toContinuousLinearEquiv Eu Es Pu Ps
      Cu Cs ru rs hPu hPs (by simpa only [add_comm] using hsum) hPsAi
      hru.le hru1 hrs.le hrs1 hu' hs' v).symm


end HolomorphicAnosov
