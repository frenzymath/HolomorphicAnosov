import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.SpecificLimits.Normed

namespace HolomorphicAnosov

open Filter Topology _root_.Topology

theorem tendsto_clm_zero_of_pointwise
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ V]
    (f : ℕ → V →L[ℝ] W) (hf : ∀ v, Tendsto (fun n ↦ f n v) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  let e : (V →L[ℝ] W) ≃L[ℝ] Fin (Module.finrank ℝ V) → W :=
    ((ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm).arrowCongr
      (1 : W ≃L[ℝ] W)).trans (ContinuousLinearEquiv.piRing _)
  rw [e.toHomeomorph.isInducing.tendsto_nhds_iff]
  refine tendsto_pi_nhds.mpr fun i ↦ ?_
  change Tendsto (fun n ↦ f n
    ((ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm).symm
      (Pi.single i 1))) atTop (𝓝 0)
  exact hf _

end HolomorphicAnosov
