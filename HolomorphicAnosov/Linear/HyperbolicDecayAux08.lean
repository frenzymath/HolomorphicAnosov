import HolomorphicAnosov.Linear.HyperbolicDecayAux07

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- A finite-dimensional complex operator whose eigenvalues all lie inside the unit circle has powers converging to zero in operator norm. -/
theorem operator_powers_decay_of_eigenvalues
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →L[ℂ] W)
    (hB : ∀ μ, Module.End.HasEigenvalue B.toLinearMap μ → ‖μ‖ < 1) :
    Tendsto (fun n : ℕ ↦ B ^ n) atTop (𝓝 0) := by
  rcases subsingleton_or_nontrivial W with hs | hn
  · let := hs
    simpa only [show (fun n : ℕ ↦ B ^ n) = fun _ ↦ (0 : W →L[ℂ] W) from
      funext fun _ ↦ Subsingleton.elim _ _] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : W →L[ℂ] W)) atTop (𝓝 0))
  · let := hn
    apply powers_tendsto_zero_of_spectralRadius_lt_one B
    apply spectrum.spectralRadius_lt_of_forall_lt
    intro μ hμ
    rw [ContinuousLinearMap.spectrum_eq] at hμ
    exact_mod_cast hB μ (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)



end HolomorphicAnosov
