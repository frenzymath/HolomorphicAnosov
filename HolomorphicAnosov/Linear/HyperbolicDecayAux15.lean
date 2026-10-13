import HolomorphicAnosov.Linear.HyperbolicDecayAux14

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- Powers of a restricted continuous operator agree with the corresponding ambient powers. -/
theorem restrict_pow_coe
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W →L[𝕜] W) (p : Submodule 𝕜 W) (h : ∀ v ∈ p, T v ∈ p) (n : ℕ) (v : p) :
    (((T.restrict h) ^ n) v : W) = (T ^ n) (v : W) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [pow_succ', mul_apply_eq_comp, ContinuousLinearMap.coe_restrict_apply] using congrArg T ih



end HolomorphicAnosov
