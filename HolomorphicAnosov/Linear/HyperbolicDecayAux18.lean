import HolomorphicAnosov.Linear.HyperbolicDecayAux17

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-- If the inverse operator powers tend to zero, every vector whose forward orbit tends to zero is
zero. (Alves, Thm 5.5) -/
theorem eq_zero_of_forward_decay_of_inverse_operator_decay
    {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (T : W ≃L[𝕜] W)
    (hi : Tendsto (fun n : ℕ ↦ T.symm.toContinuousLinearMap ^ n) atTop (𝓝 0))
    (v : W) (hv : Tendsto (fun n : ℕ ↦ (T ^ n) v) atTop (𝓝 0)) : v = 0 := by
  have h := ((isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := W) (F := W)).continuous.tendsto
    ((0 : W →L[𝕜] W), (0 : W))).comp (hi.prodMk_nhds hv)
  have hc : Tendsto (fun _ : ℕ ↦ v) atTop (𝓝 0) := by
    convert h using 1
    funext n
    change v = (T.symm.toContinuousLinearMap ^ n) ((T ^ n) v)
    rw [← equiv_pow_map]
    change v = (T.symm ^ n) ((T ^ n) v)
    change v = (T.symm ^ n * T ^ n) v
    have he : T.symm ^ n * T ^ n = 1 := by
      change T⁻¹ ^ n * T ^ n = 1
      rw [inv_pow, inv_mul_cancel]
    rw [he]
    rfl
  exact tendsto_nhds_unique tendsto_const_nhds hc



end HolomorphicAnosov
