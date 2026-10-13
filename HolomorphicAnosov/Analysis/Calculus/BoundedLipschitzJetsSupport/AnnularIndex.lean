import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- HPS p.28 annuli cover a punctured ball: take the first radius below t. -/
theorem annular_index {r : ℕ → ℝ} (ht : Tendsto r atTop (𝓝 0))
    {t : ℝ} (hp : 0 < t) (h0 : t ≤ r 0) :
    ∃ n : ℕ, r (n+1) < t ∧ t ≤ r n := by
  have he : ∃ k, r k < t := ((tendsto_order.mp ht).2 t hp).exists
  let k := Nat.find he
  have hk : r k < t := Nat.find_spec he
  have hk0 : k ≠ 0 := by intro h; rw [h] at hk; linarith
  refine ⟨k-1, ?_, ?_⟩
  · simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)] using hk
  · exact le_of_not_gt (Nat.find_min he (by omega : k-1 < k))

end HolomorphicAnosov.BoundedLipschitzJets

