import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Filter Set
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Strict local eventual bounds below one yield a positive uniform bound strictly below one.
The positive padding also covers zero operator norms and zero-dimensional fibres. -/
theorem compact_local_strict_bound (b : X → ℝ)
    (hb : ∀ x, ∃ q : ℝ, q < 1 ∧ ∀ᶠ y in 𝓝 x, b y ≤ q) :
    ∃ theta : ℝ, 0 < theta ∧ theta < 1 ∧ ∀ x, b x ≤ theta := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨1 / 2, by norm_num, by norm_num, fun x ↦ isEmptyElim x⟩
  · choose q hq hbound using hb
    obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
      (fun x ↦ {y | b y ≤ q x}) hbound
    have htne : t.Nonempty := by
      obtain ⟨x⟩ := hX
      have hx : x ∈ ⋃ z ∈ t, {y | b y ≤ q z} := by rw [ht]; trivial
      obtain ⟨z, hz, _⟩ := mem_iUnion₂.mp hx
      exact ⟨z, hz⟩
    obtain ⟨z, hz, hmax⟩ := t.exists_max_image q htne
    let m : ℝ := max 0 (q z)
    have hm0 : 0 ≤ m := le_max_left _ _
    have hm1 : m < 1 := max_lt zero_lt_one (hq z)
    refine ⟨(m + 1) / 2, by linarith, by linarith, fun x ↦ ?_⟩
    have hx : x ∈ ⋃ w ∈ t, {y | b y ≤ q w} := by rw [ht]; trivial
    obtain ⟨w, hw, hwx⟩ := mem_iUnion₂.mp hx
    have hxm : b x ≤ m := hwx.trans ((hmax w hw).trans (le_max_right _ _))
    linarith

end HolomorphicAnosov
