import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

noncomputable section

namespace HolomorphicAnosov.BowenBasicSetCoding

open Set Filter
open scoped Topology _root_.Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The five Bowen scales are chosen successively by uniform continuity of
the original map and its inverse, together with the bracket modulus. The
iteration is on positive radii, so positivity is preserved by construction.
Source: Bowen (1970), the scale choice on p. 728. -/
theorem exists_factOne_product_scales
    (F : X ≃ₜ X) (γ : ℝ) (hγ : 0 < γ) (εmod : ℝ → ℝ)
    (hmod : ∀ δ, 0 < δ → 0 < εmod δ) :
    ∃ α : Fin 5 → ℝ, α 0 = γ ∧ (∀ i, 0 < α i) ∧
      (∀ i : Fin 4,
        α i.succ < (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3))) ∧
      (∀ i : Fin 4, ∀ a b : X, dist a b ≤ α i.succ →
        dist (F a) (F b) < α i.castSucc ∧
          dist (F.symm a) (F.symm b) < α i.castSucc) := by
  have hstep : ∀ r : {r : ℝ // 0 < r}, ∃ s : {r : ℝ // 0 < r},
      s.val < (1 / 3 : ℝ) * min (r.val / 3) (εmod (r.val / 3)) ∧
      ∀ a b : X, dist a b ≤ s.val →
        dist (F a) (F b) < r.val ∧ dist (F.symm a) (F.symm b) < r.val := by
    intro r
    obtain ⟨u, hu, huf⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous F.continuous) r.val r.property
    obtain ⟨v, hv, hvf⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous F.symm.continuous) r.val r.property
    let t := (1 / 3 : ℝ) * min (r.val / 3) (εmod (r.val / 3))
    have ht : 0 < t := mul_pos (by norm_num)
      (lt_min (div_pos r.property (by norm_num))
        (hmod _ (div_pos r.property (by norm_num))))
    let s := min t (min u v) / 2
    have hs : 0 < s := half_pos (lt_min ht (lt_min hu hv))
    have hst : s < t := (half_lt_self (lt_min ht (lt_min hu hv))).trans_le
      (min_le_left _ _)
    have hsu : s < u := (half_lt_self (lt_min ht (lt_min hu hv))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
    have hsv : s < v := (half_lt_self (lt_min ht (lt_min hu hv))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨⟨s, hs⟩, hst, fun a b hab ↦
      ⟨huf (hab.trans_lt hsu), hvf (hab.trans_lt hsv)⟩⟩
  choose step hscale hmap using hstep
  let a : ℕ → {r : ℝ // 0 < r} := fun n ↦ step^[n] ⟨γ, hγ⟩
  have ha : ∀ n, a (n + 1) = step (a n) := fun n ↦ Function.iterate_succ_apply' ..
  refine ⟨fun i ↦ (a i.val).val, rfl, fun i ↦ (a i.val).property, ?_, ?_⟩
  · intro i
    change (a (i.val + 1)).val < _
    rw [ha]
    exact hscale (a i.val)
  · intro i x y hxy
    change dist x y ≤ (a (i.val + 1)).val at hxy
    rw [ha] at hxy
    exact hmap (a i.val) x y hxy


end HolomorphicAnosov.BowenBasicSetCoding
