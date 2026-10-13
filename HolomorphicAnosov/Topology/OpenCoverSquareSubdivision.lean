import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite square grid subordinate to an open cover

This file constructs a finite grid of the unit square whose closed cells map into cover members. (Nisoli, Thm. 1.3.8)
-/

namespace HolomorphicAnosov
open Set

/-- A continuous map of the unit square admits a finite uniform grid whose closed cells map into members of any open cover. (Nisoli, Thm. 1.3.8) -/
theorem exists_openCover_squareSubdivision
    {X ι : Type*} [TopologicalSpace X]
    (H : unitInterval × unitInterval → X) (hH : Continuous H)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ z, ∃ i, H z ∈ U i) :
    ∃ n : ℕ, ∃ t : Fin (n + 2) → unitInterval,
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧
      ∀ j k : Fin (n + 1), ∃ i,
        MapsTo H (Icc (t j.castSucc) (t j.succ) ×ˢ
          Icc (t k.castSucc) (t k.succ)) (U i) := by
  have hcov : (univ : Set (unitInterval × unitInterval)) ⊆ ⋃ i, H ⁻¹' U i := by
    intro z _
    obtain ⟨i, hi⟩ := hcover z
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i ↦ (hU i).preimage hH) hcov
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  let t : Fin (n + 2) → unitInterval := fun j ↦
    ⟨(j.val : ℝ) / (n + 1), by
      constructor
      · positivity
      · apply (div_le_one hnpos).2
        exact_mod_cast (Nat.le_of_lt_succ j.isLt)⟩
  have hclose (j : Fin (n + 1)) (z : unitInterval)
      (hz : z ∈ Icc (t j.castSucc) (t j.succ)) : dist z (t j.castSucc) < δ := by
    have hlo : (j.val : ℝ) / (n + 1) ≤ (z : ℝ) := hz.1
    have hhi : (z : ℝ) ≤ (j.val + 1 : ℝ) / (n + 1) := by
      have hh : (z : ℝ) ≤ ((j.succ.val : ℝ) / (n + 1)) := hz.2
      simpa only [Fin.val_succ, Nat.cast_add, Nat.cast_one] using hh
    change |(z : ℝ) - (j.val : ℝ) / (n + 1)| < δ
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    calc
      (z : ℝ) - (j.val : ℝ) / (n + 1) ≤
          (j.val + 1 : ℝ) / (n + 1) - (j.val : ℝ) / (n + 1) :=
        sub_le_sub_right hhi _
      _ = 1 / (n + 1 : ℝ) := by ring
      _ < δ := hn
  refine ⟨n, t, ?_, ?_, ?_, ?_⟩
  · intro j k hjk
    change (j.val : ℝ) / (n + 1) < (k.val : ℝ) / (n + 1)
    exact (div_lt_div_iff_of_pos_right hnpos).2 (Nat.cast_lt.mpr hjk)
  · apply Subtype.ext
    simp [t]
  · apply Subtype.ext
    simp [t, ne_of_gt hnpos]
  · intro j k
    obtain ⟨i, hi⟩ := hball (t j.castSucc, t k.castSucc) (mem_univ _)
    refine ⟨i, fun z hz ↦ hi ?_⟩
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hclose j z.1 hz.1, hclose k z.2 hz.2⟩

end HolomorphicAnosov
