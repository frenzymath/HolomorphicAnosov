import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter

open Set Filter _root_.Topology
open scoped BigOperators ENNReal Classical
noncomputable section

/-- Compactness gives a finite cover by extended balls of radius one. For a finite-distance pair, its chosen centers are at finite distance. The triangle inequality bounds the pair by two plus the center distance, which is bounded by the nonnegative finite double sum. No connectedness is used. -/
theorem compact_finite_edist_bound {X : Type*} [PseudoEMetricSpace X] [CompactSpace X] :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : X, edist x y ≠ ⊤ → (edist x y).toReal ≤ R := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ Metric.eball x 1) (fun _ ↦ Metric.isOpen_eball)
    (by intro x hx; exact mem_iUnion.mpr ⟨x, by simp⟩)
  let C : ℝ := ∑ i ∈ t, ∑ j ∈ t, (edist i j).toReal
  have hC : 0 ≤ C := by positivity
  refine ⟨C + 3, by linarith, ?_⟩
  intro x y hxy
  obtain ⟨i, hit, hix⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  obtain ⟨j, hjt, hjy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  have hix1 : edist i x < 1 := by simpa only [Metric.mem_eball, edist_comm] using hix
  have hjy1 : edist j y < 1 := by simpa only [Metric.mem_eball, edist_comm] using hjy
  have hixf : edist i x < ⊤ := hix1.trans (by simp)
  have hjyf : edist j y < ⊤ := hjy1.trans (by simp)
  have hijf : edist i j < ⊤ := Metric.edistLtTopSetoid.iseqv.trans hixf
    (Metric.edistLtTopSetoid.iseqv.trans (lt_top_iff_ne_top.mpr hxy)
      (Metric.edistLtTopSetoid.iseqv.symm hjyf))
  have hxif : edist x i ≠ ⊤ := by simpa only [edist_comm] using hixf.ne
  have hsum : edist x i + edist i j + edist j y ≠ ⊤ := by
    simp [hxif, hijf.ne, hjyf.ne]
  have hbound := ENNReal.toReal_mono hsum
    (show edist x y ≤ edist x i + edist i j + edist j y from
      (edist_triangle x j y).trans
        (add_le_add (edist_triangle x i j) le_rfl))
  rw [ENNReal.toReal_add (by simp [hxif, hijf.ne]) hjyf.ne,
    ENNReal.toReal_add hxif hijf.ne] at hbound
  have hxir : (edist x i).toReal ≤ 1 := by
    simpa only [edist_comm, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top hix1.le
  have hjyr : (edist j y).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top hjy1.le
  have hcell : (edist i j).toReal ≤ C := by
    exact (Finset.single_le_sum (fun _ _ ↦ ENNReal.toReal_nonneg) hjt).trans
      (Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ ENNReal.toReal_nonneg)) hit)
  linarith


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter
