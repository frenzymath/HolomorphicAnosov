import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Small sublevel sets after removing a null zero set
-/

open MeasureTheory Set
open scoped ENNReal Topology _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Analysis.Regularity

/-- A measurable real function with null zero set has arbitrarily small absolute
value sublevel sets in a finite measure space.

Source: Campanato (1964), Lemma [2.I], pp.140–143; the zero-set-null input is
Mityagin's real-analytic zero-set theorem. The decreasing sublevel sets at reciprocal positive integer thresholds
intersect in the zero set. Continuity from above makes their measures tend
to zero, so a threshold with measure below the requested positive bound exists.
DAG node: analysis.sublevel_small_of_zero_set_null_g18. -/
theorem exists_measure_sublevel_lt_of_zero_set_null
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hzero : μ {x | f x = 0} = 0) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ r : ℝ, 0 < r ∧ μ {x | |f x| ≤ r} < ε := by
  intro ε hε
  let s : ℕ → Set α := fun m ↦ {x | |f x| ≤ (m + 1 : ℝ)⁻¹}
  have hs : ∀ m, NullMeasurableSet (s m) μ := fun m ↦
    (measurableSet_le (continuous_abs.measurable.comp hf) measurable_const).nullMeasurableSet
  have hmono : Antitone s := by
    intro m n hmn x hx
    change |f x| ≤ (m + 1 : ℝ)⁻¹
    change |f x| ≤ (n + 1 : ℝ)⁻¹ at hx
    have hcast : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hmn 1
    exact hx.trans (by simpa [one_div] using
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < m + 1) hcast)
  have hinter : (⋂ m, s m) = {x | f x = 0} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro hx
      by_contra hne
      have hpos := abs_pos.mpr hne
      obtain ⟨m, hm⟩ := exists_nat_gt (|f x|⁻¹)
      have hlt : (m + 1 : ℝ)⁻¹ < |f x| := by
        rw [inv_lt_comm₀ (by positivity) hpos]
        linarith
      exact (not_lt_of_ge (hx m)) hlt
    · intro hx m
      change |f x| ≤ (m + 1 : ℝ)⁻¹
      rw [hx, abs_zero]
      positivity
  have ht := tendsto_measure_iInter_atTop hs hmono ⟨0, measure_ne_top μ _⟩
  rw [hinter, hzero] at ht
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨(m + 1 : ℝ)⁻¹, by positivity, hm⟩

end HolomorphicAnosov.Analysis.Regularity

