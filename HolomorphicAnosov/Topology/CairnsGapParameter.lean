import HolomorphicAnosov.Topology.CairnsNormalizedCircleGap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

namespace HolomorphicAnosov.Topology.Plane.CairnsCircleGap
open Set

/-- A proper angular gap is parametrized injectively by its affine angular path.
Its endpoints and range are precisely the gap's declared endpoints and closed arc.
Source: Cairns (1951), §3(D,E), pp.862–863; affine interval parametrization followed
by the exponential, which is injective on intervals shorter than one full turn. -/
theorem parameter_embedding_range (g : CairnsCircleGap) :
    _root_.Topology.IsEmbedding g.parameter ∧ range g.parameter = g.closedArc ∧
      g.parameter 0 = g.first ∧ g.parameter 1 = g.last := by
  let f : unitInterval → ℝ := fun t ↦ g.start + (g.stop - g.start) * (t : ℝ)
  have hmem (t : unitInterval) : f t ∈ Icc g.start g.stop := by
    dsimp [f]
    constructor <;> nlinarith [t.property.1, t.property.2, g.start_lt_stop]
  have hinj : Function.Injective g.parameter := by
    intro s t h
    have he := Circle.exp_injOn_Icc g.shorter_than_turn (hmem s) (hmem t) h
    apply Subtype.ext
    dsimp [f] at he
    nlinarith [g.start_lt_stop]
  have hcont : Continuous g.parameter := by
    unfold parameter
    exact Circle.exp.continuous.comp (by fun_prop)
  refine ⟨(hcont.isClosedEmbedding hinj).isEmbedding, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      exact ⟨f t, hmem t, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      let t : unitInterval := ⟨(x - g.start) / (g.stop - g.start),
        (div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr g.start_lt_stop).le),
        (div_le_one (sub_pos.mpr g.start_lt_stop)).mpr (by linarith [hx.2])⟩
      refine ⟨t, ?_⟩
      unfold parameter
      congr 1
      dsimp [t]
      rw [mul_div_cancel₀ _ (sub_pos.mpr g.start_lt_stop).ne']
      ring
  · simp [parameter, first]
  · simp [parameter, last]

end HolomorphicAnosov.Topology.Plane.CairnsCircleGap

namespace HolomorphicAnosov.Topology.Plane.CairnsCircleGap
open Set

/-- The two affine parameters on complementary full-turn gaps cover the circle and
meet only at their common endpoints. -/
theorem opposite_parameter_cover_inter
    (g₁ g₂ : CairnsCircleGap)
    (hstart : g₂.start = g₁.stop)
    (hstop : g₂.stop = g₁.start + 2 * Real.pi)
    (hfirst : g₂.first = g₁.last)
    (hlast : g₂.last = g₁.first) :
    range g₁.parameter ∪ range g₂.parameter = (Set.univ : Set Circle) ∧
      range g₁.parameter ∩ range g₂.parameter = {g₁.first, g₁.last} := by
  have hp1 := parameter_embedding_range g₁
  have hp2 := parameter_embedding_range g₂
  have hr1 : range g₁.parameter = Circle.exp '' Icc g₁.start g₁.stop := by
    simpa [CairnsCircleGap.closedArc] using hp1.2.1
  have hr2 : range g₂.parameter = Circle.exp '' Icc g₂.start g₂.stop := by
    simpa [CairnsCircleGap.closedArc] using hp2.2.1
  have hinterval : Icc g₁.start g₁.stop ∪ Icc g₂.start g₂.stop =
      Icc g₁.start (g₁.start + 2 * Real.pi) := by
    rw [hstart, hstop]
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, by linarith [hx.2, g₁.shorter_than_turn, Real.pi_pos]⟩
      · exact ⟨by linarith [hx.1, g₁.start_lt_stop], hx.2⟩
    · intro hx
      by_cases hxb : x ≤ g₁.stop
      · exact Or.inl ⟨hx.1, hxb⟩
      · exact Or.inr ⟨le_of_not_ge hxb, hx.2⟩
  have hcover : range g₁.parameter ∪ range g₂.parameter = (Set.univ : Set Circle) := by
    rw [hr1, hr2, ← image_union, hinterval]
    rw [Circle.periodic_exp.image_Icc (by positivity) g₁.start]
    exact Circle.exp_surjective.range_eq
  have hmeet : range g₁.parameter ∩ range g₂.parameter = {g₁.first, g₁.last} := by
    ext z
    constructor
    · intro hz
      rw [hr1, hr2] at hz
      rcases hz with ⟨⟨x, hx, hzx⟩, ⟨y, hy, hzy⟩⟩
      have he : Circle.exp x = Circle.exp y := hzx.trans hzy.symm
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp he
      have hm0r : (m : ℝ) ≤ 0 := by
        have hxy : x ≤ y := le_trans hx.2 (by simpa [hstart] using hy.1)
        nlinarith [hm, Real.pi_pos]
      have hmneg1r : (-1 : ℝ) ≤ (m : ℝ) := by
        have hxa : g₁.start ≤ x := hx.1
        have hyd : y ≤ g₁.start + 2 * Real.pi := by simpa [hstop] using hy.2
        nlinarith [hm, Real.pi_pos]
      have hm0 : m ≤ 0 := by exact_mod_cast hm0r
      have hmneg1 : (-1 : ℤ) ≤ m := by exact_mod_cast hmneg1r
      have hmcases : m = -1 ∨ m = 0 := by omega
      rcases hmcases with hmneg1 | hmzero
      · have hm' : x = y - 2 * Real.pi := by
          rw [hmneg1] at hm
          norm_num at hm ⊢
          exact hm
        have hxa : x = g₁.start := by
          have hyd : y ≤ g₁.start + 2 * Real.pi := by simpa [hstop] using hy.2
          nlinarith [hm', hx.1, hyd, Real.pi_pos]
        have hxe : z = g₁.first := by
          rw [← hzx, hxa]
          rfl
        simp [hxe]
      · have hm' : x = y := by
          rw [hmzero] at hm
          simpa using hm
        have hxb : x = g₁.stop := by
          have hby : g₁.stop ≤ y := by simpa [hstart] using hy.1
          nlinarith [hm', hx.2, hby]
        have hze : z = g₁.last := by
          rw [← hzx, hxb]
          rfl
        simp [hze]
    · intro hz
      simp only [mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · have hz1 : g₁.first ∈ range g₁.parameter := by
          rw [hr1]
          exact ⟨g₁.start, ⟨le_rfl, le_of_lt g₁.start_lt_stop⟩, rfl⟩
        have hz2 : g₁.first ∈ range g₂.parameter := by
          rw [hr2, ← hlast]
          exact ⟨g₂.stop, ⟨le_of_lt g₂.start_lt_stop, le_rfl⟩, rfl⟩
        exact ⟨hz1, hz2⟩
      · have hz1 : g₁.last ∈ range g₁.parameter := by
          rw [hr1]
          exact ⟨g₁.stop, ⟨le_of_lt g₁.start_lt_stop, le_rfl⟩, rfl⟩
        have hz2 : g₁.last ∈ range g₂.parameter := by
          rw [hr2, ← hfirst]
          exact ⟨g₂.start, ⟨le_rfl, le_of_lt g₂.start_lt_stop⟩, rfl⟩
        exact ⟨hz1, hz2⟩
  exact ⟨hcover, hmeet⟩

end HolomorphicAnosov.Topology.Plane.CairnsCircleGap

namespace HolomorphicAnosov.Topology.Plane.CairnsCircleGap
open Set

/-- The opposite gap can be reversed to obtain the common endpoint orientation
used by the chord-sector theorem, without changing its range. -/
theorem opposite_parameter_chord_arc_data
    (g₁ g₂ : CairnsCircleGap)
    (hstart : g₂.start = g₁.stop)
    (hstop : g₂.stop = g₁.start + 2 * Real.pi)
    (hfirst : g₂.first = g₁.last)
    (hlast : g₂.last = g₁.first) :
    Topology.IsEmbedding g₁.parameter ∧
      Topology.IsEmbedding (fun t : unitInterval => g₂.parameter (unitInterval.symm t)) ∧
      g₁.parameter 0 = g₁.first ∧ g₁.parameter 1 = g₁.last ∧
      (fun t : unitInterval => g₂.parameter (unitInterval.symm t)) 0 = g₁.first ∧
      (fun t : unitInterval => g₂.parameter (unitInterval.symm t)) 1 = g₁.last ∧
      range g₁.parameter ∪ range (fun t : unitInterval => g₂.parameter (unitInterval.symm t)) = Set.univ ∧
      range g₁.parameter ∩ range (fun t : unitInterval => g₂.parameter (unitInterval.symm t)) =
        {g₁.first, g₁.last} := by
  have hp1 := parameter_embedding_range g₁
  have hp2 := parameter_embedding_range g₂
  have hrev : Topology.IsEmbedding (fun t : unitInterval => g₂.parameter (unitInterval.symm t)) := by
    simpa only [Function.comp_def, unitInterval.symmHomeomorph_apply] using hp2.1.comp unitInterval.symmHomeomorph.isEmbedding
  have hrevRange : range (fun t : unitInterval => g₂.parameter (unitInterval.symm t)) =
      range g₂.parameter := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp⟩
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp⟩
  obtain ⟨hcover, hmeet⟩ := opposite_parameter_cover_inter g₁ g₂ hstart hstop hfirst hlast
  refine ⟨hp1.1, hrev, hp1.2.2.1, hp1.2.2.2, ?_, ?_, ?_, ?_⟩
  · simpa [hlast] using hp2.2.2.2
  · simpa [hfirst] using hp2.2.2.1
  · simpa [hrevRange] using hcover
  · simpa [hrevRange] using hmeet

end HolomorphicAnosov.Topology.Plane.CairnsCircleGap

namespace HolomorphicAnosov.Topology.Plane.CairnsCircleGap
open Set

/-- The same opposite-gap data with the first parameter reversed gives the
common endpoint orientation for the second gap. -/
theorem opposite_parameter_chord_arc_data_reverse
    (g₁ g₂ : CairnsCircleGap)
    (hstart : g₂.start = g₁.stop)
    (hstop : g₂.stop = g₁.start + 2 * Real.pi)
    (hfirst : g₂.first = g₁.last)
    (hlast : g₂.last = g₁.first) :
    Topology.IsEmbedding g₂.parameter ∧
      Topology.IsEmbedding (fun t : unitInterval => g₁.parameter (unitInterval.symm t)) ∧
      g₂.parameter 0 = g₂.first ∧ g₂.parameter 1 = g₂.last ∧
      (fun t : unitInterval => g₁.parameter (unitInterval.symm t)) 0 = g₂.first ∧
      (fun t : unitInterval => g₁.parameter (unitInterval.symm t)) 1 = g₂.last ∧
      range g₂.parameter ∪ range (fun t : unitInterval => g₁.parameter (unitInterval.symm t)) = Set.univ ∧
      range g₂.parameter ∩ range (fun t : unitInterval => g₁.parameter (unitInterval.symm t)) =
        {g₂.first, g₂.last} := by
  have hp1 := parameter_embedding_range g₁
  have hp2 := parameter_embedding_range g₂
  have hrev : Topology.IsEmbedding (fun t : unitInterval => g₁.parameter (unitInterval.symm t)) := by
    simpa only [Function.comp_def, unitInterval.symmHomeomorph_apply] using hp1.1.comp unitInterval.symmHomeomorph.isEmbedding
  have hrevRange : range (fun t : unitInterval => g₁.parameter (unitInterval.symm t)) =
      range g₁.parameter := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp⟩
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp⟩
  obtain ⟨hcover, hmeet⟩ := opposite_parameter_cover_inter g₁ g₂ hstart hstop hfirst hlast
  refine ⟨hp2.1, hrev, hp2.2.2.1, hp2.2.2.2, ?_, ?_, ?_, ?_⟩
  · simpa [hfirst] using hp1.2.2.2
  · simpa [hlast] using hp1.2.2.1
  · rw [hrevRange]
    simpa [union_comm] using hcover
  · rw [hrevRange]
    calc
      range g₂.parameter ∩ range g₁.parameter = range g₁.parameter ∩ range g₂.parameter := inter_comm _ _
      _ = {g₁.first, g₁.last} := hmeet
      _ = {g₂.first, g₂.last} := by rw [hfirst, hlast]; exact Set.pair_comm _ _

end HolomorphicAnosov.Topology.Plane.CairnsCircleGap
