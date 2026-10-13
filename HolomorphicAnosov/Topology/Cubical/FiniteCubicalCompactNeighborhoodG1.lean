import Mathlib.Data.Finset.Max
import Mathlib.Topology.MetricSpace.ProperSpace
import HolomorphicAnosov.Topology.StandardDiskBoundaryFiniteCW

/-!
# Finite cubical neighborhoods of compact sets

Dold (1965), §5 Step 6, p.8. A finite cover by coordinate boxes has a common
finite endpoint grid. The cells lying in those boxes form the required subcomplex.
-/

noncomputable section
namespace HolomorphicAnosov.Cubical
open Set ClosedCoordinateCell
/-- A cell of the common finite endpoint grid, including its degenerate faces. -/
def endpointGridCell {N : ℕ} (E : Finset ℝ) (c : ClosedCoordinateCell N) : Prop :=
  ∀ i, c.lower i ∈ E ∧ c.upper i ∈ E ∧
    ∀ t ∈ E, ¬ (c.lower i < t ∧ t < c.upper i)

lemma endpointGridCell_face {N : ℕ} (E : Finset ℝ) {a c : ClosedCoordinateCell N}
    (hc : endpointGridCell E c) (ha : IsFace a c) : endpointGridCell E a := by
  intro i
  rcases ha i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩
  · simpa only [hl, hu] using hc i
  · rw [hl, hu]
    exact ⟨(hc i).1, (hc i).1, fun _ _ h ↦ (lt_asymm h.1 h.2)⟩
  · rw [hl, hu]
    exact ⟨(hc i).2.1, (hc i).2.1, fun _ _ h ↦ (lt_asymm h.1 h.2)⟩

lemma endpointGridCell_finite (N : ℕ) (E : Finset ℝ) :
    {c : ClosedCoordinateCell N | endpointGridCell E c}.Finite := by
  let f : {c : ClosedCoordinateCell N // endpointGridCell E c} →
      (Fin N → {t : ℝ // t ∈ E}) × (Fin N → {t : ℝ // t ∈ E}) :=
    fun c ↦ (fun i ↦ ⟨c.val.lower i, (c.property i).1⟩,
      fun i ↦ ⟨c.val.upper i, (c.property i).2.1⟩)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply ClosedCoordinateCell.eq_of_corners
    · funext i
      exact congrArg (fun p ↦ (p.1 i).val) h
    · funext i
      exact congrArg (fun p ↦ (p.2 i).val) h
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

lemma endpointInterval_inter_face (E : Finset ℝ) {a b c d : ℝ}
    (hc : c ∈ E) (hd : d ∈ E) (_hab : a ≤ b) (hcd : c ≤ d)
    (hgrid : ∀ t ∈ E, ¬ (a < t ∧ t < b))
    (hinter : max a c ≤ min b d) :
    (max a c = a ∧ min b d = b) ∨
      (max a c = a ∧ min b d = a) ∨
      (max a c = b ∧ min b d = b) := by
  by_cases hca : c ≤ a
  · rw [max_eq_left hca] at hinter ⊢
    by_cases hbd : b ≤ d
    · exact Or.inl ⟨rfl, min_eq_left hbd⟩
    · have hda : d ≤ a := le_of_not_gt fun had ↦ hgrid d hd ⟨had, lt_of_not_ge hbd⟩
      have had : a ≤ d := hinter.trans (min_le_right _ _)
      exact Or.inr (Or.inl ⟨rfl, (min_eq_right (le_of_not_ge hbd)).trans (le_antisymm hda had)⟩)
  · have hac : a < c := lt_of_not_ge hca
    have hbc : b ≤ c := le_of_not_gt fun hcb ↦ hgrid c hc ⟨hac, hcb⟩
    have hcb : c ≤ b := (le_max_right _ _).trans (hinter.trans (min_le_left _ _))
    have hcb' : c = b := le_antisymm hcb hbc
    exact Or.inr (Or.inr ⟨(max_eq_right hac.le).trans hcb', min_eq_left (hbc.trans hcd)⟩)

lemma endpointGrid_intersection (N : ℕ) (E : Finset ℝ) (a b : ClosedCoordinateCell N)
    (ha : endpointGridCell E a) (hb : endpointGridCell E b)
    (hn : (a.carrier ∩ b.carrier).Nonempty) :
    ∃ d, endpointGridCell E d ∧ IsFace d a ∧ IsFace d b ∧
      d.carrier = a.carrier ∩ b.carrier := by
  obtain ⟨x, hxa, hxb⟩ := hn
  have hinter (i : Fin N) : max (a.lower i) (b.lower i) ≤ min (a.upper i) (b.upper i) :=
    max_le (le_min (a.lower_le_upper i) ((hxa.1 i).trans (hxb.2 i)))
      (le_min ((hxb.1 i).trans (hxa.2 i)) (b.lower_le_upper i))
  let d : ClosedCoordinateCell N := {
    lower i := max (a.lower i) (b.lower i)
    upper i := min (a.upper i) (b.upper i)
    lower_le_upper := hinter }
  have hda : IsFace d a := fun i ↦ endpointInterval_inter_face E
    (hb i).1 (hb i).2.1 (a.lower_le_upper i) (b.lower_le_upper i) (ha i).2.2 (hinter i)
  have hdb : IsFace d b := by
    intro i
    simpa only [max_comm, min_comm] using endpointInterval_inter_face E
      (ha i).1 (ha i).2.1 (b.lower_le_upper i) (a.lower_le_upper i) (hb i).2.2
      (by simpa only [max_comm, min_comm] using hinter i)
  refine ⟨d, endpointGridCell_face E ha hda, hda, hdb, ?_⟩
  ext y
  change (∀ i, max (a.lower i) (b.lower i) ≤ y i) ∧
    (∀ i, y i ≤ min (a.upper i) (b.upper i)) ↔
    ((∀ i, a.lower i ≤ y i) ∧ (∀ i, y i ≤ a.upper i)) ∧
    ((∀ i, b.lower i ≤ y i) ∧ (∀ i, y i ≤ b.upper i))
  simp only [max_le_iff, le_min_iff, forall_and]
  tauto

lemma endpointGrid_bracket (E : Finset ℝ) {l x u : ℝ} (hl : l ∈ E) (hu : u ∈ E)
    (hlx : l ≤ x) (hxu : x ≤ u) :
    ∃ a ∈ E, ∃ b ∈ E, l ≤ a ∧ a ≤ x ∧ x ≤ b ∧ b ≤ u ∧
      ∀ t ∈ E, ¬ (a < t ∧ t < b) := by
  classical
  let L := E.filter (· ≤ x)
  let U := E.filter (x ≤ ·)
  have hL : L.Nonempty := ⟨l, Finset.mem_filter.mpr ⟨hl, hlx⟩⟩
  have hU : U.Nonempty := ⟨u, Finset.mem_filter.mpr ⟨hu, hxu⟩⟩
  let a := L.max' hL
  let b := U.min' hU
  have ha := Finset.mem_filter.mp (L.max'_mem hL)
  have hb := Finset.mem_filter.mp (U.min'_mem hU)
  refine ⟨a, ha.1, b, hb.1, L.le_max' l (Finset.mem_filter.mpr ⟨hl, hlx⟩),
    ha.2, hb.2, U.min'_le u (Finset.mem_filter.mpr ⟨hu, hxu⟩), ?_⟩
  intro t ht htt
  by_cases htx : t ≤ x
  · exact not_lt_of_ge (L.le_max' t (Finset.mem_filter.mpr ⟨ht, htx⟩)) htt.1
  · exact not_lt_of_ge (U.min'_le t (Finset.mem_filter.mpr ⟨ht, le_of_not_ge htx⟩)) htt.2

/-- Every point of an endpoint-aligned box lies in a grid cell contained in that box. -/
lemma endpointGrid_refines_box (N : ℕ) (E : Finset ℝ) (c : ClosedCoordinateCell N)
    (hc : ∀ i, c.lower i ∈ E ∧ c.upper i ∈ E) {x : Fin N → ℝ} (hx : x ∈ c.carrier) :
    ∃ d : ClosedCoordinateCell N, endpointGridCell E d ∧ x ∈ d.carrier ∧ d.carrier ⊆ c.carrier := by
  choose a ha b hb hla hax hxb hbu hgrid using
    fun i ↦ endpointGrid_bracket E (hc i).1 (hc i).2 (hx.1 i) (hx.2 i)
  let d : ClosedCoordinateCell N := ⟨a, b, fun i ↦ (hax i).trans (hxb i)⟩
  refine ⟨d, fun i ↦ ⟨ha i, hb i, hgrid i⟩, ⟨hax, hxb⟩, ?_⟩
  intro y hy
  exact ⟨fun i ↦ (hla i).trans (hy.1 i), fun i ↦ (hy.2 i).trans (hbu i)⟩

/-- The finite endpoint grid subdivides the surrounding cube literally. -/
def endpointGridSubdivision (N : ℕ) (E : Finset ℝ) (R : ℝ) (hR : 0 < R)
    (hE : ∀ t ∈ E, -R ≤ t ∧ t ≤ R) (hneg : -R ∈ E) (hpos : R ∈ E) :
    FiniteRectilinearSubdivision N where
  cube := ⟨fun _ ↦ -R, fun _ ↦ R, fun _ ↦ by linarith⟩
  cube_side := ⟨2 * R, by positivity, fun _ ↦ by dsimp; ring⟩
  cells := {c | endpointGridCell E c}
  finite_cells := endpointGridCell_finite N E
  faces _ hc _ hf := endpointGridCell_face E hc hf
  intersections a ha b hb hn := endpointGrid_intersection N E a b ha hb hn
  cover := by
    ext x
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, _, ⟨hc, rfl⟩, hx⟩
      exact ⟨fun i ↦ (hE (c.lower i) (hc i).1).1.trans (hx.1 i),
        fun i ↦ (hx.2 i).trans (hE (c.upper i) (hc i).2.1).2⟩
    · intro hx
      obtain ⟨d, hd, hxd, _⟩ := endpointGrid_refines_box N E
        ⟨fun _ ↦ -R, fun _ ↦ R, fun _ ↦ by linarith⟩ (fun _ ↦ ⟨hneg, hpos⟩) hx
      exact Set.mem_iUnion₂.mpr ⟨d, hd, hxd⟩

/-- Every finite family of coordinate boxes has a common finite cubical refinement. -/
lemma finite_boxes_cubical_refinement (N : ℕ) (B : Finset (ClosedCoordinateCell N)) :
    ∃ C : FiniteRectilinearSubdivision N, ∃ P : CubicalSubcomplex C,
      P.carrier = ⋃ c ∈ B, c.carrier := by
  classical
  let E₀ : Finset ℝ := B.biUnion fun c ↦ Finset.univ.image c.lower ∪ Finset.univ.image c.upper
  let R : ℝ := 1 + ∑ t ∈ E₀, |t|
  have hsum : 0 ≤ ∑ t ∈ E₀, |t| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hR : 0 < R := by dsimp [R]; linarith
  have hbound : ∀ t ∈ E₀, -R ≤ t ∧ t ≤ R := by
    intro t ht
    have ht' := Finset.single_le_sum (fun t (_ : t ∈ E₀) ↦ abs_nonneg t) ht
    have ha := (abs_le.mp (le_trans ht' (show (∑ t ∈ E₀, |t|) ≤ R by dsimp [R]; linarith)))
    exact ha
  let E := insert (-R) (insert R E₀)
  have hE : ∀ t ∈ E, -R ≤ t ∧ t ≤ R := by
    intro t ht
    simp only [E, Finset.mem_insert] at ht
    rcases ht with rfl | rfl | ht
    · constructor <;> linarith
    · constructor <;> linarith
    · exact hbound t ht
  have hneg : -R ∈ E := Finset.mem_insert_self _ _
  have hpos : R ∈ E := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  let C := endpointGridSubdivision N E R hR hE hneg hpos
  let P : CubicalSubcomplex C := {
    cells := {c | endpointGridCell E c ∧ ∃ b ∈ B, c.carrier ⊆ b.carrier}
    subset_cells := fun _ hc ↦ hc.1
    faces := by
      intro c hc d hd
      obtain ⟨b, hb, hcb⟩ := hc.2
      exact ⟨endpointGridCell_face E hc.1 hd, b, hb,
        (HolomorphicAnosov.StandardDiskBoundaryCW.face_subset hd).trans hcb⟩ }
  refine ⟨C, P, ?_⟩
  have hend (c : ClosedCoordinateCell N) (hc : c ∈ B) :
      ∀ i, c.lower i ∈ E ∧ c.upper i ∈ E := by
    intro i
    constructor
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨b, hb, hcb⟩ := hc.2
    exact Set.mem_iUnion₂.mpr ⟨b, hb, hcb hx⟩
  · intro hx
    obtain ⟨b, hb, hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨c, hc, hxc, hcb⟩ := endpointGrid_refines_box N E b (hend b hb) hx
    exact Set.mem_iUnion₂.mpr ⟨c, ⟨hc, b, hb, hcb⟩, hxc⟩

/-- A closed maximum-norm ball as a literal coordinate box. -/
def closedBallCell (N : ℕ) (x : Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r) : ClosedCoordinateCell N where
  lower i := x i - r
  upper i := x i + r
  lower_le_upper _ := by linarith

lemma closedBallCell_carrier (N : ℕ) (x : Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    (closedBallCell N x r hr).carrier = Metric.closedBall x r := by
  ext y
  change ((∀ i, x i - r ≤ y i) ∧ (∀ i, y i ≤ x i + r)) ↔ dist y x ≤ r
  rw [dist_pi_le_iff hr]
  constructor
  · rintro ⟨hl, hu⟩ i
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hl i, hu i]
  · intro h
    have hi (i : Fin N) := abs_le.mp (show |y i - x i| ≤ r by simpa only [Real.dist_eq] using h i)
    exact ⟨fun i ↦ by linarith [(hi i).1], fun i ↦ by linarith [(hi i).2]⟩

/-- Compactness supplies finitely many closed coordinate boxes inside an open set. -/
lemma compact_covered_by_finite_boxes (N : ℕ) (K O : Set (Fin N → ℝ))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ B : Finset (ClosedCoordinateCell N), K ⊆ ⋃ c ∈ B, c.carrier ∧
      (⋃ c ∈ B, c.carrier) ⊆ O := by
  classical
  have hr : ∀ x : K, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x.val r ⊆ O :=
    fun x ↦ Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds (hKO x.property))
  choose r hr hball using hr
  have hcover : K ⊆ ⋃ x : K, Metric.ball x.val (r x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K ↦ Metric.ball x.val (r x))
    (fun _ ↦ Metric.isOpen_ball) hcover
  let c (x : K) := closedBallCell N x.val (r x) (hr x).le
  refine ⟨s.image c, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    refine Set.mem_iUnion₂.mpr ⟨c y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    rw [closedBallCell_carrier]
    exact Metric.ball_subset_closedBall hxy
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact hball y (by rwa [closedBallCell_carrier] at hxb)

/-- Every compact subset of an open coordinate-space set lies in a finite cubical
subcomplex contained in that open set.

Source: Dold (1965), §5 Step 6, p.8. Choose closed coordinate boxes inside the open
set whose interiors cover the compact set, then take a finite subcover. Collect
all endpoint coordinates and add two endpoints of a surrounding cube. The adjacent
intervals in this finite ordered set give a finite subdivision; their intersections
are whole common faces. Selecting cells contained in one of the original boxes
forms a subcomplex with exactly the union of those boxes as its carrier. -/
theorem finite_cubical_compact_neighborhood (N : ℕ) (K O : Set (Fin N → ℝ))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ C : FiniteRectilinearSubdivision N, ∃ P : CubicalSubcomplex C,
      K ⊆ P.carrier ∧ P.carrier ⊆ O := by
  obtain ⟨B, hKB, hBO⟩ := compact_covered_by_finite_boxes N K O hK hO hKO
  obtain ⟨C, P, hP⟩ := finite_boxes_cubical_refinement N B
  exact ⟨C, P, hP ▸ hKB, hP ▸ hBO⟩

end HolomorphicAnosov.Cubical

