import Mathlib.Topology.CWComplex.Classical.Finite
import HolomorphicAnosov.Topology.Cubical.CellBoundarySubsetSkeleton
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Logic.Equiv.PartialEquiv
import HolomorphicAnosov.Topology.Cubical.FiniteRectilinearSubdivision
import HolomorphicAnosov.Topology.Cubical.CoordinateCellNormalization
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Finite CW structure on the original rectilinear subdivision

Source: Hatcher, Algebraic Topology, Appendix A.2, p.521. The coordinate verification
below is agent-written: the common-face condition makes the relative open boxes
pairwise disjoint, and replacing endpoint coordinates by singleton intervals gives
an open cell containing each point of a closed box.
-/

namespace HolomorphicAnosov.Cubical
open Set ClosedCoordinateCell

namespace ClosedCoordinateCell

/-- The relative open box: active coordinates are strictly between their endpoints,
and inactive coordinates keep their prescribed value. Source: Hatcher A.2, p.521,
coordinate-cell specialization. This definition includes zero-dimensional cells. -/
def openCarrier {N : ℕ} (c : ClosedCoordinateCell N) : Set (Fin N → ℝ) :=
  {x | x ∈ c.carrier ∧ ∀ i, c.lower i < c.upper i → c.lower i < x i ∧ x i < c.upper i}

lemma eq_of_corners {N : ℕ} {a b : ClosedCoordinateCell N}
    (hl : a.lower = b.lower) (hu : a.upper = b.upper) : a = b := by
  cases a
  cases b
  cases hl
  cases hu
  rfl

/-- A face containing a relative interior point is the entire cell.
Source: the face-interior condition in Hatcher A.2, p.521. An endpoint face cannot
contain a point strictly between the endpoints of an active coordinate. Every
remaining coordinate retains the whole original interval, including singleton
intervals, so the lower and upper corners coincide. -/
theorem IsFace.eq_of_mem_openCarrier {N : ℕ} {a b : ClosedCoordinateCell N}
    (h : IsFace a b) {x : Fin N → ℝ} (ha : x ∈ a.carrier)
    (hb : x ∈ b.openCarrier) : a = b := by
  have hcoord (i : Fin N) : a.lower i = b.lower i ∧ a.upper i = b.upper i := by
    rcases h i with hfull | hlow | hupp
    · exact hfull
    · by_cases hi : b.lower i < b.upper i
      · have hx := (hb.2 i hi).1
        have hx' := ha.2 i
        rw [hlow.2] at hx'
        exact False.elim (not_lt_of_ge hx' hx)
      · have heq := le_antisymm (b.lower_le_upper i) (le_of_not_gt hi)
        exact ⟨hlow.1, hlow.2.trans heq⟩
    · by_cases hi : b.lower i < b.upper i
      · have hx := (hb.2 i hi).2
        have hx' := ha.1 i
        rw [hupp.1] at hx'
        exact False.elim (not_lt_of_ge hx' hx)
      · have heq := le_antisymm (b.lower_le_upper i) (le_of_not_gt hi)
        exact ⟨hupp.1.trans heq.symm, hupp.2⟩
  exact eq_of_corners (funext fun i ↦ (hcoord i).1) (funext fun i ↦ (hcoord i).2)

/-- Every point of a closed box lies in the relative open box of one of its faces.
Source: Hatcher A.2, p.521, coordinate verification. In each coordinate already
at an endpoint collapse the interval to that endpoint; retain every other interval.
The original inequalities then become strict in all remaining active directions. -/
theorem exists_face_mem_openCarrier {N : ℕ} (c : ClosedCoordinateCell N)
    {x : Fin N → ℝ} (hx : x ∈ c.carrier) :
    ∃ a : ClosedCoordinateCell N, IsFace a c ∧ x ∈ a.openCarrier := by
  classical
  let endpoint (i : Fin N) := x i = c.lower i ∨ x i = c.upper i
  let a : ClosedCoordinateCell N :=
    ⟨fun i ↦ if endpoint i then x i else c.lower i,
      fun i ↦ if endpoint i then x i else c.upper i, by
        intro i
        dsimp only
        split_ifs <;> [exact le_rfl; exact c.lower_le_upper i]⟩
  refine ⟨a, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : endpoint i
    · rcases hi with hi | hi
      · right; left; simp [a, endpoint, hi]
      · right; right; simp [a, endpoint, hi]
    · left; simp [a, hi]
  · constructor <;> intro i <;> dsimp only [a] <;> split_ifs
    · exact le_rfl
    · exact hx.1 i
    · exact le_rfl
    · exact hx.2 i
  · intro i hi
    by_cases he : endpoint i
    · simp [a, he] at hi
    · have hl : x i ≠ c.lower i := fun h ↦ he (Or.inl h)
      have hu : x i ≠ c.upper i := fun h ↦ he (Or.inr h)
      change (if endpoint i then x i else c.lower i) < x i ∧
        x i < (if endpoint i then x i else c.upper i)
      simp only [ite_eq_right he]
      exact ⟨lt_of_le_of_ne (hx.1 i) hl.symm, lt_of_le_of_ne (hx.2 i) hu⟩

end ClosedCoordinateCell

/-- Distinct cells of a rectilinear subdivision have disjoint relative open boxes.
Source: Hatcher A.2(i), p.521. Their nonempty closed intersection is a common face.
A point in both relative interiors forces that common face to equal both cells. -/
theorem finiteSubdivision_openCarrier_disjoint {N : ℕ}
    (K : FiniteRectilinearSubdivision N) {a b : ClosedCoordinateCell N}
    (ha : a ∈ K.cells) (hb : b ∈ K.cells) (hab : a ≠ b) :
    Disjoint a.openCarrier b.openCarrier := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  obtain ⟨d, _, hda, hdb, hd⟩ := K.intersections a ha b hb ⟨x, hxa.1, hxb.1⟩
  have hxd : x ∈ d.carrier := by rw [hd]; exact ⟨hxa.1, hxb.1⟩
  exact hab ((hda.eq_of_mem_openCarrier hxd hxa).symm.trans
    (hdb.eq_of_mem_openCarrier hxd hxb))

/-- The original relative open boxes partition the original cube, including all
lower-dimensional faces. Source: Hatcher A.2(i), p.521. The closed-cell cover
provides a box containing each point, and the endpoint-face construction gives
an original face whose relative open box contains it. Disjointness gives uniqueness. -/
theorem finiteSubdivision_openCarrier_partition {N : ℕ}
    (K : FiniteRectilinearSubdivision N) {x : Fin N → ℝ} (hx : x ∈ K.cube.carrier) :
    ∃! c : {c : ClosedCoordinateCell N // c ∈ K.cells}, x ∈ c.val.openCarrier := by
  rw [← K.cover] at hx
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨a, haface, hxa⟩ := c.exists_face_mem_openCarrier hxc
  refine ⟨⟨a, K.faces c hc a haface⟩, hxa, ?_⟩
  intro b hxb
  apply Subtype.ext
  by_contra hne
  exact Set.disjoint_left.mp (finiteSubdivision_openCarrier_disjoint K b.property
    (K.faces c hc a haface) hne) hxb hxa


set_option maxHeartbeats 600000 in
/-- A closed coordinate cell has a characteristic map from the closed maximum-norm
unit disk in its actual dimension, with exactly its relative open box as open-cell
image. Source: Hatcher Appendix A.2, p.521, coordinate specialization. Normalize
active intervals to [-1,1], inactive coordinates to zero, and enumerate the active
coordinates. The inverse normalization restricted to the active coordinate plane
is the map. The closed and open sup-norm balls are precisely its weak and strict
coordinate inequalities; its inverse is active-coordinate projection. -/
theorem coordinate_cell_characteristic_map {N n : ℕ} (c : ClosedCoordinateCell N)
    (hd : c.dimension = n) :
    ∃ χ : PartialEquiv (Fin n → ℝ) (Fin N → ℝ),
      χ.source = Metric.ball 0 1 ∧
      χ.target = c.openCarrier ∧
      (∀ u, χ.symm (χ u) = u) ∧
      Continuous χ ∧ Continuous χ.symm ∧
      χ '' Metric.closedBall 0 1 = c.carrier ∧
      χ '' Metric.ball 0 1 = c.openCarrier := by
  classical
  obtain ⟨e, hecell, hefaces⟩ := coordinate_cell_normalization c
  have hcard : Fintype.card {i : Fin N // c.lower i < c.upper i} = n := by
    calc
      _ = Nat.card {i : Fin N // c.lower i < c.upper i} := Nat.card_eq_fintype_card.symm
      _ = c.dimension := Nat.card_coe_set_eq _
      _ = n := hd
  let aeq := Fintype.equivFinOfCardEq hcard
  let relabel := Homeomorph.piCongrLeft (Y := fun _ : Fin n ↦ ℝ) aeq
  let E := e.trans (relabel.prodCongr (Homeomorph.refl
    ({i : Fin N // ¬ c.lower i < c.upper i} → ℝ)))
  have hcoord (x : Fin N → ℝ) (j : Fin n) :
      (E x).1 j = (e x).1 (aeq.symm j) := by
    simp [E, relabel, Homeomorph.piCongrLeft_apply]
  have hclosed (x : Fin N → ℝ) :
      x ∈ c.carrier ↔ ‖(E x).1‖ ≤ 1 ∧ (E x).2 = 0 := by
    rw [hecell x, pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨fun j ↦ ?_, hb⟩
      simpa only [hcoord, Real.norm_eq_abs, abs_le] using ha (aeq.symm j)
    · rintro ⟨ha, hb⟩
      refine ⟨fun i ↦ ?_, hb⟩
      have hi := ha (aeq i)
      simpa only [hcoord, Equiv.symm_apply_apply, Real.norm_eq_abs, abs_le] using hi
  have hopen (x : Fin N → ℝ) :
      x ∈ c.openCarrier ↔ ‖(E x).1‖ < 1 ∧ (E x).2 = 0 := by
    constructor
    · intro hx
      obtain ⟨hbound, hz⟩ := (hclosed x).mp hx.1
      refine ⟨(pi_norm_lt_iff zero_lt_one).mpr fun j ↦ ?_, hz⟩
      have hle := (norm_le_pi_norm ((E x).1) j).trans hbound
      apply lt_of_le_of_ne hle
      intro heq
      have habs : |(e x).1 (aeq.symm j)| = 1 := by
        simpa only [hcoord, Real.norm_eq_abs] using heq
      have hendpoint : ∃ i, (e x).1 i = -1 ∨ (e x).1 i = 1 := by
        refine ⟨aeq.symm j, ?_⟩
        rcases le_total 0 ((e x).1 (aeq.symm j)) with h | h
        · right; simpa only [abs_of_nonneg h] using habs
        · left; rw [abs_of_nonpos h] at habs; linarith
      obtain ⟨i, hi, hxi⟩ := (hefaces x).mpr hendpoint
      rcases hxi with hxi | hxi
      · exact (ne_of_gt (hx.2 i hi).1) hxi
      · exact (ne_of_lt (hx.2 i hi).2) hxi
    · rintro ⟨hnorm, hz⟩
      have hx := (hclosed x).mpr ⟨hnorm.le, hz⟩
      refine ⟨hx, fun i hi ↦ ?_⟩
      have hne : ¬ (x i = c.lower i ∨ x i = c.upper i) := by
        intro hxi
        obtain ⟨j, hj⟩ := (hefaces x).mp ⟨i, hi, hxi⟩
        have hlt := (pi_norm_lt_iff zero_lt_one).mp hnorm (aeq j)
        simp only [hcoord, Equiv.symm_apply_apply] at hlt
        rcases hj with hj | hj <;> simp only [hj, Real.norm_eq_abs, abs_neg, abs_one, lt_self_iff_false] at hlt
      exact ⟨lt_of_le_of_ne (hx.1 i) (fun h ↦ hne (Or.inl h.symm)),
        lt_of_le_of_ne (hx.2 i) (fun h ↦ hne (Or.inr h))⟩
  let χ : PartialEquiv (Fin n → ℝ) (Fin N → ℝ) :=
    { toFun := fun u ↦ E.symm (u, 0)
      invFun := fun x ↦ (E x).1
      source := Metric.ball 0 1
      target := c.openCarrier
      map_source' := by
        intro u hu
        apply (hopen _).mpr
        simpa only [Homeomorph.apply_symm_apply, Metric.mem_ball, dist_zero_right] using
          And.intro hu (rfl : (0 : {i : Fin N // ¬ c.lower i < c.upper i} → ℝ) = 0)
      map_target' := by
        intro x hx
        simpa only [Metric.mem_ball, dist_zero_right] using ((hopen x).mp hx).1
      left_inv' := by intro u _; simp only [Homeomorph.apply_symm_apply]
      right_inv' := by
        intro x hx
        have hz := ((hopen x).mp hx).2
        calc
          E.symm ((E x).1, 0) = E.symm (E x) := by rw [← hz]
          _ = x := E.symm_apply_apply x }
  refine ⟨χ, rfl, rfl, (fun u ↦ by change (E (E.symm (u, 0))).1 = u; simp),
    E.symm.continuous.comp (continuous_id.prodMk continuous_const),
    continuous_fst.comp E.continuous, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      apply (hclosed _).mpr
      change ‖(E (E.symm (u, 0))).1‖ ≤ 1 ∧ (E (E.symm (u, 0))).2 = 0
      simpa only [Homeomorph.apply_symm_apply, Metric.mem_closedBall, dist_zero_right] using
        And.intro hu (rfl : (0 : {i : Fin N // ¬ c.lower i < c.upper i} → ℝ) = 0)
    · intro hx
      obtain ⟨hbound, hz⟩ := (hclosed x).mp hx
      refine ⟨(E x).1, ?_, ?_⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using hbound
      · change E.symm ((E x).1, 0) = x
        rw [← hz]
        exact E.symm_apply_apply x
  · exact χ.image_source_eq_target


set_option maxHeartbeats 600000 in
/-- The original finite rectilinear subdivision carries a native finite CW structure
whose closed and open cells are exactly the original boxes and relative open boxes.
Source: Hatcher Appendix A.2, p.521. Use the affine characteristic maps on the
original dimension-indexed cell family. Open boxes are disjoint by the common-face
axiom; sphere points map to endpoint faces of smaller dimension. The closed images
cover the original cube. Mathlib's finite CW constructor then supplies the weak
topology from finitely many compact characteristic images. No carrier is replaced. -/
theorem finiteSubdivision_cwStructure {N : ℕ} (K : FiniteRectilinearSubdivision N) :
    ∃ cw : _root_.Topology.CWComplex K.cube.carrier,
      letI := cw
      _root_.Topology.RelCWComplex.Finite K.cube.carrier ∧
      ∃ index : ∀ n, {c : ClosedCoordinateCell N // c ∈ K.cells ∧ c.dimension = n} ≃
          _root_.Topology.RelCWComplex.cell K.cube.carrier n,
        ∀ n c,
          _root_.Topology.RelCWComplex.closedCell (C := K.cube.carrier) n (index n c) =
            c.val.carrier ∧
          _root_.Topology.RelCWComplex.openCell (C := K.cube.carrier) n (index n c) =
            c.val.openCarrier := by
  classical
  let cell (n : ℕ) := {c : ClosedCoordinateCell N // c ∈ K.cells ∧ c.dimension = n}
  have hfinite (n : ℕ) : Finite (cell n) :=
    (K.finite_cells.subset (fun _ h ↦ h.1)).to_subtype
  have hempty : ∀ᶠ n in Filter.atTop, IsEmpty (cell n) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨N + 1, fun n hn ↦ ⟨fun c ↦ ?_⟩⟩
    have hdim : c.val.dimension ≤ N := by
      simpa [ClosedCoordinateCell.dimension] using
        ({i : Fin N | c.val.lower i < c.val.upper i}.ncard_le_card)
    have := c.property.2
    omega
  choose χ hsource htarget hleft hcont hinv hclosed hopen using
    (fun n (c : cell n) ↦ coordinate_cell_characteristic_map c.val c.property.2)
  have hdisjoint : (univ : Set (Σ n, cell n)).PairwiseDisjoint
      (fun nc ↦ χ nc.1 nc.2 '' Metric.ball 0 1) := by
    intro a _ b _ hab
    change Disjoint (χ a.1 a.2 '' Metric.ball 0 1) (χ b.1 b.2 '' Metric.ball 0 1)
    rw [hopen, hopen]
    apply finiteSubdivision_openCarrier_disjoint K a.2.property.1 b.2.property.1
    intro heq
    apply hab
    rcases a with ⟨n, a⟩
    rcases b with ⟨m, b⟩
    have hnm : n = m := a.property.2.symm.trans (heq ▸ b.property.2)
    subst m
    have hab' : a = b := Subtype.ext heq
    subst b
    rfl
  have hattach (n : ℕ) (c : cell n) :
      MapsTo (χ n c) (Metric.sphere 0 1)
        (⋃ (m < n) (b : cell m), χ m b '' Metric.closedBall 0 1) := by
    intro u hu
    have huclosed : u ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
      Metric.sphere_subset_closedBall hu
    have hxc : χ n c u ∈ c.val.carrier := by
      rw [← hclosed n c]
      exact mem_image_of_mem _ huclosed
    have hxnot : χ n c u ∉ c.val.openCarrier := by
      intro hx
      have hin : (χ n c).symm (χ n c u) ∈ (χ n c).source :=
        (χ n c).map_target ((htarget n c).symm ▸ hx)
      rw [hleft, hsource] at hin
      exact (Metric.sphere_disjoint_ball.notMem_of_mem_left hu) hin
    have hboundary : ∃ i : Fin N, c.val.lower i < c.val.upper i ∧
        (χ n c u i = c.val.lower i ∨ χ n c u i = c.val.upper i) := by
      by_contra h
      apply hxnot
      refine ⟨hxc, fun i hi ↦ ?_⟩
      have hne : ¬ (χ n c u i = c.val.lower i ∨ χ n c u i = c.val.upper i) :=
        fun hx ↦ h ⟨i, hi, hx⟩
      exact ⟨lt_of_le_of_ne (hxc.1 i) (fun h ↦ hne (Or.inl h.symm)),
        lt_of_le_of_ne (hxc.2 i) (fun h ↦ hne (Or.inr h))⟩
    have hn : n ≠ 0 := by
      intro hn
      obtain ⟨i, hi, _⟩ := hboundary
      have : 0 < c.val.dimension := (Set.ncard_pos (Set.toFinite _)).mpr ⟨i, hi⟩
      omega
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hs := cell_boundary_subset_skeleton K q c.val c.property.1 c.property.2
      ⟨hxc, hboundary⟩
    -- Unfold the literal skeletal union to retain the original cell witness.
    simp only [FiniteRectilinearSubdivision.skeleton, mem_iUnion] at hs
    obtain ⟨b, hb, hdim, hxb⟩ := hs
    refine mem_iUnion.mpr ⟨b.dimension, mem_iUnion.mpr ⟨by omega,
      mem_iUnion.mpr ⟨⟨b, hb, rfl⟩, ?_⟩⟩⟩
    rw [hclosed]
    exact hxb
  have hcover : (⋃ n, ⋃ c : cell n, χ n c '' Metric.closedBall 0 1) = K.cube.carrier := by
    rw [← K.cover]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, c, hx⟩
      exact ⟨c.val, c.property.1, (hclosed n c) ▸ hx⟩
    · rintro ⟨c, hc, hx⟩
      refine ⟨c.dimension, ⟨c, hc, rfl⟩, ?_⟩
      rw [hclosed]
      exact hx
  let cw := _root_.Topology.CWComplex.mkFinite K.cube.carrier cell χ hempty hfinite
    hsource (fun n c ↦ (hcont n c).continuousOn)
    (fun n c ↦ (hinv n c).continuousOn) hdisjoint hattach hcover
  exact ⟨cw, _root_.Topology.CWComplex.finite_mkFinite K.cube.carrier cell χ hempty hfinite
    hsource (fun n c ↦ (hcont n c).continuousOn)
    (fun n c ↦ (hinv n c).continuousOn) hdisjoint hattach hcover,
    (fun n ↦ Equiv.refl (cell n)), fun n c ↦ ⟨hclosed n c, hopen n c⟩⟩

end HolomorphicAnosov.Cubical



