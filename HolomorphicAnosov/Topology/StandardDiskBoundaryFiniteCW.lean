import HolomorphicAnosov.Topology.Cubical.SubcomplexCWStructureG15

/-!
# Finite CW structure on a standard disk boundary

Source: Hatcher, Algebraic Topology, Appendix A.2 p.521. The native standard
disk uses the maximum norm. Its boundary is the union of proper coordinate
faces of the cube [-1,1]^N, so the existing coordinate-cell construction gives
a finite CW structure with every cell dimension strictly less than N.
-/

noncomputable section
namespace HolomorphicAnosov.StandardDiskBoundaryCW
open Set _root_.Topology Cubical Cubical.ClosedCoordinateCell

private def cube (N : ℕ) : ClosedCoordinateCell N where
  lower _ := -1
  upper _ := 1
  lower_le_upper _ := by norm_num

private theorem face_trans {N : ℕ} {a b c : ClosedCoordinateCell N}
    (hab : IsFace a b) (hbc : IsFace b c) : IsFace a c := by
  intro i
  rcases hab i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
    rcases hbc i with ⟨hl', hu'⟩ | ⟨hl', hu'⟩ | ⟨hl', hu'⟩ <;> simp_all

private theorem finite_faces (N : ℕ) : {c : ClosedCoordinateCell N | IsFace c (cube N)}.Finite := by
  classical
  let f : {c : ClosedCoordinateCell N // IsFace c (cube N)} →
      (Fin N → Bool) × (Fin N → Bool) :=
    fun c ↦ (fun i ↦ decide (c.val.lower i = 1), fun i ↦ decide (c.val.upper i = 1))
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply ClosedCoordinateCell.eq_of_corners
    · funext i
      have hh := congrArg (fun t ↦ t.1 i) h
      change decide (a.val.lower i = 1) = decide (b.val.lower i = 1) at hh
      have ha := a.property i
      have hb := b.property i
      rcases ha with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
        rcases hb with ⟨hl', hu'⟩ | ⟨hl', hu'⟩ | ⟨hl', hu'⟩ <;> simp_all [cube]
    · funext i
      have hh := congrArg (fun t ↦ t.2 i) h
      change decide (a.val.upper i = 1) = decide (b.val.upper i = 1) at hh
      have ha := a.property i
      have hb := b.property i
      rcases ha with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
        rcases hb with ⟨hl', hu'⟩ | ⟨hl', hu'⟩ | ⟨hl', hu'⟩ <;> simp_all [cube]
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

theorem face_subset {N : ℕ} {a b : ClosedCoordinateCell N} (h : IsFace a b) :
    a.carrier ⊆ b.carrier := by
  intro x hx
  constructor <;> intro i
  · have hx := hx.1 i
    rcases h i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
      rw [hl] at hx <;> exact (by first | exact hx | exact (b.lower_le_upper i).trans hx)
  · have hx := hx.2 i
    rcases h i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
      rw [hu] at hx <;> exact (by first | exact hx | exact hx.trans (b.lower_le_upper i))

private theorem faces_intersect {N : ℕ} {a b : ClosedCoordinateCell N}
    (ha : IsFace a (cube N)) (hb : IsFace b (cube N))
    (hn : (a.carrier ∩ b.carrier).Nonempty) :
    ∃ d, IsFace d (cube N) ∧ IsFace d a ∧ IsFace d b ∧
      d.carrier = a.carrier ∩ b.carrier := by
  obtain ⟨x, hxa, hxb⟩ := hn
  let d : ClosedCoordinateCell N := {
    lower i := max (a.lower i) (b.lower i)
    upper i := min (a.upper i) (b.upper i)
    lower_le_upper i := max_le (le_min (a.lower_le_upper i) ((hxa.1 i).trans (hxb.2 i)))
      (le_min ((hxb.1 i).trans (hxa.2 i)) (b.lower_le_upper i)) }
  have hda : IsFace d a := by
    intro i
    have h1 := hxa.1 i
    have h2 := hxa.2 i
    have h3 := hxb.1 i
    have h4 := hxb.2 i
    change (max (a.lower i) (b.lower i) = a.lower i ∧ min (a.upper i) (b.upper i) = a.upper i) ∨
      (max (a.lower i) (b.lower i) = a.lower i ∧ min (a.upper i) (b.upper i) = a.lower i) ∨
      (max (a.lower i) (b.lower i) = a.upper i ∧ min (a.upper i) (b.upper i) = a.upper i)
    rcases ha i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
      rcases hb i with ⟨hl', hu'⟩ | ⟨hl', hu'⟩ | ⟨hl', hu'⟩ <;>
      simp_all [cube] <;> linarith
  have hdb : IsFace d b := by
    intro i
    have h1 := hxa.1 i
    have h2 := hxa.2 i
    have h3 := hxb.1 i
    have h4 := hxb.2 i
    change (max (a.lower i) (b.lower i) = b.lower i ∧ min (a.upper i) (b.upper i) = b.upper i) ∨
      (max (a.lower i) (b.lower i) = b.lower i ∧ min (a.upper i) (b.upper i) = b.lower i) ∨
      (max (a.lower i) (b.lower i) = b.upper i ∧ min (a.upper i) (b.upper i) = b.upper i)
    rcases ha i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩ <;>
      rcases hb i with ⟨hl', hu'⟩ | ⟨hl', hu'⟩ | ⟨hl', hu'⟩ <;>
      simp_all [cube] <;> linarith
  refine ⟨d, face_trans hda ha, hda, hdb, ?_⟩
  ext y
  change (∀ i, max (a.lower i) (b.lower i) ≤ y i) ∧
    (∀ i, y i ≤ min (a.upper i) (b.upper i)) ↔
    ((∀ i, a.lower i ≤ y i) ∧ (∀ i, y i ≤ a.upper i)) ∧
    ((∀ i, b.lower i ≤ y i) ∧ (∀ i, y i ≤ b.upper i))
  simp only [max_le_iff, le_min_iff, forall_and]
  tauto

/-- The standard cube with all its coordinate faces is a finite rectilinear
subdivision. Its face intersections are the coordinatewise intersections,
and all closed faces are retained. Source: Hatcher Appendix A.2 p.521. -/
private def cubeSubdivision (N : ℕ) : FiniteRectilinearSubdivision N where
  cube := cube N
  cube_side := ⟨2, by norm_num, fun _ ↦ by norm_num [cube]⟩
  cells := {c | IsFace c (cube N)}
  finite_cells := finite_faces N
  faces _ hc _ ha := face_trans ha hc
  intersections _ ha _ hb hn := faces_intersect ha hb hn
  cover := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨c, hc, hx⟩
      exact face_subset hc hx
    · intro hx
      exact ⟨cube N, fun _ ↦ Or.inl ⟨rfl, rfl⟩, hx⟩

private theorem cube_carrier (N : ℕ) :
    (cube N).carrier = Metric.closedBall (0 : Fin N → ℝ) 1 := by
  ext x
  simp only [ClosedCoordinateCell.carrier, cube, mem_Icc, Pi.le_def,
    Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num), Real.norm_eq_abs, abs_le,
    forall_and]

private theorem cube_openCarrier (N : ℕ) :
    (cube N).openCarrier = Metric.ball (0 : Fin N → ℝ) 1 := by
  ext x
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num)]
  constructor
  · intro hx i
    exact abs_lt.mpr (hx.2 i (by norm_num [cube]))
  · intro hx
    have hi (i : Fin N) : -1 < x i ∧ x i < 1 := abs_lt.mp (hx i)
    exact ⟨⟨fun i ↦ (hi i).1.le, fun i ↦ (hi i).2.le⟩, fun i _ ↦ hi i⟩

private theorem cube_dimension (N : ℕ) : (cube N).dimension = N := by
  simp [ClosedCoordinateCell.dimension, cube]

private theorem face_eq_cube_of_dimension {N : ℕ} {c : ClosedCoordinateCell N}
    (hc : IsFace c (cube N)) (hd : c.dimension = N) : c = cube N := by
  have hfull : {i : Fin N | c.lower i < c.upper i} = univ := by
    apply (Set.eq_univ_iff_ncard _).mpr
    simpa only [Nat.card_fin, ClosedCoordinateCell.dimension] using hd
  have hi (i : Fin N) : c.lower i < c.upper i := by
    change i ∈ {i : Fin N | c.lower i < c.upper i}
    rw [hfull]
    trivial
  apply ClosedCoordinateCell.eq_of_corners <;> funext i
  · rcases hc i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩
    · exact hl
    · exact hl
    · have := hi i; simp_all
  · rcases hc i with ⟨hl, hu⟩ | ⟨hl, hu⟩ | ⟨hl, hu⟩
    · exact hu
    · have := hi i; simp_all
    · exact hu

private def boundaryComplex (N : ℕ) : CubicalSubcomplex (cubeSubdivision N) where
  cells := {c | IsFace c (cube N) ∧ c.dimension < N}
  subset_cells _ hc := hc.1
  faces _ hc _ ha := ⟨face_trans ha hc.1, ha.dimension_le.trans_lt hc.2⟩

private theorem boundary_carrier (N : ℕ) :
    (boundaryComplex N).carrier = Metric.sphere (0 : Fin N → ℝ) 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.mp hx
    have hclosed : x ∈ Metric.closedBall (0 : Fin N → ℝ) 1 :=
      cube_carrier N ▸ face_subset hc.1 hx
    have hnot : x ∉ Metric.ball (0 : Fin N → ℝ) 1 := by
      intro hball
      have heq := hc.1.eq_of_mem_openCarrier hx ((cube_openCarrier N).symm ▸ hball)
      have hdim := hc.2
      rw [heq, cube_dimension] at hdim
      omega
    exact Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hclosed)
      (le_of_not_gt (fun h ↦ hnot (Metric.mem_ball.mpr h))))
  · intro hx
    have hclosed : x ∈ (cube N).carrier :=
      (cube_carrier N).symm ▸ Metric.sphere_subset_closedBall hx
    obtain ⟨c, hc, hxc⟩ := (cube N).exists_face_mem_openCarrier hclosed
    have hdim : c.dimension < N := by
      have hle : c.dimension ≤ N := by simpa only [cube_dimension] using hc.dimension_le
      by_contra h
      have heq := face_eq_cube_of_dimension hc (by omega)
      have hopen : x ∈ Metric.ball (0 : Fin N → ℝ) 1 := by
        rw [heq, cube_openCarrier] at hxc
        exact hxc
      exact Metric.sphere_disjoint_ball.notMem_of_mem_left hx hopen
    exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨⟨hc, hdim⟩, hxc.1⟩⟩

/-- The maximum-norm sphere has a finite CW structure with every cell dimension
strictly smaller than its ambient dimension. Source: Hatcher Appendix A.2 p.521.
Use the proper cube faces. Their inherited CW skeleta contain the whole carrier
by degree N−1; disjointness excludes every higher-dimensional cell. Restricting
characteristic maps to the carrier retains the original cell indices. -/
theorem sphere_finite_cw_bounded (N : ℕ) (hN : 0 < N) :
    ∃ cw : CWComplex (univ : Set (Metric.sphere (0 : Fin N → ℝ) 1)),
      letI := cw
      RelCWComplex.Finite (univ : Set (Metric.sphere (0 : Fin N → ℝ) 1)) ∧
      ∀ n, N ≤ n → IsEmpty (RelCWComplex.cell
        (univ : Set (Metric.sphere (0 : Fin N → ℝ) 1)) n) := by
  obtain ⟨cw, hfinite, _, hsk⟩ := cubical_subcomplex_cw_structure
    (cubeSubdivision N) (boundaryComplex N)
  have hbase : ∃ cw : CWComplex (boundaryComplex N).carrier,
      letI := cw
      RelCWComplex.Finite (boundaryComplex N).carrier ∧
      ∀ n, N ≤ n → IsEmpty (RelCWComplex.cell (boundaryComplex N).carrier n) := by
    let := cw
    let := hfinite
    refine ⟨cw, hfinite, ?_⟩
    have hs : (CWComplex.skeleton (boundaryComplex N).carrier (↑(N - 1 : ℕ)) : Set (Fin N → ℝ)) =
        (boundaryComplex N).carrier := by
      rw [hsk]
      ext x
      simp only [CubicalSubcomplex.skeleton, CubicalSubcomplex.carrier, mem_iUnion]
      constructor
      · rintro ⟨c, hc, _, hx⟩
        exact ⟨c, hc, hx⟩
      · rintro ⟨c, hc, hx⟩
        exact ⟨c, hc, by have := hc.2; omega, hx⟩
    intro n hn
    refine ⟨fun i ↦ ?_⟩
    obtain ⟨x, hx⟩ := RelCWComplex.openCell_nonempty (C := (boundaryComplex N).carrier) n i
    have hxc := RelCWComplex.openCell_subset_complex n i hx
    rw [← hs] at hxc
    exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeleton_openCell
      (C := (boundaryComplex N).carrier) (j := i) (by exact_mod_cast (show N - 1 < n by omega)))
      hxc hx
  rw [boundary_carrier] at hbase
  obtain ⟨cwS, hfinS, hbound⟩ := hbase
  let := cwS
  let := hfinS
  let c0 : Metric.sphere (0 : Fin N → ℝ) 1 :=
    ⟨Pi.single ⟨0, hN⟩ 1, by simp [Pi.norm_single]⟩
  let := cwCarrierStructureG6 (Metric.sphere (0 : Fin N → ℝ) 1) c0
  refine ⟨inferInstance, cwCarrier_finite _ c0, ?_⟩
  exact hbound


end HolomorphicAnosov.StandardDiskBoundaryCW

