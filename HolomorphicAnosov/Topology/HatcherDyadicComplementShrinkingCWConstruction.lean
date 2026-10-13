import HolomorphicAnosov.Topology.DyadicComplementGeometry
import HolomorphicAnosov.Topology.DyadicCubesShrinkAt

namespace HolomorphicAnosov
open Set Topology _root_.Topology
/-- Hatcher’s regular locally finite dyadic CW structure on a compact-set complement.

Source: Hatcher, Algebraic Topology, proof of Theorem A.7, pp.525–526.
The proof uses the explicit minimal-face construction in `DyadicComplementGeometry`
and the finite-grid estimate `dyadic_cubes_shrink_at`. Every assertion below is proved.

Following Hatcher A.7 pp.525–526, start with the integer unit grid and its dyadic refinements. At level zero retain every closed cube disjoint from C. At each later level retain the cubes disjoint from C that are not contained in a retained earlier cube. Given x outside C, its complement is open, so choose an avoiding ball about x; dyadic_cube_in_ball gives a sufficiently small avoiding cube through x. If it is contained in an earlier retained cube use that cube, otherwise take the least avoiding level. Thus the retained cubes cover the complement and have disjoint interiors. Their coordinate boxes are compact in the original Euclidean topology.

To verify local finiteness, choose a small closed neighborhood of a complement point with positive distance from C. At all sufficiently fine dyadic levels, every cube meeting that neighborhood has an ancestor at a fixed coarser level disjoint from C. It cannot be newly selected after that level. At each of the remaining finitely many levels only finitely many cubes meet this bounded neighborhood. Retained cubes and their faces are consequently locally finite. Dyadic alignment makes each intersection a coordinate face of the finer cube. Use the minimal relative open faces in this locally finite face arrangement, as in Hatcher, so faces crossed by a finer adjacent boundary are divided into their constituent rectangular faces. The open cells are disjoint and exhaust the complement; each closed face has only finitely many constituent proper faces because it is compact and the arrangement is locally finite.

For a d-dimensional face enumerate its active coordinates by an embedding Fin d→Fin N, keep inactive coordinates at their common endpoint, and map u by midpoint plus half the side length times u_i in each active coordinate. The maximum-norm ball identities identify the parameter open and closed balls with coordinate inequalities. The affine range and image lemmas give exactly the stated open and closed coordinate boxes. Positive active lengths imply injectivity by cancellation, and coordinate inversion gives surjectivity. The coordinate inverse is continuous, giving an explicit homeomorphism of the closed parameter ball with the closed box. The sphere endpoint lemma identifies its boundary with the finite union of constituent faces of dimension below d; for d=0 the parameter is the unique empty tuple and the frontier is empty.

Attach these characteristic disks in increasing dimension. Their interiors parametrize the disjoint open faces, and their spheres map into the already constructed finite lower-dimensional face unions. A subset is closed if and only if its intersection with every closed cell is closed: the forward direction is immediate, and the reverse follows because the closed cells are a locally finite closed cover, so the relevant union of closed intersections is closed. This verifies the CW weak topology in the original complement topology, not a topology chosen afterward. There are no cells above dimension N. For the shrinking assertion at c in C, fix epsilon and first choose a fine level at which cube diameters are below epsilon/2. The finitely many coarser dyadic cubes meeting a fixed bounded neighborhood of c and disjoint from C are compact and avoid c, so a sufficiently small positive delta avoids all of them. Any selected cell meeting ball(c,delta) therefore lies in a finer cube; choose delta≤epsilon/2 and use its diameter bound and the triangle inequality to put its whole closed cell in ball(c,epsilon). The empty-C case makes this last requirement vacuous.
-/
theorem hatcher_dyadic_complement_shrinking_cw_construction :
    ∀ (N : ℕ) (_hN : 0 < N) (C : Set (EuclideanSpace ℝ (Fin N))) (_hC : IsCompact C) (_hAux : C ⊆ C),
    let X := {x : EuclideanSpace ℝ (Fin N) // x ∉ C}
    ∃ cw : CWComplex (univ : Set X),
      letI : CWComplex (univ : Set X) := cw
      LocallyFinite (fun j : Σ d : ℕ, RelCWComplex.cell (univ : Set X) d ↦
        RelCWComplex.closedCell (C := (univ : Set X)) j.1 j.2) ∧
      (∀ (d : ℕ) (_i : RelCWComplex.cell (univ : Set X) d), d ≤ N) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        ∃ (k : ℕ) (m : Fin N → ℤ) (e : Fin d ↪ Fin N) (a b : Fin N → ℝ),
          Disjoint {x : EuclideanSpace ℝ (Fin N) | ∀ j,
            (m j : ℝ) / (2 : ℝ) ^ k ≤ x j ∧
              x j ≤ ((m j : ℝ) + 1) / (2 : ℝ) ^ k} C ∧
          (∀ j, (m j : ℝ) / (2 : ℝ) ^ k ≤ a j ∧ a j ≤ b j ∧
            b j ≤ ((m j : ℝ) + 1) / (2 : ℝ) ^ k ∧
            (a j < b j ↔ j ∈ Set.range e)) ∧
          RelCWComplex.closedCell (C := (univ : Set X)) d i =
            {x : X | ∀ j, a j ≤ x.val j ∧ x.val j ≤ b j} ∧
          RelCWComplex.openCell (C := (univ : Set X)) d i =
            {x : X | (∀ j : Fin d, a (e j) < x.val (e j) ∧ x.val (e j) < b (e j)) ∧
              ∀ j : Fin N, j ∉ Set.range e → x.val j = a j} ∧
          (∀ u : Fin d → ℝ, u ∈ Metric.closedBall 0 1 →
            (∀ j : Fin d,
              (RelCWComplex.map (C := (univ : Set X)) d i u).val (e j) =
                (a (e j) + b (e j)) / 2 + (b (e j) - a (e j)) * u j / 2) ∧
            (∀ j : Fin N, j ∉ Set.range e →
              (RelCWComplex.map (C := (univ : Set X)) d i u).val j = a j))) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        ∃ h : ↥(Metric.closedBall (0 : Fin d → ℝ) 1) ≃ₜ
            ↥(RelCWComplex.closedCell (C := (univ : Set X)) d i),
          ∀ u : ↥(Metric.closedBall (0 : Fin d → ℝ) 1),
            (h u).val = RelCWComplex.map (C := (univ : Set X)) d i u.val) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        ∃ F : Finset (Σ n : ℕ, RelCWComplex.cell (univ : Set X) n),
          (∀ j : Σ n : ℕ, RelCWComplex.cell (univ : Set X) n, j ∈ F → j.1 < d) ∧
          RelCWComplex.cellFrontier (C := (univ : Set X)) d i =
            ⋃ j ∈ F, RelCWComplex.closedCell (C := (univ : Set X)) j.1 j.2) ∧
      (∀ c ∈ C, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
          (∃ x : X, x ∈ RelCWComplex.closedCell (C := (univ : Set X)) d i ∧
            dist x.val c < δ) →
          ∀ x : X, x ∈ RelCWComplex.closedCell (C := (univ : Set X)) d i →
            dist x.val c < ε) := by
  classical
  intro N hN C hC hAux
  dsimp only
  let : CWComplex (univ : Set {x : EuclideanSpace ℝ (Fin N) // x ∉ C}) :=
    DyadicComplement.cw C hC.isClosed
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change LocallyFinite (fun j : Σ d, DyadicComplement.Cells C d ↦
      DyadicComplement.maps C j.1 j.2 '' Metric.closedBall 0 1)
    have hlf := (DyadicComplement.Cell.locallyFinite hC.isClosed).comp_injective
      (DyadicComplement.cellsEquiv (C := C)).injective
    change LocallyFinite (fun j : Σ d, DyadicComplement.Cells C d ↦ j.2.val.closed) at hlf
    simpa only [DyadicComplement.maps_image_closed] using hlf
  · intro d i
    exact i.property ▸ i.val.dim_le
  · rintro d ⟨f,rfl⟩
    refine ⟨f.cubeIndex.val.1, f.cubeIndex.val.2, f.embed, f.lower, f.upper,
      f.cubeIndex.property.1, ?_, ?_, ?_, ?_⟩
    · intro j
      refine ⟨?_, f.lower_le_upper j, ?_, f.lower_lt_iff j⟩
      · unfold DyadicComplement.Cell.lower DyadicComplement.faceLower
        split_ifs <;> first | exact le_rfl | exact (DyadicComplement.grid_lt _ _).le
      · unfold DyadicComplement.Cell.upper DyadicComplement.faceUpper
        split_ifs <;> first | exact le_rfl | exact (DyadicComplement.grid_lt _ _).le
    · change DyadicComplement.maps C f.dim ⟨f,rfl⟩ '' Metric.closedBall 0 1 = _
      rw [DyadicComplement.maps_image_closed]
      exact f.closed_eq_box
    · change DyadicComplement.maps C f.dim ⟨f,rfl⟩ '' Metric.ball 0 1 = _
      rw [DyadicComplement.maps_image_open]
      exact f.open_eq_box
    · exact f.characteristic_formula
  · rintro d ⟨f,rfl⟩
    change ∃ h : ↥(Metric.closedBall (0 : Fin f.dim → ℝ) 1) ≃ₜ
      ↥(DyadicComplement.maps C f.dim ⟨f,rfl⟩ '' Metric.closedBall 0 1), _
    let h := f.closedHomeomorph.trans (Homeomorph.setCongr
      (DyadicComplement.maps_image_closed C f.dim ⟨f,rfl⟩).symm)
    exact ⟨h, fun _ ↦ rfl⟩
  · rintro d ⟨f,rfl⟩
    obtain ⟨F,hF,hboundary⟩ := f.finite_boundary hC.isClosed
    let G := F.image (DyadicComplement.cellsEquiv (C := C)).symm
    change ∃ F : Finset (Σ n, DyadicComplement.Cells C n),
      (∀ j, j ∈ F → j.1 < f.dim) ∧
      DyadicComplement.maps C f.dim ⟨f,rfl⟩ '' Metric.sphere 0 1 =
        ⋃ j ∈ F, DyadicComplement.maps C j.1 j.2 '' Metric.closedBall 0 1
    refine ⟨G, ?_, ?_⟩
    · intro j hj
      change j ∈ G at hj
      obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hj
      exact hF g hg
    · change DyadicComplement.maps C f.dim ⟨f,rfl⟩ '' Metric.sphere 0 1 =
        ⋃ j ∈ G, DyadicComplement.maps C j.1 j.2 '' Metric.closedBall 0 1
      rw [DyadicComplement.maps_image_sphere, hboundary]
      simp only [G, Finset.mem_image]
      ext x
      constructor
      · intro hx
        obtain ⟨g,hg,hxg⟩ := mem_iUnion₂.mp hx
        refine mem_iUnion₂.mpr ⟨(DyadicComplement.cellsEquiv (C := C)).symm g,
          ⟨g,hg,rfl⟩, ?_⟩
        rw [DyadicComplement.maps_image_closed]
        exact hxg
      · intro hx
        obtain ⟨j,⟨g,hg,rfl⟩,hxg⟩ := mem_iUnion₂.mp hx
        rw [DyadicComplement.maps_image_closed] at hxg
        exact mem_iUnion₂.mpr ⟨g,hg,hxg⟩
  · intro c hc ε hε
    obtain ⟨δ,hδ,hshrink⟩ := dyadic_cubes_shrink_at c ε hε
    refine ⟨δ,hδ, ?_⟩
    rintro d ⟨f,rfl⟩ ⟨x,hxf,hxd⟩ y hyf
    change x ∈ DyadicComplement.maps C f.dim ⟨f,rfl⟩ '' Metric.closedBall 0 1 at hxf
    change y ∈ DyadicComplement.maps C f.dim ⟨f,rfl⟩ '' Metric.closedBall 0 1 at hyf
    rw [DyadicComplement.maps_image_closed] at hxf hyf
    apply hshrink f.cubeIndex.val.1 f.cubeIndex.val.2
      (fun h ↦ Set.disjoint_left.mp f.cubeIndex.property.1 h hc)
      ⟨x.val, f.closure_subset_cube hxf, hxd⟩ y.val (f.closure_subset_cube hyf)

end HolomorphicAnosov

