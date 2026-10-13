import HolomorphicAnosov.Topology.Cubical.OpenCellPartition
import HolomorphicAnosov.Topology.Cubical.SubcomplexClosed
import HolomorphicAnosov.Topology.Cubical.FaceDimension
import HolomorphicAnosov.Topology.CWComplex.CarrierTransportG6

noncomputable section
namespace HolomorphicAnosov.Cubical

open Set _root_.Topology in
/-- Select the original cubical cells inside the native finite CW structure.
The common-face property makes the union of their open faces the original
subcomplex carrier. The inherited cell labels retain the ambient dimension bound.
Source: Hatcher, Appendix A.2, p.521. -/
theorem cubical_subcomplex_cw_structure {N : ℕ} (K : FiniteRectilinearSubdivision N)
    (M : CubicalSubcomplex K) :
    ∃ cw : CWComplex M.carrier,
      letI := cw
      RelCWComplex.Finite M.carrier ∧
        (∀ n, N < n → IsEmpty (RelCWComplex.cell M.carrier n)) ∧
        ∀ q : ℕ, (CWComplex.skeleton M.carrier q : Set (Fin N → ℝ)) = M.skeleton q := by
  classical
  obtain ⟨cw, hfinite, index, hcells⟩ := finiteSubdivision_cwStructure K
  let := cw
  let := hfinite
  let D : RelCWComplex.Subcomplex K.cube.carrier := {
    carrier := M.carrier
    I := fun n ↦ {i | ((index n).symm i).val ∈ M.cells}
    closed' := M.carrier_isClosed
    union' := by
      rw [empty_union]
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨n, ⟨i, hi⟩, hx⟩
        let c := (index n).symm i
        have hcell := (hcells n c).2
        rw [Equiv.apply_symm_apply] at hcell
        rw [hcell] at hx
        exact mem_iUnion.mpr ⟨c.val, mem_iUnion.mpr ⟨hi, hx.1⟩⟩
      · intro hx
        simp only [CubicalSubcomplex.carrier, mem_iUnion] at hx
        obtain ⟨c, hc, hx⟩ := hx
        obtain ⟨a, ha, hxa⟩ := c.exists_face_mem_openCarrier hx
        have ham : a ∈ M.cells := M.faces c hc a ha
        let ac : {b : ClosedCoordinateCell N // b ∈ K.cells ∧ b.dimension = a.dimension} :=
          ⟨a, M.subset_cells ham, rfl⟩
        refine ⟨a.dimension, ⟨(index a.dimension) ac, ?_⟩, ?_⟩
        · change ((index a.dimension).symm ((index a.dimension) ac)).val ∈ M.cells
          simpa only [Equiv.symm_apply_apply] using ham
        · rw [(hcells a.dimension ac).2]
          exact hxa }
  let : CWComplex M.carrier := CWComplex.Subcomplex.instCWComplex D
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · exact D.finite_subcomplex_of_finite
  · intro n hn
    refine ⟨fun i ↦ ?_⟩
    let c := (index n).symm i.val
    have hd : c.val.dimension ≤ N := by
      simpa [ClosedCoordinateCell.dimension] using
        ({j : Fin N | c.val.lower j < c.val.upper j}.ncard_le_card)
    have he := c.property.2
    omega

  intro q
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, i, hi⟩ := (CWComplex.mem_skeleton_iff (C := M.carrier)).mp hx
    let c := (index n).symm i.val
    have hopen : RelCWComplex.openCell (C := M.carrier) n i = c.val.openCarrier := by
      change RelCWComplex.openCell (C := K.cube.carrier) n i.val = _
      have hh := (hcells n c).2
      simpa only [c, Equiv.apply_symm_apply] using hh
    rw [hopen] at hi
    exact mem_iUnion.mpr ⟨c.val, mem_iUnion.mpr ⟨i.property,
      mem_iUnion.mpr ⟨c.property.2.le.trans (by exact_mod_cast hn), hi.1⟩⟩⟩
  · intro hx
    simp only [CubicalSubcomplex.skeleton, mem_iUnion, exists_prop] at hx
    obtain ⟨c, hc, hdim, hx⟩ := hx
    obtain ⟨a, ha, hxa⟩ := c.exists_face_mem_openCarrier hx
    have ham := M.faces c hc a ha
    let ac : {b : ClosedCoordinateCell N // b ∈ K.cells ∧ b.dimension = a.dimension} :=
      ⟨a, M.subset_cells ham, rfl⟩
    let i : RelCWComplex.cell M.carrier a.dimension :=
      ⟨(index a.dimension) ac, by
        change ((index a.dimension).symm ((index a.dimension) ac)).val ∈ M.cells
        simpa only [Equiv.symm_apply_apply] using ham⟩
    apply CWComplex.mem_skeleton_iff.mpr
    refine ⟨a.dimension, ?_, i, ?_⟩
    · exact_mod_cast (ClosedCoordinateCell.IsFace.dimension_le ha).trans hdim
    · change x ∈ RelCWComplex.openCell (C := K.cube.carrier) a.dimension ((index _) ac)
      rw [(hcells a.dimension ac).2]
      exact hxa

open Set _root_.Topology in
/-- Transporting the characteristic maps to the carrier preserves each skeleton. -/
theorem cwCarrier_skeleton_eq {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] (c0 : C) (q : ℕ) :
    letI := cwCarrierStructureG6 C c0
    (CWComplex.skeleton (univ : Set C) q : Set C) =
      Subtype.val ⁻¹' (CWComplex.skeleton C q : Set X) := by
  let := cwCarrierStructureG6 C c0
  ext x
  change x ∈ CWComplex.skeleton (univ : Set C) q ↔ x.val ∈ CWComplex.skeleton C q
  rw [CWComplex.mem_skeleton_iff, CWComplex.mem_skeleton_iff]
  apply exists_congr
  intro n
  apply exists_congr
  intro hn
  apply exists_congr
  intro i
  change x ∈ cwCarrierMapG6 C c0 n i '' Metric.ball 0 1 ↔
    x.val ∈ RelCWComplex.map (C := C) n i '' Metric.ball 0 1
  rw [cwCarrierMapG6_image C c0 n i _ Metric.ball_subset_closedBall]
  rfl

open Set _root_.Topology in
/-- Finite CW structures remain finite on their carrier subtype. -/
theorem cwCarrier_finite {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] [CWComplex.Finite C] (c0 : C) :
    letI := cwCarrierStructureG6 C c0
    CWComplex.Finite (univ : Set C) := by
  let := cwCarrierStructureG6 C c0
  exact { eventually_isEmpty_cell := RelCWComplex.FiniteDimensional.eventually_isEmpty_cell (C := C)
          finite_cell := RelCWComplex.FiniteType.finite_cell (C := C) }

end HolomorphicAnosov.Cubical
