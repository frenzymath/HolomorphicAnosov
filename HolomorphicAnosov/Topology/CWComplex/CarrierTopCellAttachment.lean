import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.TopCellComplementSubcomplex
import HolomorphicAnosov.Topology.CWComplex.CharacteristicInteriorHomeomorph
import HolomorphicAnosov.Topology.CWComplex.EuclideanSupRadialHomeomorph
import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

namespace HolomorphicAnosov

open HatcherAttachedCell

/-- The carrier of a CW complex is the attachment of a highest-dimensional
cell to its complement, with the inherited subspace topology. This carrier
version permits successive removal of cells while keeping one ambient CW
complex. Source: Hatcher Theorem 4.8, pp.349–351; the carrier bookkeeping is
agent-written. Restrict the characteristic disk into the carrier, using closed
cell containment. Its sphere lands outside the open cell, while the interior
homeomorphism restricts to the same cell in the carrier. The complement is a
closed subcomplex. Its inclusion and the compact characteristic disk map form
a continuous closed surjection, hence a quotient. Norm-preserving radial
coordinates give precisely the Euclidean Attachment conventions. -/
theorem cw_carrier_top_cell_attachment
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (k : ℕ) (i : Topology.RelCWComplex.cell C k)
    (htop : ∀ (m : ℕ), Topology.RelCWComplex.cell C m → m ≤ k) :
    ∃ D : Attachment C k,
      D.oldSpace = {x : C | (x : X) ∉ Topology.CWComplex.openCell k i} := by
  obtain ⟨e, he⟩ := euclidean_sup_radial_homeomorph k
  let ed : CellDisk k ≃ₜ Metric.closedBall (0 : Fin k → ℝ) 1 :=
    e.subtype (fun x ↦ by simp only [Metric.mem_closedBall, dist_zero_right, he])
  let eb : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 ≃ₜ
      Metric.ball (0 : Fin k → ℝ) 1 :=
    e.subtype (fun x ↦ by simp only [Metric.mem_ball, dist_zero_right, he])
  let O : Set C := {x | (x : X) ∉ Topology.CWComplex.openCell k i}
  let χ : C(CellDisk k, C) := ⟨fun z ↦
    ⟨Topology.RelCWComplex.map k i (e z.val),
      Topology.CWComplex.closedCell_subset_complex k i
        ⟨e z.val, (ed z).property, rfl⟩⟩,
    ((Topology.RelCWComplex.continuousOn k i).domRestrict.comp ed.continuous).subtype_mk _⟩
  have hboundary (x : CellSphere k) : χ (boundaryInclusion x) ∈ O := by
    have hx : e x.val ∈ Metric.sphere (0 : Fin k → ℝ) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right, he] using x.property
    exact Set.disjoint_left.mp
      (Topology.CWComplex.disjoint_skeletonLT_openCell (C := C)
        (j := i) (le_refl (k : ℕ∞)))
      (Topology.CWComplex.cellFrontier_subset_skeletonLT k i ⟨e x.val, hx, rfl⟩)
  let a : C(CellSphere k, O) := ⟨fun x ↦ ⟨χ (boundaryInclusion x), hboundary x⟩,
    (χ.continuous.comp
      (show Continuous (boundaryInclusion : CellSphere k → CellDisk k) from
        continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  obtain ⟨b, hb⟩ := cw_characteristic_interior_homeomorph C k i
  have hsub : Topology.CWComplex.openCell k i ⊆ Set.range (Subtype.val : C → X) := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using
      Topology.CWComplex.openCell_subset_complex k i
  let bc := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hsub
  have hO : (Subtype.val : C → X) ⁻¹' Topology.CWComplex.openCell k i = Oᶜ := by
    ext x
    simp [O]
  let b' : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) 1 ≃ₜ ↥(Oᶜ) :=
    ((eb.trans b).trans bc.symm).trans (Homeomorph.setCongr hO)
  obtain ⟨W, hW, _⟩ := cw_top_cell_complement_subcomplex C k i htop
  have hclosed : IsClosed O := by
    have hc := W.closed.preimage (continuous_subtype_val : Continuous (Subtype.val : C → X))
    convert hc using 1
    ext x
    simp [hW, O]
  have : CompactSpace (CellDisk k) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  refine ⟨{
    oldSpace := O
    characteristic := χ
    attaching := a
    boundary_eq := fun _ ↦ rfl
    quotient := ?_
    cell_open := hclosed.isOpen_compl
    interior := b'
    characteristic_interior := ?_
    coordinates := Homeomorph.unitBall.trans b' }, rfl⟩
  · apply (hclosed.isClosedMap_subtype_val.sumElim χ.continuous.isClosedMap).isQuotientMap
      (continuous_subtype_val.sumElim χ.continuous)
    intro x
    by_cases hx : x ∈ O
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · obtain ⟨z, hz, heq⟩ := (show (x : X) ∈ Topology.CWComplex.openCell k i by
        simpa only [O, Set.mem_ofPred_eq, not_not] using hx)
      let d : CellDisk k := ed.symm ⟨z, Metric.ball_subset_closedBall hz⟩
      refine ⟨Sum.inr d, ?_⟩
      apply Subtype.ext
      change Topology.RelCWComplex.map k i (e d.val) = x.val
      have hed : e d.val = z := congrArg Subtype.val (ed.apply_symm_apply ⟨z, Metric.ball_subset_closedBall hz⟩)
      rw [hed, heq]
  · intro x
    apply Subtype.ext
    change Topology.RelCWComplex.map k i (e x.val) = ((bc.symm (b (eb x))).val : X)
    have hbc := congrArg Subtype.val (bc.apply_symm_apply (b (eb x)))
    exact (hb (eb x)).symm.trans hbc.symm

end HolomorphicAnosov
