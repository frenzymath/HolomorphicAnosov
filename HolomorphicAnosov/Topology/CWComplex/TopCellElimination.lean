import HolomorphicAnosov.Topology.AttachedCellPolyhedralData
import HolomorphicAnosov.Topology.CWComplex.TopCellComplementSubcomplex
import Mathlib.Topology.CWComplex.Classical.Basic
import HolomorphicAnosov.Topology.CWComplex.CarrierTopCellAttachment
import HolomorphicAnosov.Topology.CWComplex.AttachmentLowerDimensionalElimination
import HolomorphicAnosov.Topology.CWComplex.ProperSubcomplexCellCount

namespace HolomorphicAnosov

open HatcherAttachedCell

/-- A lower-dimensional cube map into a finite CW complex can eliminate
one highest-dimensional cell, fixing the original preimage of its complement.
The resulting supporting subcomplex has strictly fewer cells.

Source: Hatcher Theorem 4.8 and Lemma 4.10, pp.349–351. Form the Attachment
on the carrier using the highest cell and its complement subcomplex. Restrict
the cube map into the carrier, apply lower-dimensional attached-cell elimination,
and include the endpoint and relative homotopy back into the ambient space.
The endpoint lies in the complement, and deletion strictly decreases the finite
cell count. The missed-point deformation uses smooth approximation and chart cutoff.
-/
theorem cw_top_cell_elimination
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    {n k : ℕ} (i : Topology.RelCWComplex.cell C k)
    (htop : ∀ (m : ℕ), Topology.RelCWComplex.cell C m → m ≤ k)
    (hnk : n < k) (f : C(Cube n, Y)) (hf : Set.range f ⊆ C) :
    ∃ (W : Topology.CWComplex.Subcomplex C) (g : C(Cube n, Y)),
      (W : Set Y) = C \ Topology.CWComplex.openCell k i ∧
      Nat.card (Σ m, W.I m) < Nat.card (Σ m, Topology.RelCWComplex.cell C m) ∧
      Set.range g ⊆ (W : Set Y) ∧
      Nonempty (ContinuousMap.HomotopyRel f g (f ⁻¹' (W : Set Y))) := by
  obtain ⟨W, hW, hWI⟩ := cw_top_cell_complement_subcomplex C k i htop
  obtain ⟨D, hD⟩ := cw_carrier_top_cell_attachment C k i htop
  let q : C(Cube n, C) := ⟨fun x ↦ ⟨f x, hf ⟨x, rfl⟩⟩,
    f.continuous.subtype_mk _⟩
  obtain ⟨r, hr, ⟨H⟩⟩ := attachment_lower_dimensional_elimination D q hnk
  let g : C(Cube n, Y) := (ContinuousMap.subtypeVal C).comp r
  have hcard := cw_subcomplex_cell_count_lt_of_omitted C W k i
    (by rw [hWI]; exact not_not_intro rfl)
  refine ⟨W, g, hW, hcard, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    rw [hW]
    refine ⟨(r x).property, ?_⟩
    change (r x).val ∉ Topology.CWComplex.openCell k i
    simpa only [hD, Set.mem_ofPred_eq] using hr ⟨x, rfl⟩
  · refine ⟨{
      toHomotopy := (H.compContinuousMap (ContinuousMap.subtypeVal C)).toHomotopy
      prop' := ?_ }⟩
    intro t x hx
    exact congrArg Subtype.val (H.eq_fst t (by
      change q x ∈ D.oldSpace
      rw [hD]
      exact (show f x ∈ C \ Topology.CWComplex.openCell k i from hW ▸ hx).2))

end HolomorphicAnosov
