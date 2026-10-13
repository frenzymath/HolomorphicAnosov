import HolomorphicAnosov.Topology.CWSkeletonCellComplement

/-! # The characteristic quotient after moving an interior disk point
Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Lemma 2.3.7,
p.67, and the adjunction topology in Theorem 2.3.1, pp.62–63.
-/

open Set _root_.Topology

namespace HolomorphicAnosov

/-- Reparametrizing the disk of one top cell by a homeomorphism preserves its
characteristic quotient onto the original skeleton.

Source: Fritsch–Piccinini, Lemma 2.3.7, p.67, and Theorem 2.3.1, pp.62–63.
The characteristic map lands in the skeleton because its entire closed cell
does. The complement subcomplex is closed, so its inclusion into the skeleton
is closed. The moved disk map is continuous from a compact disk to a Hausdorff
space, hence closed. The sum map is thus continuous and closed. It is onto:
a point in the complement comes from the first summand; otherwise it is in
the open cell, and an interior characteristic representative pulled back
through the disk homeomorphism gives a preimage in the second summand.
A continuous closed surjection is quotient. The proof uses the standard closed-map quotient criterion and allows dimension zero,
noninjective attaching maps, and infinitely many other cells.
-/
theorem cw_skeleton_moved_disk_quotient
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {C : Set X} [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)
    (A : CWComplex.Subcomplex C)
    (hA : (A : Set X) = (CWComplex.skeleton C n : Set X) \ CWComplex.openCell n i)
    (H : Metric.closedBall (0 : Fin n → ℝ) 1 ≃ₜ
      Metric.closedBall (0 : Fin n → ℝ) 1) :
    let S := (CWComplex.skeleton C n : Set X)
    let B := {y : S | y.val ∈ (A : Set X)}
    ∃ χ : C(Metric.closedBall (0 : Fin n → ℝ) 1, S),
      (∀ z, (χ z).val = RelCWComplex.map n i (H z).val) ∧
      IsQuotientMap (Sum.elim (Subtype.val : B → S) χ) := by
  dsimp only
  let χ : C(Metric.closedBall (0 : Fin n → ℝ) 1,
      (CWComplex.skeleton C n : Set X)) :=
    ⟨fun z ↦ ⟨RelCWComplex.map n i (H z).val,
      CWComplex.closedCell_subset_skeleton n i ⟨(H z).val, (H z).property, rfl⟩⟩,
      ((RelCWComplex.continuousOn n i).domRestrict.comp H.continuous).subtype_mk _⟩
  have hclosed : IsClosed {y : (CWComplex.skeleton C n : Set X) | y.val ∈ (A : Set X)} :=
    A.closed.preimage continuous_subtype_val
  refine ⟨χ, fun _ ↦ rfl, ?_⟩
  apply (hclosed.isClosedMap_subtype_val.sumElim χ.continuous.isClosedMap).isQuotientMap
    (continuous_subtype_val.sumElim χ.continuous)
  intro y
  by_cases hy : y.val ∈ (A : Set X)
  · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
  · have hcell : y.val ∈ CWComplex.openCell n i := by
      by_contra hnot
      exact hy (hA ▸ ⟨y.property, hnot⟩)
    obtain ⟨v, hv, hvy⟩ := hcell
    let z : Metric.closedBall (0 : Fin n → ℝ) 1 := ⟨v, Metric.ball_subset_closedBall hv⟩
    refine ⟨Sum.inr (H.symm z), ?_⟩
    apply Subtype.ext
    change RelCWComplex.map n i (H (H.symm z)).val = y.val
    rw [H.apply_symm_apply]
    exact hvy

end HolomorphicAnosov
