import HolomorphicAnosov.Topology.CWComplex.DiskAdjunction

/-!
# New open cells in a disk adjunction

Hatcher, Algebraic Topology, Appendix p.519: each newly attached open disk
maps homeomorphically onto its open cell. The proof expands the fact that
no boundary generator meets a disk interior, so interior open subsets are
saturated open subsets of the disjoint union. It uses the original quotient
topology, with no separation or boundary-injectivity hypothesis.
DAG: `topo.finite_adjunction_open_cell_embedding_g4`.
-/

open Set TopCat _root_.Topology
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- The interior of a newly attached disk embeds openly in its adjunction.
For each interior point its equality predicate is invariant under the
boundary-generated equivalence relation, since that point lies on neither
side of a boundary generator. Hence every interior subset is saturated.
The interior inclusion into the Euclidean closed disk is an open embedding;
its fixed-label image in the disjoint union is open. The quotient topology
therefore makes the new-cell map open. The same invariant proves injectivity,
and continuity follows from the quotient projection. This is the literal
quotient expansion of Hatcher Appendix p.519, written by the agent. It also
applies in dimension zero, when the boundary is empty. -/
theorem adjunction_new_openCell_isOpenEmbedding {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} (i : Fin k) :
    IsOpenEmbedding (fun z : 𝔹 n ↦ @newCharacteristic n X k a i (ballInclusion n z)) := by
  classical
  have hball : IsOpenEmbedding (ballInclusion n) := by
    have h := IsOpenEmbedding.inclusion
      (Metric.ball_subset_closedBall : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆
        Metric.closedBall 0 1) (Metric.isOpen_ball.preimage continuous_subtype_val)
    exact Homeomorph.ulift.symm.isOpenEmbedding.comp (h.comp Homeomorph.ulift.isOpenEmbedding)
  let raw : 𝔹 n → X ⊕ (Fin k × 𝔻 n) := fun z ↦ .inr (i, ballInclusion n z)
  let R := fun p q : X ⊕ (Fin k × 𝔻 n) ↦ ∃ (j : Fin k) (z : ∂𝔻 n),
    p = Sum.inr (j, diskBoundaryInclusion n z) ∧ q = Sum.inl (a j z)
  have hne (j : Fin k) (w : ∂𝔻 n) (z : 𝔹 n) :
      Sum.inr (j, diskBoundaryInclusion n w) ≠ raw z := by
    intro he
    have hwz : diskBoundaryInclusion n w = ballInclusion n z :=
      congrArg Prod.snd (Sum.inr.inj he)
    have hc := congrArg (fun v : 𝔻 n ↦ v.down.val) hwz
    have hw := w.down.property
    have hz := z.down.property
    change dist w.down.val 0 = 1 at hw
    change dist z.down.val 0 < 1 at hz
    change w.down.val = z.down.val at hc
    rw [hc] at hw
    exact (ne_of_lt hz) hw
  have hinvariant (z : 𝔹 n) {p q} (h : Relation.EqvGen R p q) :
      p = raw z ↔ q = raw z := by
    induction h with
    | rel p q h =>
      obtain ⟨j, w, rfl, rfl⟩ := h
      exact iff_of_false (hne j w z) (by intro h; cases h)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hraw : Function.Injective raw := by
    intro z w hzw
    exact hball.injective (congrArg Prod.snd (Sum.inr.inj hzw))
  have hopen : IsOpenMap raw := by
    intro U hU
    have heq : raw '' U = Sum.inr '' (({i} : Set (Fin k)) ×ˢ ((ballInclusion n) '' U)) := by
      ext p
      simp only [raw, mem_image, mem_prod, mem_singleton_iff, Prod.exists]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨i, ballInclusion n z, ⟨rfl, z, hz, rfl⟩, rfl⟩
      · rintro ⟨j, w, ⟨rfl, z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [heq]
    exact isOpenMap_inr _ (isOpen_discrete _ |>.prod (hball.isOpenMap _ hU))
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_quotient_mk'.comp
      (continuous_inr.comp (continuous_const.prodMk hball.continuous))) ?_ ?_
  · intro z w hzw
    apply hraw
    exact (hinvariant w (Quotient.exact hzw)).mpr rfl
  · intro U hU
    apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
    have heq : Quotient.mk (Relation.EqvGen.setoid R) ⁻¹'
        ((fun z : 𝔹 n ↦ @newCharacteristic n X k a i (ballInclusion n z)) '' U) = raw '' U := by
      ext p
      constructor
      · rintro ⟨z, hz, he⟩
        exact ⟨z, hz, ((hinvariant z (Quotient.exact he)).mp rfl).symm⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    convert hopen U hU using 1
    exact heq

end HolomorphicAnosov.FiniteCellAdjunction
