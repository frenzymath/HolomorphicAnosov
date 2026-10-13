import HolomorphicAnosov.Topology.CWComplex.AttachmentSkeleton

/-!
# Closed embeddings of original attachment stages

Hatcher, Algebraic Topology, Appendix pp.519–520 states that original skeleta
have their given topology and are closed. The proof here is an agent-written
closed-saturation argument for the literal quotient, rather than the radial
open-neighborhood extension used in the parent proof plan.
DAG: `topo.finite_attachment_stage_closed_embedding_g4`.
-/

open Set TopCat _root_.Topology
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- Hatcher Appendix p.519: the old space embeds as a closed subspace of a
disk adjunction. No separation assumption on the old space or quotient is
needed. A subset of the old space saturates to itself together with precisely
the boundary points whose attaching images lie in that subset. The boundary
inclusion is a closed embedding, so a closed subset has closed saturation.
The quotient closed-set criterion proves the old map closed. The same
saturation identity for singletons proves injectivity, and the quotient
projection proves continuity. -/
theorem adjunction_old_isClosedEmbedding {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} : IsClosedEmbedding (@oldInclusion n X k a) := by
  classical
  let : T2Space (𝔻 n) := by unfold TopCat.disk; infer_instance
  have hb : Function.Injective (diskBoundaryInclusion n) :=
    (TopCat.mono_iff_injective _).mp inferInstance
  let R := fun p q : X ⊕ (Fin k × 𝔻 n) ↦ ∃ (i : Fin k) (z : ∂𝔻 n),
    p = Sum.inr (i, diskBoundaryInclusion n z) ∧ q = Sum.inl (a i z)
  let sat (A : Set X) : X ⊕ (Fin k × 𝔻 n) → Prop
    | .inl x => x ∈ A
    | .inr p => ∃ z : ∂𝔻 n, diskBoundaryInclusion n z = p.2 ∧ a p.1 z ∈ A
  have hs (A : Set X) {p q} (h : Relation.EqvGen R p q) : sat A p ↔ sat A q := by
    induction h with
    | rel p q h =>
      obtain ⟨i, z, rfl, rfl⟩ := h
      change (∃ w, diskBoundaryInclusion n w = diskBoundaryInclusion n z ∧ a i w ∈ A) ↔ a i z ∈ A
      constructor
      · rintro ⟨w, hw, ha⟩
        simpa only [hb hw] using ha
      · intro ha
        exact ⟨z, rfl, ha⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have himage (A : Set X) (p : X ⊕ (Fin k × 𝔻 n)) :
      Quotient.mk (Relation.EqvGen.setoid R) p ∈ oldInclusion '' A ↔ sat A p := by
    constructor
    · rintro ⟨x, hx, he⟩
      exact (hs A (Quotient.exact he)).mp hx
    · cases p with
      | inl x => intro hx; exact ⟨x, hx, rfl⟩
      | inr p =>
        rintro ⟨z, hz, ha⟩
        refine ⟨a p.1 z, ha, ?_⟩
        apply Quotient.sound
        apply Relation.EqvGen.symm
        apply Relation.EqvGen.rel
        exact ⟨p.1, z, by rw [hz], rfl⟩
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_quotient_mk'.comp continuous_inl) ?_ ?_
  · intro x y hxy
    have hy : oldInclusion y ∈ oldInclusion '' ({x} : Set X) :=
      ⟨x, mem_singleton x, hxy⟩
    exact ((himage {x} (.inl y)).mp hy).symm
  · intro A hA
    apply isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage.mp
    apply isClosed_sum_iff.mpr
    constructor
    · convert hA using 1
      ext x
      exact himage A (.inl x)
    · have hboundary : IsClosedEmbedding (diskBoundaryInclusion n) :=
        (diskBoundaryInclusion n).hom.continuous.isClosedEmbedding hb
      have hB (i : Fin k) : IsClosed ((diskBoundaryInclusion n) '' ((a i) ⁻¹' A)) :=
        hboundary.isClosedMap _ (hA.preimage (a i).continuous)
      have heq : Sum.inr ⁻¹' (Quotient.mk (Relation.EqvGen.setoid R) ⁻¹' (oldInclusion '' A)) =
          ⋃ i : Fin k, ({i} : Set (Fin k)) ×ˢ ((diskBoundaryInclusion n) '' ((a i) ⁻¹' A)) := by
        ext ⟨i, z⟩
        change Quotient.mk (Relation.EqvGen.setoid R) (.inr (i, z)) ∈ oldInclusion '' A ↔ _
        apply (himage A (.inr (i, z))).trans
        simp only [mem_iUnion, mem_prod, mem_singleton_iff, mem_image, mem_preimage]
        constructor
        · rintro ⟨w, hw, ha⟩
          exact ⟨i, rfl, w, ha, hw⟩
        · rintro ⟨j, rfl, w, ha, hw⟩
          exact ⟨w, hw, ha⟩
      have hclosed : IsClosed (⋃ i : Fin k, ({i} : Set (Fin k)) ×ˢ
          ((diskBoundaryInclusion n) '' ((a i) ⁻¹' A))) :=
        isClosed_iUnion_of_finite fun i ↦ isClosed_singleton.prod (hB i)
      convert hclosed using 1
      exact heq

/-- Every original stage of a finite disk-attachment tower is a closed
subspace with its original topology. Compose the one-step closed embeddings
along the stage witness; the terminal stage uses the identity map. Hatcher,
Appendix pp.519–520; the one-step proof above is an agent-written expansion.
The zero-length tower and empty spaces or attachment families are included. -/
theorem attachment_stage_isClosedEmbedding {d : ℕ} {X : TopCat.{u}} {T : Tower d X}
    {m : ℕ} {Y : TopCat.{u}} (S : Stage T m Y) : IsClosedEmbedding (stageInclusion S) := by
  induction S with
  | last => exact IsClosedEmbedding.id
  | previous S ih => exact adjunction_old_isClosedEmbedding.comp ih

end HolomorphicAnosov.FiniteCellAdjunction
