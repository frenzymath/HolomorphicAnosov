import HolomorphicAnosov.Topology.RelativeTriangleRealization.InteriorClasses

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-- The open interior of each original triangle is an open embedded cell of
the paired-face quotient, without assumptions on the pairing. Source:
Hatcher, Algebraic Topology, pp.103–104, open-simplex topology.

Proof: The simplex interior is open because its finitely many barycentric
coordinates are continuous and strictly positive. Every interior point has
a singleton quotient class. Consequently the inverse image of the quotient
image of an open subset of that triangle interior is exactly that open subset
in the corresponding component of the finite disjoint union. This is open:
the triangle-label singleton is open in the discrete finite label space. The
quotient open-set criterion proves the restricted triangle map is open. It is
continuous by restriction and injective by the singleton-class theorem, hence
an open embedding. No separation or involution assumption is needed. -/
theorem triangleInterior_isOpenEmbedding {m : ℕ}
    (pair : Occurrence m → Occurrence m) (i : Fin m) :
    Topology.IsOpenEmbedding (fun t : interior 2 ↦ triangle pair i t.val) := by
  have hi : IsOpen (interior 2) := by
    change IsOpen (Set.ofPred (fun t : Simplex 2 ↦ ∀ j, 0 < t.weights j))
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦ isOpen_lt continuous_const
      (Convexity.StdSimplex.continuous_weights_apply ℝ j)
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (triangle pair i).continuous.comp continuous_subtype_val
  · intro t s h
    exact Subtype.ext ((triangleInterior_eq_iff pair i i t.val s.val t.property).mp h).2
  · intro U hU
    let q : Fin m × Simplex 2 → Space pair := Quotient.mk _
    have heq : q ⁻¹' ((fun t : interior 2 ↦ triangle pair i t.val) '' U) =
        ({i} : Set (Fin m)) ×ˢ (Subtype.val '' U) := by
      ext x
      constructor
      · rintro ⟨t, ht, he⟩
        have hx := (triangleInterior_eq_iff pair i x.1 t.val x.2 t.property).mp he
        exact ⟨hx.1.symm, ⟨t, ht, hx.2⟩⟩
      · rintro ⟨hx, t, ht, he⟩
        refine ⟨t, ht, ?_⟩
        change triangle pair i t.val = triangle pair x.1 x.2
        exact (triangleInterior_eq_iff pair i x.1 t.val x.2 t.property).mpr
          ⟨hx.symm, he⟩
    apply (isQuotientMap_quotient_mk' (s := Relation.EqvGen.setoid (pointRelation pair))).isOpen_preimage.mp
    change IsOpen (q ⁻¹' _)
    rw [heq]
    exact (isOpen_discrete _).prod (hi.isOpenMap_subtype_val U hU)

end HolomorphicAnosov.RelativeTriangleRealization
