import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-- Implementation scratch for Hatcher's open-edge characteristic maps. A
point in the interior of a triangle face has one zero barycentric coordinate,
so equality with any other face point forces the same omitted coordinate
and the same ordered parameter. -/
theorem interior_face_eq {j k : Fin 3} (t s : Simplex 1)
    (ht : t ∈ interior 1) (h : face j t = face k s) : j = k ∧ t = s := by
  have hz (j : Fin 3) (s : Simplex 1) : (face j s).weights j = 0 := by
    change s.weights.mapDomain j.succAbove j = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact j.succAbove_ne a ha
  have hjk : j = k := by
    by_contra hne
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
    have hh := congrArg (fun z : Simplex 2 ↦ z.weights k) h
    rw [hz] at hh
    change t.weights.mapDomain j.succAbove k = 0 at hh
    rw [← ha, Finsupp.mapDomain_apply_of_injective j.succAbove_right_injective] at hh
    exact (ne_of_gt (ht a)) hh
  subst k
  refine ⟨rfl, ?_⟩
  apply Convexity.StdSimplex.ext
  have hw := congrArg Convexity.StdSimplex.weights h
  exact Finsupp.mapDomain_injective j.succAbove_right_injective hw


/-- An interior edge point has exactly the one- or two-point orbit dictated by
the face involution, with its ordered parameter unchanged.

Source: Hatcher, Algebraic Topology, pp.103–104 and the paired-edge construction
on p.167. The proof spells out the edge-interior class assertion used there.

Proof: An interior point of a face has zero weight exactly at its omitted
vertex, and strictly positive weights at both other vertices. Thus equality
with a point on another face forces equal omitted vertices and equal edge
parameters. Fix an occurrence o and an interior parameter t. The set formed
by its point and its paired point is invariant under each generating face
relation: face uniqueness reduces a step to applying the pairing, and two
steps cancel by involutivity. The generating relation is symmetric for the
same reason. Induction over its equivalence closure preserves membership
in this two-point set. Quotient equality therefore implies membership in
that set. Conversely an unchanged point has the same class, and its partner
is identified by a single generating relation. This includes fixed faces,
pairings within one triangle, and arbitrary vertex identifications. -/
theorem edgeInterior_class_iff {m : ℕ} (pair : Occurrence m → Occurrence m)
    (hinv : Function.Involutive pair) (o : Occurrence m)
    (t : Simplex 1) (ht : t ∈ interior 1) (x : Fin m × Simplex 2) :
    edge pair o t = Quotient.mk _ x ↔
      x = (o.1, face o.2 t) ∨ x = ((pair o).1, face (pair o).2 t) := by
  have hface (j k : Fin 3) (s : Simplex 1) (h : face j t = face k s) :
      j = k ∧ t = s := interior_face_eq t s ht h
  have hpoint (a b : Occurrence m) (s : Simplex 1)
      (h : (a.1, face a.2 t) = (b.1, face b.2 s)) : a = b ∧ t = s := by
    have he := hface a.2 b.2 s (congrArg Prod.snd h)
    exact ⟨Prod.ext (congrArg (fun z : Fin m × Simplex 2 ↦ z.1) h) he.1, he.2⟩
  let P (y : Fin m × Simplex 2) : Prop :=
    y = (o.1, face o.2 t) ∨ y = ((pair o).1, face (pair o).2 t)
  have hpres (a b : Fin m × Simplex 2) (hab : pointRelation pair a b) : P a → P b := by
    obtain ⟨p, s, rfl, rfl⟩ := hab
    rintro (h | h)
    · obtain ⟨hp, hs⟩ := hpoint o p s h.symm
      subst p; subst s
      exact Or.inr rfl
    · obtain ⟨hp, hs⟩ := hpoint (pair o) p s h.symm
      subst p; subst s
      exact Or.inl (by rw [hinv])
  have hsymm (a b : Fin m × Simplex 2) (hab : pointRelation pair a b) :
      pointRelation pair b a := by
    obtain ⟨p, s, rfl, rfl⟩ := hab
    exact ⟨pair p, s, rfl, by rw [hinv]⟩
  have hclasses (a b : Fin m × Simplex 2)
      (h : Relation.EqvGen (pointRelation pair) a b) : P a ↔ P b := by
    induction h with
    | rel a b hab => exact ⟨hpres a b hab, hpres b a (hsymm a b hab)⟩
    | refl a => rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  constructor
  · intro h
    exact (hclasses _ x (Quotient.exact h)).mp (Or.inl rfl)
  · rintro (rfl | rfl)
    · rfl
    · exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨o, t, rfl, rfl⟩)

/-- Equality of interior edge points forces equality of their pairing classes
and ordered parameters. The edge-class theorem gives either equal original
points or paired points; unique omitted face coordinates then identify the
occurrences and parameters. -/
theorem edgeInterior_eq_classes {m : ℕ} (pair : Occurrence m → Occurrence m)
    (hinv : Function.Involutive pair) {o p : Occurrence m}
    {t s : interior 1} (h : edge pair o t.val = edge pair p s.val) :
    edgeClass pair o = edgeClass pair p ∧ t = s := by
  have ho := (edgeInterior_class_iff pair hinv o t.val t.property
    (p.1,face p.2 s.val)).mp h
  rcases ho with ho | ho
  · have hf := interior_face_eq t.val s.val t.property (congrArg Prod.snd ho).symm
    have hp : o = p := Prod.ext (congrArg Prod.fst ho).symm hf.1
    exact ⟨congrArg (edgeClass pair) hp,Subtype.ext hf.2⟩
  · have hf := interior_face_eq t.val s.val t.property (congrArg Prod.snd ho).symm
    have hp : pair o = p := Prod.ext (congrArg Prod.fst ho).symm hf.1
    exact ⟨Quotient.sound (Relation.EqvGen.rel _ _ hp.symm),Subtype.ext hf.2⟩


end HolomorphicAnosov.RelativeTriangleRealization
