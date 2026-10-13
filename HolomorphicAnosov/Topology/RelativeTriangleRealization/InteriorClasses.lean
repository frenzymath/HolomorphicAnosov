import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-- A face point is never in the positive triangle interior: its omitted
barycentric coordinate is zero. -/
theorem face_not_interior (j : Fin 3) (s : Simplex 1) : face j s ∉ interior 2 := by
  intro h
  have hz : (face j s).weights j = 0 := by
    change s.weights.mapDomain j.succAbove j = 0
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a,ha⟩
    exact j.succAbove_ne a ha
  exact (ne_of_gt (h j)) hz


/-- A point in an open triangle has a singleton class in the paired-face
quotient. Source: Hatcher, Algebraic Topology, pp.103–104, the open-simplex
partition of a delta complex.

Proof: Every face has zero barycentric weight at its omitted vertex, so
neither endpoint of a generating relation is in an open triangle. Induction
on the generated equivalence relation shows that any related pair with an
interior endpoint consists of equal points. Reflexivity is immediate;
symmetry exchanges endpoints; transitivity carries interior membership
through the first equality and then applies the second. The reverse quotient
equality follows by substitution. The matching need not be involutive, and
no nonempty or separation assumption is used. -/
theorem triangleInterior_eq_iff {m : ℕ} (pair : Occurrence m → Occurrence m)
    (i j : Fin m) (t s : Simplex 2) (ht : t ∈ interior 2) :
    triangle pair i t = triangle pair j s ↔ i = j ∧ t = s := by
  have hclasses (a b : Fin m × Simplex 2)
      (h : Relation.EqvGen (pointRelation pair) a b) :
      a.2 ∈ interior 2 ∨ b.2 ∈ interior 2 → a = b := by
    induction h with
    | rel a b hab =>
      obtain ⟨o, z, rfl, rfl⟩ := hab
      rintro (ha | hb)
      · exact (face_not_interior o.2 z ha).elim
      · exact (face_not_interior (pair o).2 z hb).elim
    | refl a => exact fun _ ↦ rfl
    | symm a b hab ih => exact fun h ↦ (ih h.symm).symm
    | trans a b c hab hbc ihab ihbc =>
      rintro (ha | hc)
      · have hab' := ihab (Or.inl ha)
        have hbc' := ihbc (Or.inl (hab' ▸ ha))
        exact hab'.trans hbc'
      · have hbc' := ihbc (Or.inr hc)
        have hab' := ihab (Or.inr (hbc'.symm ▸ hc))
        exact hab'.trans hbc'
  constructor
  · intro h
    have hab := hclasses (i,t) (j,s) (Quotient.exact h) (Or.inl ht)
    exact Prod.mk.inj hab
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A positive triangle interior class cannot meet an edge image. Its quotient
class is a singleton, while every face point has a zero coordinate. -/
theorem triangleInterior_ne_edge {m : ℕ} (pair : Occurrence m → Occurrence m)
    (i : Fin m) (o : Occurrence m) (t : interior 2) (s : Simplex 1) :
    triangle pair i t.val ≠ edge pair o s := by
  intro h
  have he := (triangleInterior_eq_iff pair i o.1 t.val (face o.2 s) t.property).mp h
  exact face_not_interior o.2 s (he.2 ▸ t.property)


end HolomorphicAnosov.RelativeTriangleRealization
