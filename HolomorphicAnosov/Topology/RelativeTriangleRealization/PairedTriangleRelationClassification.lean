import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic
import HolomorphicAnosov.Topology.RelativeTriangleRealization.InteriorClasses
import HolomorphicAnosov.Topology.RelativeTriangleRealization.EdgeInteriorClasses
import HolomorphicAnosov.Topology.RelativeTriangleRealization.VertexClassStratum

open Set Filter Topology _root_.Topology
noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
Source: Hatcher, *Algebraic Topology*, p.167 and Appendix A.3, pp.521–522.
The generated relation splits into a diagonal class, a finite vertex class,
or one of the two orientations of an open-face pairing.  This classification
is the combinatorial input for the closedness provider in the quotient
construction.
-/
theorem pairedTriangle_eqvGen_classification {m : ℕ}
    (pair : Occurrence m → Occurrence m)
    (hinv : Function.Involutive pair) {a b : Fin m × Simplex 2}
    (h : Relation.EqvGen (pointRelation pair) a b) :
    a = b ∨
      ((∃ v : Fin m × Fin 3, a = (v.1, Convexity.StdSimplex.single v.2)) ∧
       (∃ v : Fin m × Fin 3, b = (v.1, Convexity.StdSimplex.single v.2)) ∧
       Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)) a =
         Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)) b) ∨
      (∃ o : Occurrence m, ∃ t : Simplex 1,
        a = (o.1, face o.2 t) ∧ b = ((pair o).1, face (pair o).2 t)) ∨
      (∃ o : Occurrence m, ∃ t : Simplex 1,
        b = (o.1, face o.2 t) ∧ a = ((pair o).1, face (pair o).2 t)) := by
  have hq : Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)) a =
      Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)) b := Quotient.sound h
  by_cases ha : a.2 ∈ interior 2
  · left
    have hi := (triangleInterior_eq_iff pair a.1 b.1 a.2 b.2 ha).mp hq
    exact Prod.ext hi.1 hi.2
  by_cases hva : ∃ v : Fin m × Fin 3, a = (v.1, Convexity.StdSimplex.single v.2)
  · right; left
    refine ⟨hva, ?_, hq⟩
    obtain ⟨v, hv⟩ := hva
    have hvq : vertex pair v = Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)) a := by
      rw [vertex, triangle]
      exact congrArg (Quotient.mk (Relation.EqvGen.setoid (pointRelation pair))) hv.symm
    obtain ⟨w, hw⟩ := vertexClass_classifies pair hinv v b (hvq.trans hq)
    exact ⟨w, hw⟩
  · have hbound : ∃ j : Fin 3, ∃ u : Simplex 1, a.2 = face j u := by
      have hex : ∃ j : Fin 3, ¬ (0 : ℝ) < a.2.weights j := by
        by_contra hpos
        push Not at hpos
        exact ha hpos
      obtain ⟨j, hj⟩ := hex
      have hj0 : a.2.weights j = 0 := le_antisymm (not_lt.mp hj) (a.2.nonneg j)
      have hr : a.2 ∈ Set.range (Convexity.StdSimplex.map j.succAbove) := by
        rw [Convexity.StdSimplex.mem_range_map_iff]
        intro x hx
        rw [Fin.range_succAbove] at hx
        have : x = j := by simpa using hx
        subst x
        exact hj0
      obtain ⟨u, hu⟩ := hr
      exact ⟨j, u, hu.symm⟩
    obtain ⟨j, u, hau⟩ := hbound
    have hu : u ∈ interior 1 := by
      by_contra hnu
      obtain ⟨v, hv⟩ := face_boundary_vertex hnu
      apply hva
      exact ⟨(a.1, v), Prod.ext rfl (hau.trans hv)⟩
    have he := (edgeInterior_class_iff pair hinv (a.1, j) u hu b).mp (by
      rw [show edge pair (a.1, j) u = Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)) a by
        rw [edge, triangle]
        exact congrArg (Quotient.mk (Relation.EqvGen.setoid (pointRelation pair)))
          (Prod.ext rfl hau.symm)]
      exact hq)
    rcases he with he | he
    · left
      exact Prod.ext (congrArg Prod.fst he).symm (hau.trans (congrArg Prod.snd he).symm)
    · exact Or.inr (Or.inr (Or.inl ⟨(a.1, j), u, Prod.ext rfl hau, he⟩))

end HolomorphicAnosov.RelativeTriangleRealization
