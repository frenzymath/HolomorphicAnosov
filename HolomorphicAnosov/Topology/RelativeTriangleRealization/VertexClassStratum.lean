import HolomorphicAnosov.Topology.RelativeTriangleRealization.VertexClassFinite
import HolomorphicAnosov.Topology.RelativeTriangleRealization.VertexRepresentativeStep
import HolomorphicAnosov.Topology.RelativeTriangleRealization.VertexRepresentativeStep

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
# Vertex strata in the paired-triangle quotient

Source: Hatcher, *Algebraic Topology*, pp.103--104 and p.167. -/

/-- A quotient class containing a triangle vertex has only vertex
representatives. -/
theorem vertexClass_classifies {m : ℕ}
    (pair : Occurrence m → Occurrence m)
    (hinv : Function.Involutive pair) :
    ∀ (v : Fin m × Fin 3) (x : Fin m × Simplex 2),
      vertex pair v = Quotient.mk _ x →
        ∃ w : Fin m × Fin 3,
          x = (w.1, Convexity.StdSimplex.single w.2) := by
  let P : Fin m × Simplex 2 → Prop := fun y ↦
    ∃ w : Fin m × Fin 3, y = (w.1, Convexity.StdSimplex.single w.2)
  have hpres (a b : Fin m × Simplex 2) (hab : pointRelation pair a b) :
      P a → P b := by
    exact vertex_representative_step pair hab
  have hsymm (a b : Fin m × Simplex 2) (hab : pointRelation pair a b) :
      pointRelation pair b a := by
    obtain ⟨o, t, rfl, rfl⟩ := hab
    exact ⟨pair o, t, rfl, by rw [hinv]⟩
  have hclasses (a b : Fin m × Simplex 2)
      (h : Relation.EqvGen (pointRelation pair) a b) : P a ↔ P b := by
    induction h with
    | rel a b hab =>
        exact ⟨hpres a b hab, hpres b a (hsymm a b hab)⟩
    | refl a => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  intro v x h
  have hv : P (v.1, Convexity.StdSimplex.single v.2) := ⟨v, rfl⟩
  exact (hclasses _ x (Quotient.exact h)).mp hv


end HolomorphicAnosov.RelativeTriangleRealization
