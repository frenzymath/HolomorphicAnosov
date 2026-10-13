import Mathlib.Basic.Finite.Defs
import HolomorphicAnosov.Topology.CWComplex.AttachmentCells
import HolomorphicAnosov.Topology.CWComplex.AttachmentTower
import Mathlib.Data.Fintype.EquivFin

/-! Finiteness of the original cells of a finite disk-attachment tower.
Source: Hatcher, Algebraic Topology, Appendix pp.519–520, finite CW complexes
and their original cells. The proof counts the labels of the construction. -/

open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- The original cell labels of a finite attachment tower form a finite type.

Source: Hatcher Appendix pp.519–520. Induct on the tower. In the initial
stage every label comes from a point of the finite initial space. At a successor,
every label is either a retained old label or one of the finitely many new disk
labels. Thus the old labels disjoint union the new labels surject onto all labels,
and finiteness passes to their image. Empty initial spaces, empty attachment
families and the zero-stage tower are included. -/
theorem tower_finite_cells {d : ℕ} {X : TopCat.{u}} (T : Tower d X) :
    Finite (Σ n, Cell T n) := by
  let Label : {d : ℕ} → {X : TopCat.{u}} → Tower d X → Type (u + 1) :=
    fun {_} {_} T ↦ Tower.rec
      (motive := fun {_} {_} _ ↦ Type (u + 1))
      (fun X _ _ ↦ ULift.{u+1} X)
      (fun _ k _ L ↦ L ⊕ ULift.{u+1} (Fin k)) T
  let decode : {d : ℕ} → {X : TopCat.{u}} → (T : Tower d X) → Label T → Σ n, Cell T n :=
    fun {_} {_} T ↦ Tower.rec
      (motive := fun {_} {_} T ↦ Label T → Σ n, Cell T n)
      (fun X finite discrete x ↦ ⟨0, .point x.down⟩)
      (fun T k a f x ↦ match x with
        | .inl z => ⟨(f z).1, .old (f z).2⟩
        | .inr i => ⟨_, .fresh i.down⟩) T
  have hsurj : ∀ {d : ℕ} {X : TopCat.{u}} (T : Tower d X),
      Function.Surjective (decode T) := by
    intro d X T ⟨n,c⟩
    induction c with
    | point x => exact ⟨ULift.up x, rfl⟩
    | @old d n X T k a c ih =>
      obtain ⟨z,hz⟩ := ih
      refine ⟨.inl z, ?_⟩
      change (⟨(decode T z).1, .old (decode T z).2⟩ : Σ n, Cell (T.attach k a) n) = _
      rw [hz]
    | fresh i => exact ⟨.inr (ULift.up i), rfl⟩
  have hfinite : ∀ {d : ℕ} {X : TopCat.{u}} (T : Tower d X), Finite (Label T) := by
    intro d X T
    induction T with
    | points X finite discrete =>
      let := finite
      dsimp [Label]
      infer_instance
    | attach T k a ih =>
      let := ih
      change Finite (Label T ⊕ ULift.{u+1} (Fin k))
      infer_instance
  let := hfinite T
  exact Finite.of_surjective (decode T) (hsurj T)

end HolomorphicAnosov.FiniteCellAdjunction
