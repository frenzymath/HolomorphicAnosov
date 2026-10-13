import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Connected.PathConnected

open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov
universe u v
/-- Attaching path-connected spaces along nonempty subspaces preserves path connectedness.
Source: Hatcher, Algebraic Topology, Proposition 1.26 pp.50–51. Every new point joins
an attaching point within its attached space, and then joins a fixed old point.
The pushout and coproduct universal properties ensure that these are all points. -/
theorem attachCells_pathConnectedSpace
    {α : Type v} {A B : α → TopCat.{u}} (g : ∀ a, A a ⟶ B a)
    {X Y : TopCat.{u}} [PathConnectedSpace X] (f : X ⟶ Y)
    (c : HomotopicalAlgebra.AttachCells.{u} g f)
    (hA : ∀ a, Nonempty (A a)) (hB : ∀ a, PathConnectedSpace (B a)) :
    PathConnectedSpace Y := by
  classical
  obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := X)
  have hjoin : ∀ y : Y, Joined (f x₀) y := by
    intro y
    obtain ⟨x, rfl⟩ | ⟨z, rfl⟩ :=
      Types.eq_or_eq_of_isPushout (c.isPushout.map (forget TopCat)) y
    · exact (PathConnectedSpace.joined x₀ x).map f.hom.continuous
    · obtain ⟨i, b, hb⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget TopCat) c.isColimit₂) z
      obtain ⟨a⟩ := hA (c.π i.as)
      have : PathConnectedSpace (B (c.π i.as)) := hB _
      have h₁ := (PathConnectedSpace.joined x₀ (c.g₁ (c.cofan₁.inj i.as a))).map
        f.hom.continuous
      have h₂ := (PathConnectedSpace.joined (g (c.π i.as) a) b).map
        (c.cell i.as).hom.continuous
      have heq : f (c.g₁ (c.cofan₁.inj i.as a)) = c.cell i.as (g (c.π i.as) a) := by
        have h := congrArg (fun k ↦ k a)
          (show c.cofan₁.inj i.as ≫ c.g₁ ≫ f = g (c.π i.as) ≫ c.cell i.as by
            rw [c.isPushout.w, ← Category.assoc, c.hm]
            rfl)
        exact h
      rw [heq] at h₁
      have heq₂ : c.cell i.as b = c.g₂ z := by
        change c.g₂ (c.cofan₂.inj i.as b) = c.g₂ z
        exact congrArg c.g₂ hb
      rw [heq₂] at h₂
      exact h₁.trans h₂
  exact ⟨⟨f x₀⟩, fun y z ↦ (hjoin y).symm.trans (hjoin z)⟩
end HolomorphicAnosov
