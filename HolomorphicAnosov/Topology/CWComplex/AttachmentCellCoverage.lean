import HolomorphicAnosov.Topology.CWComplex.AttachmentCells
import Mathlib.Tactic

/-! Coverage by original cells in finite disk-attachment towers.
Source: Hatcher, Algebraic Topology, Appendix pp.519–520. -/

noncomputable section
open Set TopCat
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- A closed disk point lies either in the open disk or on its boundary.
This is the scalar dichotomy `r < 1 ∨ r = 1` under `r ≤ 1`. -/
theorem disk_point_interior_or_boundary (n : ℕ) (z : 𝔻 n) :
    (∃ b : 𝔹 n, ballInclusion n b = z) ∨
      (∃ b : ∂𝔻 n, diskBoundaryInclusion n b = z) := by
  obtain ⟨⟨v, hv⟩⟩ := z
  rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hv) with hlt | heq
  · exact Or.inl ⟨⟨⟨v, Metric.mem_ball.mpr hlt⟩⟩, rfl⟩
  · exact Or.inr ⟨⟨⟨v, Metric.mem_sphere.mpr heq⟩⟩, rfl⟩

/-- A fresh characteristic map agrees with its attaching map on the boundary.
Source: Hatcher Appendix p.519. This is one generator of the defining equivalence
relation, and therefore holds for arbitrary, possibly noninjective attachments. -/
theorem newCharacteristic_boundary {n : ℕ} {X : TopCat.{u}} {k : ℕ}
    {a : Fin k → C(∂𝔻 n, X)} (i : Fin k) (z : ∂𝔻 n) :
    newCharacteristic (a := a) i (diskBoundaryInclusion n z) = oldInclusion (a i z) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨i, z, rfl, rfl⟩)

/-- Original open cells cover every finite attachment tower.
Source: Hatcher Appendix pp.519–520. Induct on the tower. A zero-stage point is
its own zero-cell. At an attachment choose a quotient representative. Old points
are covered by retained cells. A new disk point is either interior, hence in its
fresh cell, or boundary, hence identified with an old point already covered. -/
theorem tower_openCell_cover {d : ℕ} {X : TopCat.{u}} (T : Tower d X) :
    (⋃ (n : ℕ) (c : Cell T n), openCell c) = Set.univ := by
  have covers : ∀ {d : ℕ} {X : TopCat.{u}} (T : Tower d X) (x : X),
      ∃ (n : ℕ) (c : Cell T n), x ∈ openCell c := by
    intro d X T
    induction T with
    | points X finite discrete =>
      intro x
      refine ⟨0, .point x, ?_⟩
      exact ⟨⟨⟨0, by simp⟩⟩, rfl⟩
    | @attach d X T k a ih =>
      intro x
      refine Quotient.inductionOn x ?_
      intro p
      cases p with
      | inl y =>
        obtain ⟨n, c, b, hb⟩ := ih y
        exact ⟨n, .old c, b, congrArg oldInclusion hb⟩
      | inr p =>
        obtain ⟨i, z⟩ := p
        rcases disk_point_interior_or_boundary (d + 1) z with ⟨b, rfl⟩ | ⟨b, rfl⟩
        · exact ⟨d + 1, .fresh i, b, rfl⟩
        · obtain ⟨n, c, v, hv⟩ := ih (a i b)
          refine ⟨n, .old c, v, ?_⟩
          exact (congrArg oldInclusion hv).trans (newCharacteristic_boundary i b).symm
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨n, c, hc⟩ := covers T x
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨c, hc⟩⟩

end HolomorphicAnosov.FiniteCellAdjunction
