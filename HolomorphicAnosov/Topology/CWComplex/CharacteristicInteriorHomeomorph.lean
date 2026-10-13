import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.PartialHomeomorph.Basic

namespace HolomorphicAnosov

/-- The characteristic map restricts to a homeomorphism from its open disk
onto the open cell. Source: Hatcher, Algebraic Topology, §0, definition of
CW structure. The CW characteristic partial equivalence and its continuous
inverse define a partial homeomorphism. Restrict it to its source and target,
then identify those sets with the open ball and open cell. -/
theorem cw_characteristic_interior_homeomorph
    {X : Type*} [TopologicalSpace X] (C : Set X) [Topology.CWComplex C]
    (k : ℕ) (i : Topology.RelCWComplex.cell C k) :
    ∃ e : Metric.ball (0 : Fin k → ℝ) 1 ≃ₜ Topology.CWComplex.openCell k i,
      ∀ x, (e x : X) = Topology.RelCWComplex.map k i x.val := by
  let P : PartialHomeomorph (Fin k → ℝ) X :=
    { toPartialEquiv := Topology.RelCWComplex.map k i
      continuousOn_toFun := by
        rw [Topology.RelCWComplex.source_eq]
        exact (Topology.RelCWComplex.continuousOn k i).mono Metric.ball_subset_closedBall
      continuousOn_invFun := Topology.RelCWComplex.continuousOn_symm k i }
  have hs : Metric.ball (0 : Fin k → ℝ) 1 = P.source :=
    (Topology.RelCWComplex.source_eq k i).symm
  have ht : P.target = Topology.CWComplex.openCell k i := by
    rw [← P.image_source_eq_target, ← hs]
    rfl
  refine ⟨(Homeomorph.setCongr hs).trans
    (P.toHomeomorphSourceTarget.trans (Homeomorph.setCongr ht)), ?_⟩
  intro x
  rfl

end HolomorphicAnosov
