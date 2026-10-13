import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Topology.Connected.LocallyConnected

open Set

namespace HolomorphicAnosov.Analysis.Complex

/-- A continuous nonvanishing complex-valued function on an open set whose connected
components are simply connected admits a continuous logarithm.

Source: Conway, Functions of One Complex Variable II, Chapter 14 Lemma 5.4, p.49,
componentwise choice of logarithm branches; Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp` supplies the branch on each component.
Choose a branch once for each component as a set. Components of an open set in a locally
path connected space are open. On each component the assembled function is exactly the
chosen continuous branch, proving continuity locally and the exponential identity.
The empty open set is allowed: all the requirements are then vacuous. -/
theorem continuous_logarithm_of_simplyConnected_components
    {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    {U : Set X} (hU : IsOpen U)
    (hsc : ∀ x ∈ U, IsSimplyConnected (connectedComponentIn U x))
    {g : X → ℂ} (hg : ContinuousOn g U) (hg0 : ∀ x ∈ U, g x ≠ 0) :
    ∃ L : X → ℂ, ContinuousOn L U ∧ EqOn (_root_.Complex.exp ∘ L) g U := by
  classical
  have hbranch (C : Set X) : ∃ L : X → ℂ,
      (∃ x ∈ U, C = connectedComponentIn U x) →
        ContinuousOn L C ∧ EqOn (_root_.Complex.exp ∘ L) g C := by
    by_cases hC : ∃ x ∈ U, C = connectedComponentIn U x
    · obtain ⟨x, hx, rfl⟩ := hC
      obtain ⟨L, hLc, hLe⟩ := _root_.Complex.exists_continuousOn_eqOn_exp_comp
        (hsc x hx) hU.connectedComponentIn
        (hg.mono (connectedComponentIn_subset U x)) (by
          rintro ⟨z, hz, hzero⟩
          exact hg0 z (connectedComponentIn_subset U x hz) hzero)
      exact ⟨L, fun _ ↦ ⟨hLc, hLe⟩⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ (hC h).elim⟩
  choose F hF using hbranch
  let L : X → ℂ := fun x ↦ F (connectedComponentIn U x) x
  refine ⟨L, ?_, ?_⟩
  · intro x hx
    have hEq : EqOn L (F (connectedComponentIn U x)) (connectedComponentIn U x) := by
      intro z hz
      dsimp [L]
      rw [← connectedComponentIn_eq hz]
    exact (((hF _ ⟨x, hx, rfl⟩).1.congr hEq).continuousAt
      (hU.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx))).continuousWithinAt
  · intro x hx
    exact (hF _ ⟨x, hx, rfl⟩).2 (mem_connectedComponentIn hx)

end HolomorphicAnosov.Analysis.Complex

