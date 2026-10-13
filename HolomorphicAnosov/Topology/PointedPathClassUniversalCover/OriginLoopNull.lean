import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.CoverPathConnected

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem origin_loop_null {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [PathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    ∀ loop : Path (⟨b, Path.Homotopic.Quotient.refl b⟩ : PathCover b) ⟨b, Path.Homotopic.Quotient.refl b⟩,
      loop.Homotopic (Path.refl (⟨b, Path.Homotopic.Quotient.refl b⟩ : PathCover b)) := by
  let _ := pathCoverTopology b
  intro loop
  let P : C(PathCover b, X) := ⟨Sigma.fst, endpoint_continuous b hsemi⟩
  let α : Path b b := loop.map P.continuous
  have cov := endpoint_covering b hsemi
  have hEq : (loop : unitInterval → PathCover b) = stoppedLift α :=
    cov.eq_of_comp_eq loop.continuous (stoppedLift_continuous hsemi α) rfl 0
      (loop.source.trans (stoppedLift_zero α).symm)
  have hEnd : (⟨b, mk α⟩ : PathCover b) = ⟨b, Path.Homotopic.Quotient.refl b⟩ := by
    rw [← stoppedLift_one α, ← hEq]
    exact loop.target
  have hα : mk α = Path.Homotopic.Quotient.refl b := eq_of_heq (Sigma.mk.inj hEnd).2
  apply Path.Homotopic.Quotient.eq.mp
  apply cov.injective_path_homotopic_map _ _
  change Path.Homotopic.Quotient.map (mk loop) P =
    Path.Homotopic.Quotient.map (mk (Path.refl (⟨b, Path.Homotopic.Quotient.refl b⟩ : PathCover b))) P
  rw [← mk_map, ← mk_map]
  exact hα



end
end HolomorphicAnosov
