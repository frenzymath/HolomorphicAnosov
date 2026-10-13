import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.OriginLoopNull

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem cover_simplyConnected {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [PathConnectedSpace X] (b : X)
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    SimplyConnectedSpace (PathCover b) := by
  let _ := pathCoverTopology b
  let _ := cover_pathConnected b hsemi
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro e μ
  let e0 : PathCover b := ⟨b, Path.Homotopic.Quotient.refl b⟩
  let ρ := PathConnectedSpace.somePath e0 e
  have hq : (mk ρ).trans ((mk μ).trans (mk ρ).symm) = Path.Homotopic.Quotient.refl e0 :=
    Path.Homotopic.Quotient.eq.mpr (origin_loop_null b hsemi (ρ.trans (μ.trans ρ.symm)))
  apply Path.Homotopic.Quotient.eq.mp
  change mk μ = Path.Homotopic.Quotient.refl e
  calc
    mk μ = (mk ρ).symm.trans (((mk ρ).trans ((mk μ).trans (mk ρ).symm)).trans
        (mk ρ)) := by
      simp only [← trans_assoc, symm_trans, refl_trans]
      rw [trans_assoc, symm_trans, trans_refl]
    _ = (mk ρ).symm.trans ((Path.Homotopic.Quotient.refl e0).trans (mk ρ)) := by rw [hq]
    _ = Path.Homotopic.Quotient.refl e := by simp

end
end HolomorphicAnosov
