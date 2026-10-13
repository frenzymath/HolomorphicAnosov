import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.StoppedLift

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem stoppedLift_continuous {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {b x : X}
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x))
    (α : Path b x) :
    letI := pathCoverTopology b
    Continuous (stoppedLift α) := by
  let := pathCoverTopology b
  apply (sheets_basis b hsemi).continuous_iff.mpr
  rintro S ⟨U, a, hU, ha, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have htU : α t ∈ U := sheet_endpoint_mem ht
  obtain ⟨l, r, htI, hInhds, hI⟩ := exists_Icc_mem_subset_of_mem_nhds
    (α.continuous.continuousAt.preimage_mem_nhds (hU.1.mem_nhds htU))
  apply Filter.mem_of_superset hInhds
  intro s hs
  rw [← sheet_recenter ht]
  refine ⟨α.subpath t s, ?_, stoppedClass_trans α t s⟩
  intro u
  have hu : α.subpath t s u ∈ α '' Set.uIcc t s := by
    rw [← Path.range_subpath]
    exact ⟨u, rfl⟩
  obtain ⟨v, hv, hev⟩ := hu
  have hvI := Set.ordConnected_Icc.uIcc_subset htI hs hv
  exact hev ▸ hI hvI

end
end HolomorphicAnosov
