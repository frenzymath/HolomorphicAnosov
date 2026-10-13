import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PathCoverTopology

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem sheets_basis {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    (b : X) (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x)) :
    letI := pathCoverTopology b
    TopologicalSpace.IsTopologicalBasis (sheetFamily b) := by
  let := pathCoverTopology b
  refine ⟨?_, ?_, rfl⟩
  · rintro S ⟨U, a, hU, ha, rfl⟩ T ⟨V, c, hV, hc, rfl⟩ e ⟨heU, heV⟩
    obtain ⟨W, hW, heW, hsub⟩ := good_neighborhood hsemi e.1 (hU.1.inter hV.1)
      ⟨sheet_endpoint_mem heU, sheet_endpoint_mem heV⟩
    refine ⟨PathSheet W e, ⟨W, e, hW, heW, rfl⟩, self_mem_sheet heW, ?_⟩
    intro d hd
    constructor
    · rw [← sheet_recenter heU]
      exact sheet_mono (fun y hy ↦ (hsub hy).1) hd
    · rw [← sheet_recenter heV]
      exact sheet_mono (fun y hy ↦ (hsub hy).2) hd
  · apply eq_univ_of_forall
    intro e
    obtain ⟨U, hU, heU, _⟩ := good_neighborhood hsemi e.1 isOpen_univ (mem_univ _)
    exact mem_sUnion.mpr ⟨PathSheet U e, ⟨U, e, hU, heU, rfl⟩, self_mem_sheet heU⟩



end
end HolomorphicAnosov
