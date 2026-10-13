import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetEndpointMem

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem sheet_recenter {X : Type*} [TopologicalSpace X] {b : X}
    {U : Set X} {a e : PathCover b} (he : e ∈ PathSheet U a) :
    PathSheet U e = PathSheet U a := by
  rcases he with ⟨η, hη, hclass⟩
  ext d
  constructor
  · rintro ⟨μ, hμ, hd⟩
    refine ⟨η.trans μ, ?_, ?_⟩
    · exact range_subset_iff.mp (by
        rw [Path.trans_range]
        exact union_subset (range_subset_iff.mpr hη) (range_subset_iff.mpr hμ))
    · change a.2.trans (trans (Path.Homotopic.Quotient.mk η) (Path.Homotopic.Quotient.mk μ)) = d.2
      rw [← trans_assoc, hclass, hd]
  · rintro ⟨μ, hμ, hd⟩
    refine ⟨η.symm.trans μ, ?_, ?_⟩
    · exact range_subset_iff.mp (by
        rw [Path.trans_range, Path.symm_range]
        exact union_subset (range_subset_iff.mpr hη) (range_subset_iff.mpr hμ))
    · change e.2.trans (trans (symm (Path.Homotopic.Quotient.mk η)) (Path.Homotopic.Quotient.mk μ)) = d.2
      rw [← hclass, ← trans_assoc, trans_assoc a.2, trans_symm, trans_refl]
      exact hd

end
end HolomorphicAnosov
