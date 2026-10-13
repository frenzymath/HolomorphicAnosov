import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PrefixSheet

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

def prefixHomeomorph {X : Type*} [TopologicalSpace X] (b : X)
    (γ : (FundamentalGroup X b)ᵐᵒᵖ) :
    letI := pathCoverTopology b
    PathCover b ≃ₜ PathCover b := by
  letI := pathCoverTopology b
  refine { prefixEquiv b γ with continuous_toFun := ?_, continuous_invFun := ?_ }
  · apply continuous_generateFrom_iff.mpr
    rintro S ⟨U, a, hU, ha, rfl⟩
    have heq : prefixEquiv b γ ⁻¹' PathSheet U a =
        PathSheet U ((prefixEquiv b γ).symm a) := by
      ext e
      simpa using prefix_sheet γ U ((prefixEquiv b γ).symm a) e
    change IsOpen ((prefixEquiv b γ) ⁻¹' PathSheet U a)
    rw [heq]
    exact TopologicalSpace.isOpen_generateFrom_of_mem
      ⟨U, (prefixEquiv b γ).symm a, hU, ha, rfl⟩
  · apply continuous_generateFrom_iff.mpr
    rintro S ⟨U, a, hU, ha, rfl⟩
    have heq : (prefixEquiv b γ).symm ⁻¹' PathSheet U a =
        PathSheet U (prefixEquiv b γ a) := by
      ext e
      simpa using (prefix_sheet γ U a ((prefixEquiv b γ).symm e)).symm
    change IsOpen ((prefixEquiv b γ).symm ⁻¹' PathSheet U a)
    rw [heq]
    exact TopologicalSpace.isOpen_generateFrom_of_mem
      ⟨U, prefixEquiv b γ a, hU, ha, rfl⟩



end
end HolomorphicAnosov
