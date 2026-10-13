import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.PathSheet

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem good_path_eq {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : GoodSet U) {x y : X} (η θ : Path x y)
    (hη : ∀ t, η t ∈ U) (hθ : ∀ t, θ t ∈ U) :
    ((Path.Homotopic.Quotient.mk η) : Path.Homotopic.Quotient x y) = (Path.Homotopic.Quotient.mk θ) := by
  have hloop : ∀ t, (η.trans θ.symm) t ∈ U := by
    have hr : Set.range (η.trans θ.symm) ⊆ U := by
      rw [Path.trans_range, Path.symm_range]
      exact union_subset (range_subset_iff.mpr hη) (range_subset_iff.mpr hθ)
    exact fun t ↦ hr ⟨t, rfl⟩
  have he : trans ((Path.Homotopic.Quotient.mk η) : Path.Homotopic.Quotient x y) (symm (Path.Homotopic.Quotient.mk θ)) = Path.Homotopic.Quotient.refl x :=
    Path.Homotopic.Quotient.eq.mpr (hU.2.2 x (by simpa using hη 0) _ hloop)
  calc
    ((Path.Homotopic.Quotient.mk η) : Path.Homotopic.Quotient x y) =
        (trans ((Path.Homotopic.Quotient.mk η) : Path.Homotopic.Quotient x y) (symm (Path.Homotopic.Quotient.mk θ))).trans (Path.Homotopic.Quotient.mk θ) := by simp
    _ = (Path.Homotopic.Quotient.refl x).trans (Path.Homotopic.Quotient.mk θ) := congrArg (fun q : Path.Homotopic.Quotient x x ↦ q.trans (Path.Homotopic.Quotient.mk θ)) he
    _ = (Path.Homotopic.Quotient.mk θ) := refl_trans _



end
end HolomorphicAnosov
