import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Subpath
import Mathlib.Topology.Homotopy.Lifting
import HolomorphicAnosov.Topology.PointedPathClassUniversalCover.SheetProjectionSurjective

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section
open Set Function Filter
open Path.Homotopic.Quotient

theorem good_neighborhood {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X]
    (hsemi : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ p : Path x x, (∀ t, p t ∈ U) → p.Homotopic (Path.refl x))
    (x : X) {O : Set X} (hO : IsOpen O) (hx : x ∈ O) :
    ∃ U, GoodSet U ∧ x ∈ U ∧ U ⊆ O := by
  obtain ⟨N, hN, hxN, hnull⟩ := hsemi x
  obtain ⟨U, ⟨hU, hxU, hpath⟩, hsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp ((hO.inter hN).mem_nhds ⟨hx, hxN⟩)
  refine ⟨U, ⟨hU, hpath, ?_⟩, hxU, fun y hy ↦ (hsub hy).1⟩
  intro y hy μ hμ
  let ρ := (hpath.joinedIn x hxU y hy).somePath
  have hρ : ∀ t, ρ t ∈ U := (hpath.joinedIn x hxU y hy).somePath_mem
  have hwhole : ∀ t, (ρ.trans (μ.trans ρ.symm)) t ∈ N := by
    have hcontain : range (ρ.trans (μ.trans ρ.symm)) ⊆ U := by
      rw [Path.trans_range, Path.trans_range, Path.symm_range]
      exact union_subset (range_subset_iff.mpr hρ)
        (union_subset (range_subset_iff.mpr hμ) (range_subset_iff.mpr hρ))
    exact fun t ↦ (hsub (hcontain ⟨t, rfl⟩)).2
  have hq : (Path.Homotopic.Quotient.mk ρ).trans
      ((Path.Homotopic.Quotient.mk μ).trans (Path.Homotopic.Quotient.mk ρ).symm) =
      Path.Homotopic.Quotient.refl x := Path.Homotopic.Quotient.eq.mpr (hnull _ hwhole)
  apply Path.Homotopic.Quotient.eq.mp
  change Path.Homotopic.Quotient.mk μ = Path.Homotopic.Quotient.refl y
  calc
    Path.Homotopic.Quotient.mk μ =
      (Path.Homotopic.Quotient.mk ρ).symm.trans
        (((Path.Homotopic.Quotient.mk ρ).trans
          ((Path.Homotopic.Quotient.mk μ).trans (Path.Homotopic.Quotient.mk ρ).symm)).trans
            (Path.Homotopic.Quotient.mk ρ)) := by
      simp only [← trans_assoc, symm_trans, refl_trans]
      rw [trans_assoc, symm_trans, trans_refl]
    _ = (Path.Homotopic.Quotient.mk ρ).symm.trans
      ((Path.Homotopic.Quotient.refl x).trans (Path.Homotopic.Quotient.mk ρ)) := by rw [hq]
    _ = Path.Homotopic.Quotient.refl y := by simp

end
end HolomorphicAnosov
