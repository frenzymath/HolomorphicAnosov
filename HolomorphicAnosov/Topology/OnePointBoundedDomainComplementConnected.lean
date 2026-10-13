import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Basic

/-!
# Connected complements in the one-point compactification

This file transfers connectedness of a bounded planar complement to the sphere.
-/

open Set Metric
open scoped OnePoint

namespace HolomorphicAnosov

/-- If a bounded planar set has connected complement, its complement in the one-point compactification is connected. (Conway II, Thm. 5.5) -/
theorem onePoint_bounded_complement_connected {Q : Set ℂ}
    (hQ : Bornology.IsBounded Q) (hconn : IsConnected Qᶜ) :
    IsConnected ((OnePoint.some '' Q)ᶜ) := by
  have hinfty : (∞ : OnePoint ℂ) ∈ closure (OnePoint.some '' Qᶜ) := by
    by_contra hnot
    have hc := ((OnePoint.isClosed_iff_of_notMem hnot).mp isClosed_closure).2
    have hcomp : Bornology.IsBounded Qᶜ := hc.isBounded.subset (by
      intro z hz
      exact subset_closure ⟨z, hz, rfl⟩)
    have hu : Bornology.IsBounded (univ : Set ℂ) := by
      simpa using hQ.union hcomp
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ))
      (isCompact_univ_iff.mp
        (Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_univ, hu⟩))
  have heq : (OnePoint.some '' Q)ᶜ =
      insert ∞ (OnePoint.some '' Qᶜ) := by
    ext z
    cases z using OnePoint.rec <;> simp
  rw [heq]
  exact (hconn.image _ OnePoint.continuous_coe.continuousOn).subset_closure
    (subset_insert _ _) (insert_subset hinfty subset_closure)

end HolomorphicAnosov

