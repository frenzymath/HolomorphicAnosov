import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Logic.Relation

/-!
# Finite segment chains in an open connected set

This file proves that points in an open preconnected subset of a normed space can be joined by finitely many segments. (Gallier–Xu, Thm. C.1)
-/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- Any two points of an open preconnected subset of a real normed space are joined by finitely many segments contained in the set. (Gallier–Xu, Thm. C.1) -/
theorem open_preconnected_segment_chain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : IsOpen s) (hc : IsPreconnected s)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    Relation.ReflTransGen (fun x y : E ↦ segment ℝ x y ⊆ s) a b := by
  let : PreconnectedSpace s := Subtype.preconnectedSpace hc
  have hlocal : IsLocallyConstant
      (fun z : s ↦ Relation.ReflTransGen (fun x y : E ↦ segment ℝ x y ⊆ s) a z) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs z z.property
    have hevent : ∀ᶠ w : s in 𝓝 z, (w : E) ∈ Metric.ball (z : E) r :=
      continuous_subtype_val.continuousAt (Metric.ball_mem_nhds (z : E) hr)
    filter_upwards [hevent] with w hw
    apply propext
    constructor
    · intro h
      exact h.tail (((convex_ball (z : E) r).segment_subset hw
        (Metric.mem_ball_self hr)).trans hball)
    · intro h
      exact h.tail (((convex_ball (z : E) r).segment_subset
        (Metric.mem_ball_self hr) hw).trans hball)
  exact (hlocal.apply_eq_of_preconnectedSpace ⟨a, ha⟩ ⟨b, hb⟩).mp
    Relation.ReflTransGen.refl

end HolomorphicAnosov

