import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Conway's disk connection to a complementary component

Source: Conway, Functions of One Complex Variable I, second edition,
Chapter VII Proposition 1.2, printed p.143, final paragraph of the written proof.
-/

open Set Metric

namespace HolomorphicAnosov

/-- A point within distance `δ` of the domain complement shares a sphere-complement
component with a point of that complement, provided all points of `K` have distance
at least `δ` from it. Source: Conway VII.1.2, p.143.

Choose `w` outside `U` with `dist z w < δ`. The disk of radius `δ` about `w`
contains `z` and `w` and misses `K`, since distance to the complement is bounded
above by distance to `w`. Its continuous image in the one-point compactification
is connected. Component maximality places both points in the same component of
the complement of `K`. Monotonicity then puts the whole component of the complement
of `U` at `w` in that component. -/
theorem conway_exhaustion_near_complement
    {U K : Set ℂ} (hKU : K ⊆ U) (hUc : Uᶜ.Nonempty)
    {δ : ℝ} (hδ : 0 < δ) (hKdist : ∀ z ∈ K, δ ≤ infDist z Uᶜ)
    {z : ℂ} (hz : infDist z Uᶜ < δ) :
    ∃ w ∈ Uᶜ,
      connectedComponentIn (OnePoint.some '' U)ᶜ (OnePoint.some w) ⊆
        connectedComponentIn (OnePoint.some '' K)ᶜ (OnePoint.some z) := by
  obtain ⟨w, hw, hzw⟩ := (infDist_lt_iff hUc).mp hz
  have hball : OnePoint.some '' ball w δ ⊆ (OnePoint.some '' K)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩ hmem
    obtain ⟨y, hy, heq⟩ := hmem
    have hyv : y = v := OnePoint.coe_injective heq
    subst y
    exact (hKdist v hy).not_gt ((infDist_le_dist_of_mem hw).trans_lt hv)
  have hconn : IsPreconnected (OnePoint.some '' ball w δ) :=
    isPreconnected_ball.image _ OnePoint.continuous_coe.continuousOn
  have hwcomp : OnePoint.some w ∈
      connectedComponentIn (OnePoint.some '' K)ᶜ (OnePoint.some z) :=
    hconn.subset_connectedComponentIn ⟨z, hzw, rfl⟩ hball
      ⟨w, mem_ball_self hδ, rfl⟩
  refine ⟨w, hw, ?_⟩
  rw [connectedComponentIn_eq hwcomp]
  exact connectedComponentIn_mono _ (compl_subset_compl.mpr (image_mono hKU))

end HolomorphicAnosov
