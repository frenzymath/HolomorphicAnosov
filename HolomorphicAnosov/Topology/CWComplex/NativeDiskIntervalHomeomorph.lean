import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-!
# Native maximum-norm disk as a disk times the interval

Source input: Fritsch–Piccinini, Cellular Structures in Topology, Theorem 2.2.2,
p.58, product-cell disk and boundary argument. This explicit last-coordinate
realization in Mathlib's maximum norm is an agent-written implementation for
the original interval-product CW construction.
-/

open Set _root_.Topology

namespace HolomorphicAnosov.Topology

/-- Splitting off the last coordinate identifies the native closed `(d+1)`-disk
with the native closed `d`-disk times the unit interval, with the precise affine
time coordinate required by the interval-product characteristic map.

Proof: Each coordinate of a point of the maximum-norm unit disk lies in `[-1,1]`.
Keep the first `d` coordinates and send the last coordinate `s` to `(s+1)/2`.
The inverse appends `2t-1` to the head coordinates. Coordinate norm bounds show
that both maps have their stated domains, and the affine identities prove they
are inverse. The forward map is continuous coordinatewise; compactness of the
closed finite-dimensional disk and Hausdorffness of the target make the
continuous equivalence a homeomorphism. The construction includes `d=0`.

Source: Fritsch–Piccinini, Theorem 2.2.2 p.58; the exact maximum-norm and
last-coordinate implementation is agent-written for `topo.cw_interval_product_g8`.
-/
theorem native_disk_interval_homeomorph (d : ℕ) :
    ∃ e : ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) ≃ₜ
        ↥(Metric.closedBall (0 : Fin d → ℝ) 1) × unitInterval,
      (∀ w j, (e w).1.1 j = w.1 (Fin.castSucc j)) ∧
      (∀ w, ((e w).2 : ℝ) = (w.1 (Fin.last d) + 1) / 2) ∧
      (∀ z t, (e.symm (z, t)).1 = Fin.snoc z.1 (2 * (t : ℝ) - 1)) := by
  have hcoord {m : ℕ} (w : ↥(Metric.closedBall (0 : Fin m → ℝ) 1)) (i : Fin m) :
      ‖w.1 i‖ ≤ 1 :=
    (norm_le_pi_norm w.1 i).trans (by simpa only [Metric.mem_closedBall, dist_zero_right]
      using w.2)
  let f : ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) →
      ↥(Metric.closedBall (0 : Fin d → ℝ) 1) × unitInterval := fun w ↦
    (⟨fun j ↦ w.1 j.castSucc, by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
          (fun j ↦ hcoord w (Fin.castSucc j))⟩,
     ⟨(w.1 (Fin.last d) + 1) / 2, by
      have h := abs_le.mp (hcoord w (Fin.last d))
      constructor <;> linarith⟩)
  let g : ↥(Metric.closedBall (0 : Fin d → ℝ) 1) × unitInterval →
      ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) := fun zt ↦
    ⟨Fin.snoc zt.1.1 (2 * (zt.2 : ℝ) - 1), by
      rw [Metric.mem_closedBall, dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [Fin.snoc_last, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [zt.2.2.1, zt.2.2.2]
      · simpa only [Fin.snoc_castSucc] using hcoord zt.1 j⟩
  let e : ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) ≃
      ↥(Metric.closedBall (0 : Fin d → ℝ) 1) × unitInterval :=
    { toFun := f
      invFun := g
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp [f, g, Fin.snoc_last]
          ring
        · simp [f, g, Fin.snoc_castSucc]
      right_inv := by
        intro zt
        apply Prod.ext
        · apply Subtype.ext
          funext j
          simp [f, g, Fin.snoc_castSucc]
        · apply Subtype.ext
          simp [f, g, Fin.snoc_last] }
  have hf : Continuous f := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_pi fun j ↦ (continuous_apply j.castSucc).comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact (((continuous_apply (Fin.last d)).comp continuous_subtype_val).add
        continuous_const).div_const 2
  let : CompactSpace ↥(Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hf,
    fun _ _ ↦ rfl, fun _ ↦ rfl, fun _ _ ↦ rfl⟩

end HolomorphicAnosov.Topology

