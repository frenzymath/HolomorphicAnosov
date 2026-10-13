import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set _root_.Topology
namespace HolomorphicAnosov.Topology

/-- Native characteristic data for the prism over an arbitrary CW cell.

Source: Fritsch–Piccinini, *Cellular Structures in Topology*, Theorem 2.2.2(ii),
p.58 and its product-ball attaching-map proof. The maximum-norm coordinates
and total clamped extension implement that product characteristic map.

Proof: retain the first d coordinates for the original characteristic map,
and clamp the affine last coordinate (s+1)/2 to the unit interval. On the
closed native disk no clamping occurs. On the open disk, the head lies in the
original open disk and the time is strictly between zero and one. The inverse
uses the original characteristic inverse and appends 2t-1. The finite-product
norm bounds and original inverse identities prove the partial equivalence
laws. Forward continuity holds on the closed disk by composition and products;
inverse continuity holds on the target by the original inverse continuity and
coordinatewise continuity of snoc. No regularity or dimension restriction is
used; d=0 has an empty head block. -/
theorem prism_partial_equiv_data
    {X : Type*} [TopologicalSpace X] [CWComplex (univ : Set X)]
    (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d) :
    ∃ e : PartialEquiv (Fin (d + 1) → ℝ) (X × unitInterval),
      e.source = Metric.ball 0 1 ∧
      e.target = (CWComplex.openCell (C := (univ : Set X)) d i).prod
        (Ioo (0 : unitInterval) 1) ∧
      (∀ w ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) 1,
        (e w).1 = RelCWComplex.map (C := (univ : Set X)) d i
          (fun j ↦ w j.castSucc) ∧
        ((e w).2 : ℝ) = (w (Fin.last d) + 1) / 2) ∧
      ContinuousOn e (Metric.closedBall 0 1) ∧ ContinuousOn e.symm e.target := by
  let m := RelCWComplex.map (C := (univ : Set X)) d i
  let head : (Fin (d + 1) → ℝ) → (Fin d → ℝ) := fun w j ↦ w j.castSucc
  let time : (Fin (d + 1) → ℝ) → unitInterval :=
    fun w ↦ projIcc 0 1 zero_le_one ((w (Fin.last d) + 1) / 2)
  have hcoord (w : Fin (d + 1) → ℝ) (hw : w ∈ Metric.ball 0 1) (j) :
      ‖w j‖ < 1 := (norm_le_pi_norm w j).trans_lt (by simpa using hw)
  have hhead (w) (hw : w ∈ Metric.ball (0 : Fin (d + 1) → ℝ) 1) :
      head w ∈ m.source := by
    rw [RelCWComplex.source_eq]
    simpa [Metric.mem_ball, dist_zero_right] using
      (pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num)).mpr
        (fun j : Fin d ↦ hcoord w hw j.castSucc)
  have htime (w) (hw : w ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) 1) :
      (time w : ℝ) = (w (Fin.last d) + 1) / 2 := by
    have hc : ‖w (Fin.last d)‖ ≤ 1 :=
      (norm_le_pi_norm w _).trans (by simpa using hw)
    have hb := abs_le.mp hc
    have hh : (w (Fin.last d) + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    simp only [time, projIcc_of_mem zero_le_one hh]
  have htimeOpen (w) (hw : w ∈ Metric.ball (0 : Fin (d + 1) → ℝ) 1) :
      time w ∈ Ioo (0 : unitInterval) 1 := by
    have hc := abs_lt.mp (hcoord w hw (Fin.last d))
    change 0 < (time w : ℝ) ∧ (time w : ℝ) < 1
    rw [htime w (Metric.ball_subset_closedBall hw)]
    constructor <;> linarith
  let inv : X × unitInterval → (Fin (d + 1) → ℝ) :=
    fun y ↦ Fin.snoc (m.symm y.1) (2 * (y.2 : ℝ) - 1)
  have hinv (y : X × unitInterval)
      (hy : y ∈ m.target.prod (Ioo (0 : unitInterval) 1)) :
      inv y ∈ Metric.ball 0 1 := by
    have hm := m.map_target hy.1
    rw [RelCWComplex.source_eq] at hm
    have hc : ∀ j, ‖m.symm y.1 j‖ < 1 :=
      (pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num)).mp (by simpa using hm)
    rw [Metric.mem_ball, dist_zero_right]
    apply (pi_norm_lt_iff (show (0 : ℝ) < 1 by norm_num)).mpr
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp only [inv, Fin.snoc_last, Real.norm_eq_abs, abs_lt]
      have ht : 0 < (y.2 : ℝ) ∧ (y.2 : ℝ) < 1 := hy.2
      constructor <;> linarith
    · simpa only [inv, Fin.snoc_castSucc] using hc k
  let e : PartialEquiv (Fin (d + 1) → ℝ) (X × unitInterval) := {
    toFun := fun w ↦ (m (head w), time w)
    invFun := inv
    source := Metric.ball 0 1
    target := m.target.prod (Ioo (0 : unitInterval) 1)
    map_source' := fun w hw ↦ ⟨m.map_source (hhead w hw), htimeOpen w hw⟩
    map_target' := hinv
    left_inv' := by
      intro w hw
      funext j
      refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · simp only [inv, Fin.snoc_last, htime w (Metric.ball_subset_closedBall hw)]
        ring
      · simp only [inv, Fin.snoc_castSucc, m.left_inv (hhead w hw)]
        rfl
    right_inv' := by
      intro y hy
      apply Prod.ext
      · change m (head (inv y)) = y.1
        have hh : head (inv y) = m.symm y.1 := by ext k; simp [head, inv]
        rw [hh, m.right_inv hy.1]
      · apply Subtype.ext
        rw [htime (inv y) (Metric.ball_subset_closedBall (hinv y hy))]
        simp only [inv, Fin.snoc_last]
        ring }
  refine ⟨e, rfl, ?_, ?_, ?_, ?_⟩
  · change m.target.prod _ = (m '' Metric.ball 0 1).prod _
    rw [← m.image_source_eq_target, RelCWComplex.source_eq]
  · intro w hw
    exact ⟨rfl, htime w hw⟩
  · change ContinuousOn (fun w ↦ (m (head w), time w)) (Metric.closedBall 0 1)
    apply ContinuousOn.prodMk
    · apply (RelCWComplex.continuousOn d i).comp
        (continuous_pi (fun j ↦ continuous_apply j.castSucc)).continuousOn
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
      intro j
      exact (norm_le_pi_norm w j.castSucc).trans (by simpa using hw)
    · exact (continuous_projIcc.comp
        (((continuous_apply (Fin.last d)).add continuous_const).div_const 2)).continuousOn
  · change ContinuousOn inv (m.target.prod (Ioo (0 : unitInterval) 1))
    have hc : ContinuousOn (fun y : X × unitInterval ↦ m.symm y.1)
        (m.target.prod (Ioo (0 : unitInterval) 1)) :=
      (RelCWComplex.continuousOn_symm d i).comp continuousOn_fst (fun _ hy ↦ hy.1)
    apply continuousOn_pi.mpr
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp only [inv, Fin.snoc_last]
      exact ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub
        continuous_const).continuousOn
    · simpa only [inv, Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply k).continuousOn.comp hc (fun _ _ ↦ mem_univ _)

end HolomorphicAnosov.Topology

