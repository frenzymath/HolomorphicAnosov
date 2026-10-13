import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularWeight
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularIndex
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnuliLocallyFinite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- HPS p.28 annular interpolation of maps continuous on the relevant closed balls.
Use the affine weight on each half-open annulus. At a shared endpoint both formulas
equal the same representative. Thus the formula agrees on every closed annulus with
a continuous function there. Closed annuli are locally finite off zero; pasting proves
continuity on their union and hence at each nonzero point of the initial open ball. -/
theorem annular_interpolation
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (q : ℕ → X → Y)
    {r : ℕ → ℝ} (hrpos : ∀ n, 0 < r n) (hr : StrictAnti r)
    (hrt : Tendsto r atTop (𝓝 0))
    (hq : ∀ n, ContinuousOn (q n) (Metric.closedBall 0 (r n)) ∧
      ContinuousOn (q (n+1)) (Metric.closedBall 0 (r n))) :
    ∃ g : X → Y, g 0 = 0 ∧
      (∀ n x, r (n+1) ≤ ‖x‖ → ‖x‖ ≤ r n →
        g x = annularWeight r n ‖x‖ • q (n+1) x + (1-annularWeight r n ‖x‖) • q n x) ∧
      ∀ x, x ≠ 0 → ‖x‖ < r 0 → ContinuousAt g x := by
  classical
  have hi (x : X) (hx : 0 < ‖x‖ ∧ ‖x‖ ≤ r 0) :
      ∃ n, r (n+1) < ‖x‖ ∧ ‖x‖ ≤ r n := annular_index hrt hx.1 hx.2
  let k (x : X) : ℕ := if hx : 0 < ‖x‖ ∧ ‖x‖ ≤ r 0 then (hi x hx).choose else 0
  have hk (x : X) (hx : 0 < ‖x‖ ∧ ‖x‖ ≤ r 0) :
      r (k x+1) < ‖x‖ ∧ ‖x‖ ≤ r (k x) := by
    dsimp [k]; rw [dite_eq_left hx]; exact (hi x hx).choose_spec
  let F (n : ℕ) (x : X) : Y :=
    annularWeight r n ‖x‖ • q (n+1) x + (1-annularWeight r n ‖x‖) • q n x
  have hend (n : ℕ) (x : X) (hx : ‖x‖ = r (n+1)) : F n x = F (n+1) x := by
    have hd : r n - r (n+1) ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hr (Nat.lt_succ_self n)))
    simp [F, annularWeight, hx, hd]
  let g (x : X) : Y := if x = 0 then 0 else F (k x) x
  have heq (n : ℕ) (x : X) (hl : r (n+1) ≤ ‖x‖) (hu : ‖x‖ ≤ r n) :
      g x = F n x := by
    have hxpos : 0 < ‖x‖ := (hrpos _).trans_le hl
    have hxne : x ≠ 0 := norm_pos_iff.mp hxpos
    have hxx := hk x ⟨hxpos, hu.trans (hr.antitone (Nat.zero_le n))⟩
    have hnk : n ≤ k x := by
      by_contra hh
      have hh := hr.antitone (show k x+1 ≤ n by omega)
      linarith [hxx.1]
    have hkn : k x ≤ n+1 := by
      by_contra hh
      have hh := hr (show n+1 < k x by omega)
      linarith [hxx.2]
    have hcases : k x = n ∨ k x = n+1 := by omega
    dsimp [g]; rw [ite_eq_right hxne]
    rcases hcases with h | h
    · rw [h]
    · rw [h]
      have hx : ‖x‖ = r (n+1) := le_antisymm (by simpa [h] using hxx.2) hl
      exact (hend n x hx).symm
  refine ⟨g, by simp [g], heq, ?_⟩
  let A (n : ℕ) : Set {x : X // x ≠ 0} :=
    {x | r (n+1) ≤ ‖(x : X)‖ ∧ ‖(x : X)‖ ≤ r n}
  have hclosed (n : ℕ) : IsClosed (A n) :=
    (isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)).inter
      (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const)
  have hF (n : ℕ) : ContinuousOn (F n) (Metric.closedBall 0 (r n)) := by
    have hw : Continuous (fun x : X ↦ annularWeight r n ‖x‖) := by
      dsimp [annularWeight]; fun_prop
    exact (hw.continuousOn.smul (hq n).2).add
      ((continuous_const.sub hw).continuousOn.smul (hq n).1)
  have hlocal : ContinuousOn (fun x : {x : X // x ≠ 0} ↦ g x) (⋃ n, A n) := by
    apply (annuli_locallyFinite hrt).continuousOn_iUnion hclosed
    intro n
    have hf : ContinuousOn (fun x : {x : X // x ≠ 0} ↦ F n x) (A n) :=
      (hF n).comp continuous_subtype_val.continuousOn (fun x hx ↦ by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2)
    apply hf.congr
    intro x hx
    exact heq n x hx.1 hx.2
  intro x hx hxr
  let z : {x : X // x ≠ 0} := ⟨x, hx⟩
  have hn : (⋃ n, A n) ∈ 𝓝 z := by
    have hh : {y : {x : X // x ≠ 0} | ‖(y : X)‖ < r 0} ∈ 𝓝 z :=
      (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const).mem_nhds hxr
    apply Filter.mem_of_superset hh
    intro y hy
    obtain ⟨n, hn1, hn2⟩ := hi y ⟨norm_pos_iff.mpr y.property, hy.le⟩
    exact Set.mem_iUnion.mpr ⟨n, hn1.le, hn2⟩
  have hz : ContinuousAt (fun y : {x : X // x ≠ 0} ↦ g y) z := hlocal.continuousAt hn
  have hw : ContinuousWithinAt g {x : X | x ≠ 0} x :=
    (continuousWithinAt_iff_continuousAt_domRestrict g hx).mpr hz
  exact hw.continuousAt (isOpen_ne.mem_nhds hx)

end HolomorphicAnosov.BoundedLipschitzJets

