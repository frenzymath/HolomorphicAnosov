import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Module

namespace HolomorphicAnosov.FranksSeries
noncomputable section
open _root_.Topology
variable {X V : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V]


omit [NormedSpace ℝ V] in
/-- The source's geometric majorant supplies an everywhere continuous bounded sum,
without assuming an additional Banach space of invariant functions. -/
theorem geometric_series_sum (f : ℕ → X → V) (C r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hc : ∀ j, Continuous (f j))
    (hb : ∀ j x, ‖f j x‖ ≤ C * r ^ j) :
    Continuous (fun x ↦ ∑' j, f j x) ∧
      (∀ x, Summable (fun j ↦ f j x)) ∧
      (∀ x, ‖∑' j, f j x‖ ≤ C * (1 - r)⁻¹) := by
  have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left C
  refine ⟨continuous_tsum hc hgeom.summable hb,
    fun x ↦ hgeom.summable.of_norm_bounded (fun j ↦ hb j x),
    fun x ↦ tsum_of_norm_bounded hgeom (fun j ↦ hb j x)⟩

omit [TopologicalSpace X] [CompleteSpace V] in
/-- Positive iterates on the unstable factor give the negative resolvent sum.
This fixes the source's printed stable/unstable label reversal without changing L. -/
theorem negative_series_resolvent (L : V →L[ℝ] V) (G : X → X)
    (f : ℕ → X → V) (hs : ∀ x, Summable (fun j ↦ f j x))
    (hstep : ∀ j x, L (f j (G x)) = f (j + 1) x) (x : X) :
    L (-∑' j, f j (G x)) - (-∑' j, f j x) = f 0 x := by
  rw [map_neg, L.map_tsum (hs (G x))]
  simp_rw [hstep]
  rw [(hs x).tsum_eq_zero_add]
  abel

omit [TopologicalSpace X] in
/-- Negative iterates on the stable factor start at index one; their resolvent has
positive sign. The index-zero term enters only after applying L. -/
theorem positive_series_resolvent (L : V →L[ℝ] V) (G : X → X)
    (f : ℕ → X → V) (hs : ∀ x, Summable (fun j ↦ f j x))
    (hstep : ∀ j x, L (f (j + 1) (G x)) = f j x) (x : X) :
    L (∑' j, f (j + 1) (G x)) - (∑' j, f (j + 1) x) = f 0 x := by
  have ht : Summable (fun j ↦ f (j + 1) (G x)) := by
    simpa only [Function.comp_def, Nat.succ_eq_add_one] using
      (hs (G x)).comp_injective Nat.succ_injective
  rw [L.map_tsum ht]
  simp_rw [hstep]
  rw [(hs x).tsum_eq_zero_add]
  abel


/-- Franks's correction is a genuine continuous bounded cochain with the two
source resolvent signs. All topological descent and pointed-cover comparisons
remain outside this elementary analytic calculation. -/
theorem correction_from_geometric_terms (L : V →L[ℝ] V) (G : X → X)
    (fs fu : ℕ → X → V) (Cs Cu rs ru : ℝ)
    (hCs : 0 ≤ Cs) (_hCu : 0 ≤ Cu)
    (hrs0 : 0 ≤ rs) (hrs1 : rs < 1) (hru0 : 0 ≤ ru) (hru1 : ru < 1)
    (hcs : ∀ j, Continuous (fs j)) (hcu : ∀ j, Continuous (fu j))
    (hbs : ∀ j x, ‖fs j x‖ ≤ Cs * rs ^ j)
    (hbu : ∀ j x, ‖fu j x‖ ≤ Cu * ru ^ j)
    (hsteps : ∀ j x, L (fs (j + 1) (G x)) = fs j x)
    (hstepu : ∀ j x, L (fu j (G x)) = fu (j + 1) x)
    (b : X) (hzs : ∀ j, fs j b = 0) (hzu : ∀ j, fu j b = 0) :
    ∃ v : C(X, V), v b = 0 ∧
      (∀ x, L (v (G x)) - v x = fs 0 x + fu 0 x) ∧
      (∀ x, ‖v x‖ ≤ Cs * (1 - rs)⁻¹ + Cu * (1 - ru)⁻¹) ∧
      (∀ x, v x = (∑' j, fs (j + 1) x) - ∑' j, fu j x) := by
  have hs := geometric_series_sum fs Cs rs hrs0 hrs1 hcs hbs
  have hu := geometric_series_sum fu Cu ru hru0 hru1 hcu hbu
  have hbss : ∀ j x, ‖fs (j + 1) x‖ ≤ Cs * rs ^ j := by
    intro j x
    apply (hbs (j + 1) x).trans
    rw [pow_succ]
    calc
      Cs * (rs ^ j * rs) = (Cs * rs ^ j) * rs := by ring
      _ ≤ (Cs * rs ^ j) * 1 :=
        mul_le_mul_of_nonneg_left hrs1.le (mul_nonneg hCs (pow_nonneg hrs0 j))
      _ = Cs * rs ^ j := mul_one _
  have hss := geometric_series_sum (fun j x ↦ fs (j + 1) x) Cs rs hrs0 hrs1
    (fun j ↦ hcs (j + 1)) hbss
  let v : C(X, V) := ⟨fun x ↦ (∑' j, fs (j + 1) x) - ∑' j, fu j x,
    hss.1.sub hu.1⟩
  refine ⟨v, ?_, ?_, ?_, fun _ ↦ rfl⟩
  · change (∑' j, fs (j + 1) b) - ∑' j, fu j b = 0
    simp [hzs, hzu]
  · intro x
    change L ((∑' j, fs (j + 1) (G x)) - ∑' j, fu j (G x)) -
      ((∑' j, fs (j + 1) x) - ∑' j, fu j x) = _
    rw [map_sub]
    have hS := positive_series_resolvent L G fs hs.2.1 hsteps x
    have hU := negative_series_resolvent L G fu hu.2.1 hstepu x
    rw [map_neg] at hU
    calc
      _ = (L (∑' j, fs (j + 1) (G x)) - ∑' j, fs (j + 1) x) +
        (-L (∑' j, fu j (G x)) + ∑' j, fu j x) := by abel
      _ = _ := by rw [hS]; exact congrArg (fun t ↦ fs 0 x + t) (by simpa using hU)
  · intro x
    exact (norm_sub_le _ _).trans (add_le_add (hss.2.2 x) (hu.2.2 x))


end
end HolomorphicAnosov.FranksSeries
