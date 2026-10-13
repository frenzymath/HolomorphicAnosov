import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Existence, uniqueness, and continuous parameter dependence of intersections of plaque
graphs satisfying Lipschitz and radius bounds.
(Fisher–Hasselblatt, Prop. 12.1.3, pp. 578–579; Lemma 12.5.18, p. 602)
-/

open Set

namespace HolomorphicAnosov.Ghys

/-- Continuously varying plaque graphs with Lipschitz constant `1 / 4` and the stated radius
bounds have a unique intersection in the closed radius-`r` ball, varying continuously
with the parameter. (Fisher–Hasselblatt, Prop. 12.1.3, pp. 578–579; Lemma 12.5.18, p. 602) -/
theorem surface_graph_intersection_continuous
    {P E F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [CompleteSpace E]
    (r : ℝ) (hr : 0 < r) (U : P → E → F) (S : P → F → E)
    (hUc : Continuous (fun z : P × ↥(Metric.closedBall (0 : E) r) ↦ U z.1 z.2))
    (hSc : Continuous (fun z : P × ↥(Metric.closedBall (0 : F) (r / 2)) ↦
      S z.1 z.2))
    (hU0 : ∀ p, ‖U p 0‖ ≤ r / 4) (hS0 : ∀ p, ‖S p 0‖ ≤ r / 4)
    (hU : ∀ p, ∀ x ∈ Metric.closedBall (0 : E) r,
      ∀ y ∈ Metric.closedBall (0 : E) r,
        dist (U p x) (U p y) ≤ (1 / 4 : ℝ) * dist x y)
    (hS : ∀ p, ∀ x ∈ Metric.closedBall (0 : F) (r / 2),
      ∀ y ∈ Metric.closedBall (0 : F) (r / 2),
        dist (S p x) (S p y) ≤ (1 / 4 : ℝ) * dist x y) :
    ∃ x : P → E, Continuous x ∧
      ∀ p, x p ∈ Metric.closedBall (0 : E) r ∧ x p = S p (U p (x p)) ∧
        ∀ y ∈ Metric.closedBall (0 : E) r, y = S p (U p y) → y = x p := by
  let D := Metric.closedBall (0 : E) r
  have hzero : (0 : E) ∈ D := by simp [D, hr.le]
  have hFzero : (0 : F) ∈ Metric.closedBall (0 : F) (r / 2) := by
    simp [le_of_lt (by positivity : 0 < r / 2)]
  have himage (p : P) (x : E) (hx : x ∈ D) :
      U p x ∈ Metric.closedBall (0 : F) (r / 2) := by
    have hxnorm : dist x 0 ≤ r := by simpa [D] using hx
    apply Metric.mem_closedBall.mpr
    calc
      dist (U p x) 0 ≤ dist (U p x) (U p 0) + dist (U p 0) 0 := dist_triangle _ _ _
      _ ≤ (1 / 4 : ℝ) * dist x 0 + r / 4 :=
        add_le_add (hU p x hx 0 hzero) (by simpa using hU0 p)
      _ ≤ r / 2 := by nlinarith
  have hmap (p : P) (x : E) (hx : x ∈ D) : S p (U p x) ∈ D := by
    have hUx := himage p x hx
    have hUxnorm : dist (U p x) 0 ≤ r / 2 := Metric.mem_closedBall.mp hUx
    apply Metric.mem_closedBall.mpr
    calc
      dist (S p (U p x)) 0 ≤ dist (S p (U p x)) (S p 0) + dist (S p 0) 0 :=
        dist_triangle _ _ _
      _ ≤ (1 / 4 : ℝ) * dist (U p x) 0 + r / 4 :=
        add_le_add (hS p (U p x) hUx 0 hFzero) (by simpa using hS0 p)
      _ ≤ r := by nlinarith
  let T : P → D → D := fun p x ↦ ⟨S p (U p x), hmap p x x.property⟩
  let : CompleteSpace D := Metric.isClosed_closedBall.isComplete.completeSpace_coe
  let : Nonempty D := ⟨⟨0, hzero⟩⟩
  have hT (p : P) : ContractingWith (⟨1 / 16, by norm_num⟩ : NNReal) (T p) := by
    refine ⟨by change (1 / 16 : NNReal) < 1; norm_num,
      LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (S p (U p x.val)) (S p (U p y.val)) ≤
      (1 / 16 : ℝ) * dist x.val y.val
    calc
      _ ≤ (1 / 4 : ℝ) * dist (U p x.val) (U p y.val) :=
        hS p _ (himage p x x.property) _ (himage p y y.property)
      _ ≤ (1 / 4 : ℝ) * ((1 / 4 : ℝ) * dist x.val y.val) :=
        mul_le_mul_of_nonneg_left (hU p x x.property y y.property) (by norm_num)
      _ = _ := by ring
  let x : P → D := fun p ↦ (hT p).fixedPoint (T p)
  have hx : Continuous x := by
    apply continuous_iff_continuousAt.mpr
    intro p
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hu : Continuous (fun q ↦ U q (x p).val) :=
      hUc.comp (continuous_id.prodMk (continuous_const (y := x p)))
    have hu' : Continuous (fun q ↦ (⟨U q (x p).val, himage q (x p) (x p).property⟩ :
        Metric.closedBall (0 : F) (r / 2))) := hu.subtype_mk _
    have htc : Continuous (fun q ↦ T q (x p)) :=
      (hSc.comp (continuous_id.prodMk hu')).subtype_mk _
    have hsmall := (Metric.tendsto_nhds.mp (htc.continuousAt (x := p))) (ε * (15 / 16))
      (by positivity)
    filter_upwards [hsmall] with q hq
    have he : T p (x p) = x p := (hT p).fixedPoint_isFixedPt
    rw [he] at hq
    have hbound := (hT q).dist_fixedPoint_le (x p)
    change dist (x p) (x q) ≤ dist (x p) (T q (x p)) / (1 - (1 / 16 : ℝ)) at hbound
    rw [dist_comm (x p) (x q), dist_comm (x p) (T q (x p))] at hbound
    apply lt_of_le_of_lt hbound
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 16)).mpr
    simpa only [show (1 - 1 / 16 : ℝ) = 15 / 16 by norm_num] using hq
  refine ⟨fun p ↦ (x p).val, continuous_subtype_val.comp hx, fun p ↦ ?_⟩
  refine ⟨(x p).property, (congrArg Subtype.val (hT p).fixedPoint_isFixedPt).symm, ?_⟩
  intro y hy he
  exact congrArg Subtype.val ((hT p).fixedPoint_unique'
    (show Function.IsFixedPt (T p) (⟨y, hy⟩ : D) from Subtype.ext he.symm)
    (hT p).fixedPoint_isFixedPt)


end HolomorphicAnosov.Ghys
