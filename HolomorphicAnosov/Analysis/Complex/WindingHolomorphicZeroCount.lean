import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingNumber
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingLift
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingIncrement
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingHomotopy
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingOmittedPath
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingConstant
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingUnitZero
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingUnit
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingMul
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingPow
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingDiskNozero
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.DiskOrdersFinite
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.DiskFactorization
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingCongrSub
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingProd
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingAffineCircle
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions

/-!
# Continuous-loop winding and the holomorphic disk argument principle

DAG node: `analysis.lyubich_winding_holomorphic_zero_count`.
Source: Lyubich, *Conformal Geometry and Dynamics of Quadratic Polynomials*,
§3.3 pp.107–108, equation (3.1), Propositions 3.8–3.9; McMullen,
*Advanced Complex Analysis*, printed pp.8 and 13.

The reusable integer `loopWinding` is defined in `WindingNumber`. The theorem below
retains the exact continuous-loop, omitted-value, normalization, finite-positive-order,
and nonzero-winding clauses. The exact theorem is proved below using exponential
covering and finite analytic divisor extraction with an explicit continuity upgrade.
-/

namespace HolomorphicAnosov
noncomputable section
open scoped Topology _root_.Topology

/-- Full continuous-loop winding and holomorphic disk zero-count statement.

The integer-valued definition `loopWinding` expresses the first clause of the
source statement by its actual codomain ℤ. The finite set `s` is exactly the
interior zero set, not an arbitrarily selected subset. Each order is finite and
strictly positive; the same integer winding equals their sum. The last conjunct
explicitly records that nonzero winding gives an interior preimage.

Source statements: Lyubich §3.3 pp.107–108 and McMullen printed pp.8,13.
The following agent proof supplies the omitted combination; the compact-divisor and
codiscrete-to-pointwise argument is not attributed to those books.

Complete natural-language proof:

1. For each loop, the existing exponential covering lift has endpoint increment equal to the winding
integer times 2πi. If L is any other continuous logarithm lift of the same punctured path,
exp(L−K)=1. Covering constancy on the connected parameter interval makes L−K constant, so its
endpoint increment is the same. The nonzero scalar 2πi and injectivity of the integer cast identify
the winding integer uniquely.

2. For a free continuous homotopy avoiding b, first lift its moving initial-point path and then lift
the whole homotopy with the loop parameter first. The lifted endpoint difference is continuous in
the homotopy parameter and has exponential equal to1 because every loop is closed. Covering
constancy makes this difference constant. The preceding arbitrary-lift characterization therefore
gives equality of the two winding integers, without fixing the loop basepoint.

3. An omitted-value path produces the jointly continuous homotopy γ(z)−p(t)+b1; translating the
initial loop by b1−b0 leaves its punctured path unchanged. Hence winding is constant along that
path. The positive unit circle at0 has lift t↦2πit and winding1. For ||b||<1 the straight
omitted-value path t↦tb remains disjoint from the circle since ||tb||<1, proving winding1 about b. A
constant loop c has the constant logarithm lift log(c−b), with zero endpoint increment.

4. For two loops avoiding0, the sum of continuous logarithm lifts is a logarithm lift of their
pointwise product by exp(L1+L2)=exp(L1)exp(L2). Its endpoint increment is the sum of the two
increments. This proves product additivity, and induction proves finite-product and
nonnegative-power laws. If a continuous function g is nonzero on the closed disk, its boundary loop
contracts through g(a+(1−t)rz) to the constant g(a), proving winding0.

5. Let h=f−b and K be the original closed disk. The function h is analytic near every point of K. At
the actual boundary point a+r it is nonzero, so its analytic order there is0. The analytic identity
principle on the preconnected closed disk propagates exclusion of an identically-zero germ to every
point of K. Thus every analytic order on K is finite. Analytic and meromorphic orders agree through
the natural-to-integer cast, so the actual divisor D of h on K evaluates to analyticOrderNatAt(h,x).
The order is zero exactly at nonzeros; at zeros its finite natural value is positive.

6. The actual bundled divisor D has support contained in K and locally finite there. Its support is
finite by compactness of K. Boundary nonvanishing identifies this support exactly with the interior
zeros of f−b, so its finite-set conversion s has the required membership equivalence. For each x in
s, the analytic order is finite and positive. Constant f unequal to b yields empty support; no
constant exclusion or larger connected holomorphy neighborhood is assumed.

7. The exact meromorphic extraction theorem on K gives an analytic g nonzero everywhere on K and
codiscrete agreement h=(finprod_x(z−x)^D(x))g. Finiteness of D.support and its nonnegative natural
orders turn that product into P(z)=prod_(x∈s)(z−x)^analyticOrderNatAt(h,x), an analytic function.
This agreement is not presumed pointwise. At each interior x, codiscrete agreement supplies equality
in a punctured neighborhood restricted to K; the interior ball is a neighborhood of x, so it
supplies actual punctured ambient-neighborhood equality. Both sides are continuous at x and the
punctured complex neighborhood filter is nontrivial. Uniqueness of their limits gives h(x)=P(x)g(x).
Both sides are continuous on K, and K is the closure of its open ball because r>0; equality on that
ball extends to every point of K, including boundary points and zeros.

8. For each zero x in s, the affine circle loop a+rz−x has winding1: move the omitted value along
the segment from a to x inside the open disk, and use the explicit lift log(r)+2πit at a. The g
boundary factor has winding0 by its zero-free contraction. The pointwise factorization on K and the
finite-product/power laws therefore give winding of f boundary about b equal to the sum of the
positive analytic orders. If that winding is nonzero, s cannot be empty, and its membership
equivalence gives an actual interior preimage.
-/
theorem winding_holomorphic_zero_count :
    (∀ (γ₀ γ₁ : ComplexLoop) (b : ℂ) (hb₀ : ∀ z, γ₀ z ≠ b)
        (hb₁ : ∀ z, γ₁ z ≠ b),
      LoopHomotopyAvoids γ₀ γ₁ b → loopWinding γ₀ b hb₀ = loopWinding γ₁ b hb₁) ∧
    (∀ (γ : ComplexLoop) (b₀ b₁ : ℂ) (hb₀ : ∀ z, γ z ≠ b₀)
        (hb₁ : ∀ z, γ z ≠ b₁),
      OmittedValuePath γ b₀ b₁ → loopWinding γ b₀ hb₀ = loopWinding γ b₁ hb₁) ∧
    (∀ (b : ℂ) (hb : ∀ z, unitCircleLoop z ≠ b),
      ‖b‖ < 1 → loopWinding unitCircleLoop b hb = 1) ∧
    (∀ (c b : ℂ) (hb : c ≠ b),
      loopWinding (constantLoop c) b (fun _ => hb) = 0) ∧
    (∀ (a b : ℂ) (r : ℝ) (f : ℂ → ℂ) (hr : 0 < r)
      (hf : AnalyticOnNhd ℂ f (Metric.closedBall a r))
      (hboundary : ∀ z ∈ Metric.sphere a r, f z ≠ b),
      let γ := diskBoundaryLoop a r f hr hf.continuousOn
      let hb : ∀ z : Circle, γ z ≠ b := fun z => hboundary _ (by
        rw [Metric.mem_sphere]
        simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr, Circle.norm_coe (show Circle from z)])
      ∃ s : Finset ℂ,
        (∀ x, x ∈ s ↔ x ∈ Metric.ball a r ∧ f x = b) ∧
        (∀ x ∈ s, analyticOrderAt (fun z => f z - b) x ≠ ⊤ ∧
          0 < analyticOrderNatAt (fun z => f z - b) x) ∧
        loopWinding γ b hb = s.sum (fun x =>
          (analyticOrderNatAt (fun z => f z - b) x : ℤ)) ∧
        (loopWinding γ b hb ≠ 0 → ∃ x ∈ Metric.ball a r, f x = b)) := by
  refine ⟨loopWinding_homotopy, loopWinding_omittedPath, loopWinding_unit,
    loopWinding_constant, ?_⟩
  intro a b r f hr hf hboundary
  dsimp only
  classical
  obtain ⟨s, hs, hord, g, hg, hgne, heq⟩ := disk_factorization a b r f hr hf hboundary
  let γ := diskBoundaryLoop a r f hr hf.continuousOn
  have hb : ∀ z : Circle, γ z ≠ b := fun z ↦ hboundary _ (by
    rw [Metric.mem_sphere]
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr])
  let σ (x : {x // x ∈ s}) : ComplexLoop :=
    ⟨fun z ↦ a + r * (z : ℂ) - x.val, by fun_prop⟩
  have hσ : ∀ x z, σ x z ≠ 0 := by
    intro x z hz
    have hx := Metric.mem_ball.mp ((hs x).mp x.property).1
    have he : a + r * (z : ℂ) = x := sub_eq_zero.mp hz
    have hd : dist (a + r * (z : ℂ)) a = r := by
      simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr]
    rw [he] at hd
    exact (ne_of_lt hx) hd
  let ψ (x : {x // x ∈ s}) := σ x ^ analyticOrderNatAt (fun z ↦ f z - b) x
  have hψ : ∀ x z, ψ x z ≠ 0 := fun x z ↦ pow_ne_zero _ (hσ x z)
  let Γprod := ∏ x ∈ s.attach, ψ x
  have hΓprod : ∀ z, Γprod z ≠ 0 := by
    intro z
    simpa only [Γprod, ContinuousMap.prod_apply] using
      Finset.prod_ne_zero_iff.mpr (fun x (_ : x ∈ s.attach) ↦ hψ x z)
  let U := diskBoundaryLoop a r g hr hg.continuousOn
  have hU : ∀ z, U z ≠ 0 := fun z ↦ hgne _ (by
    rw [Metric.mem_closedBall]
    simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr])
  have hUwind : loopWinding U 0 hU = 0 := loopWinding_disk_nozero a r g hr hg.continuousOn hgne
  have hΓprodwind : loopWinding Γprod 0 hΓprod =
      ∑ x ∈ s, (analyticOrderNatAt (fun z ↦ f z - b) x : ℤ) := by
    rw [loopWinding_prod s.attach ψ hψ]
    have hi (x : {x // x ∈ s}) : loopWinding (ψ x) 0 (hψ x) =
        (analyticOrderNatAt (fun z ↦ f z - b) x : ℤ) := by
      rw [loopWinding_pow (σ x) (hσ x)]
      have hn := loopWinding_affine_circle a x r hr ((hs x).mp x.property).1 (hσ x)
      change loopWinding (σ x) 0 (hσ x) = 1 at hn
      rw [hn, mul_one]
    simp_rw [hi]
    simpa using (Finset.sum_attach s
      (fun x : ℂ ↦ (analyticOrderNatAt (fun z ↦ f z - b) x : ℤ)))
  have hw : loopWinding γ b hb =
      ∑ x ∈ s, (analyticOrderNatAt (fun z ↦ f z - b) x : ℤ) := by
    have hc := loopWinding_congr_sub γ (Γprod * U) b 0 hb
      (fun z ↦ mul_ne_zero (hΓprod z) (hU z)) (by
        intro z
        have hz : a + r * (z : ℂ) ∈ Metric.closedBall a r := by
          rw [Metric.mem_closedBall]
          simp [dist_eq_norm, Complex.norm_real, abs_of_pos hr]
        change f (a + r * (z : ℂ)) - b = Γprod z * U z - 0
        rw [sub_zero, heq _ hz]
        congr 1
        dsimp [Γprod, ψ, σ]
        simp only [ContinuousMap.prod_apply, ContinuousMap.pow_apply, ContinuousMap.coe_mk]
        exact (Finset.prod_attach s _).symm)
    exact hc.trans ((loopWinding_mul Γprod U hΓprod hU).trans (by
      rw [hΓprodwind, hUwind, add_zero]))
  refine ⟨s, hs, hord, hw, ?_⟩
  intro hn
  have hsne : s.Nonempty := by
    by_contra hempty
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hw, he, Finset.sum_empty] at hn
    exact hn rfl
  obtain ⟨x, hx⟩ := hsne
  exact ⟨x, (hs x).mp hx⟩


end
end HolomorphicAnosov
