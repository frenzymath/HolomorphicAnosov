import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Homeomorph.Defs
import HolomorphicAnosov.Analysis.SmallDiskDerivativeRadius
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.CircleIntegral
import HolomorphicAnosov.Analysis.InteriorVariationBound
import HolomorphicAnosov.Analysis.BoundedVariationIntervalCompletion
import HolomorphicAnosov.Topology.HomeomorphLimitFrontier

/-!
# Short circular crosscuts from finite Dirichlet energy

Source: Terence Tao, *246C Notes 2* (12 April 2018), §2, Theorem 20 proof,
`literature/Tao-246C-Notes2-2018.txt`, lines 255–267. Supplement: Curtis T. McMullen,
*Advanced Complex Analysis*, 22 January 2017 version, printed p. 59, Lemma 4.6 proof.

This module proves the finite-energy portion of the argument. Neither a Jordan boundary nor
boundedness of the image domain is assumed. Curve length is Mathlib's `eVariationOn`: its
literal definition is the supremum of the sums of extended Euclidean distances over finite
nondecreasing sequences of parameters in the indicated closed interval. Repeated parameters
contribute zero, so this is the usual ordered finite-partition definition of length.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology _root_.Topology ENNReal

namespace HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts

/-- The total representative of a disk homeomorphism, equal to zero outside the disk.
Source: the zero-extension convention in Tao, Theorem 20 proof. Only its interior derivative
is used; no continuity or differentiability at the unit circle is asserted. -/
def diskExtension {Q : Set ℂ} (e : (Metric.ball (0 : ℂ) 1) ≃ₜ Q) (z : ℂ) : ℂ :=
  by
    classical
    exact if hz : z ∈ Metric.ball (0 : ℂ) 1 then (e ⟨z, hz⟩).val else 0

/-- A rotated circle parametrization centered at the unit point `ζ`.
Source: Tao, Theorem 20 proof; rotating the angular coordinate makes the source interval
independent of the argument chosen for `ζ`. -/
def circleArcMap (ζ : ℂ) (r t : ℝ) : ℂ :=
  ζ + ζ * circleMap 0 r t

/-- Left parameter of the circular arc inside the disk, for `0 < r < 1`.
Source: the identity `|ζ + ζ r exp(it)|² = 1 + r² + 2r cos(t)` in Tao's circular construction. -/
def arcStart (r : ℝ) : ℝ := Real.pi - Real.arccos (r / 2)

/-- Right parameter of the circular arc inside the disk, for `0 < r < 1`.
Source: the same circular construction in Tao, Theorem 20 proof. -/
def arcEnd (r : ℝ) : ℝ := Real.pi + Real.arccos (r / 2)

/-- A holomorphic disk homeomorphism with finite nonnegative Dirichlet lower integral admits
strictly shrinking circular crosscuts with continuous rectifiable completions whose lengths
tend to zero and whose endpoint values lie in the image frontier. The endpoint values may
coincide. Holomorphy is `DifferentiableOn ℂ` on the open disk; planar area is canonical complex
Lebesgue `volume`. Every geometric and rectifiability condition concerns only the displayed
parameter interval; the total representatives carry no exterior regularity requirement.

Source: Tao, *246C Notes 2*, §2, Theorem 20 proof, lines 255–267; McMullen,
*Advanced Complex Analysis*, 22 January 2017 version, printed p. 59, Lemma 4.6 proof.

Natural-language proof:

1. On the open disk, holomorphy implies complex smoothness of every finite order, and φ′ is
holomorphic and therefore continuous. Define F:ℂ→[0,∞] by F(z)=ofReal(|φ′(z)|²) for z∈D and F(z)=0
otherwise. This piecewise definition evaluates the derivative only on D; any total representative
of φ gives the same interior derivative by local equality. D is open and measurable, so continuity
on D and continuity of the zero function on its complement imply that F is Borel measurable. The
given nonnegative energy is precisely ∫⁻_ℂ F dA<⊤. A totalized Bochner integral, which is zero for
a nonintegrable function, is not used as a finiteness criterion.

2. For ζ∈S¹ define E(r)=∫⁻_{t∈(-π,π)} F(ζ+r(cos t+i sin t)) dt, retaining its ENNReal value even
when infinite. Translation by ζ preserves canonical planar Lebesgue volume. Apply the exact polar
lower-integral identity to w↦F(ζ+w); its radius coordinate is r∈(0,∞) and its angular coordinate
is t∈(-π,π). The polar density (r,t)↦ofReal(r)F(ζ+r exp(it)) is Borel measurable. Tonelli applies
to the product of the restricted real Lebesgue measures; the angular measure is finite, hence
s-finite. Pull the finite coefficient ofReal(r) through each angular lower integral to obtain
∫⁻_{r>0}ofReal(r)E(r)dr=∫⁻_ℂ FdA<⊤. The parameter integral E is measurable. For r≥2 the circle
does not meet D because |ζ|=1, so the density vanishes; in particular its restriction to (0,2) has
finite lower integral. No finite-slice conclusion has yet been imposed on every r.

3. Specialize `HolomorphicAnosov.Analysis.exists_small_disk_derivative_radius` to
`f := diskExtension e`, the given `hhol`, `henergy`, and center `ζ`. For any positive δ and ε
this supplies r∈(0,δ) with ofReal(r²)E(r)<ofReal(ε). In particular this applies for 0<δ<2.
The source argument implemented by that public helper is as follows. Otherwise this
inequality fails at every r∈(0,δ). Since r>0, division by the positive finite coefficient
ofReal(r) gives ofReal(ε/r)≤ofReal(r)E(r), also when E(r)=⊤. The real function r↦r⁻¹ is measurable
and nonnegative on (0,δ). If its nonnegative lower integral were finite, the exact
ofReal-integral/integrability equivalence would make it IntegrableOn there. On the positive
interval Real.rpow_neg identifies r^(-1) with r⁻¹, while integrableOn_Ioo_rpow_iff at exponent -1
and δ>0 says integrability would require -1<-1. Thus ∫⁻_(0,δ)ofReal(1/r)dr=⊤. Pulling the finite
positive factor ε through this lower integral shows ∫⁻_(0,δ)ofReal(ε/r)dr=⊤. Pointwise
lower-integral comparison contradicts the finite radial energy. This proves the asserted selection
property directly for the actual lower-integral values; it does not rely on assigning finite
values on a null set.

4. Recursively apply the preceding property with ε_n=(n+2)⁻² and δ_0=1/2,
δ_n=min(1/2,r_(n-1)/2,1/(n+2)) for n≥1. Every δ_n is positive and less than 2. It gives 0<r_n<δ_n
and r_n²E(r_n)<ε_n. Because r_n² is strictly positive and finite and ε_n is finite, E(r_n)<⊤; only
at these selected radii may its value be converted to a finite real number. The radii lie in
(0,1), satisfy r_n<r_(n-1)/2 and tend to zero, and their scaled energies tend to zero by the
explicit ε_n bound. This handles strict decrease as well as arbitrarily small good radii.

5. Fix one chosen radius r, put β=arccos(r/2), A=π−β and B=π+β, and use the
rotated circle γ(t)=ζ+ζr exp(it). Since 0<r<1, 0<β<π/2 and B−A=2β<π<2π. The identity
|γ(t)|²=1+r²+2r cos(t) identifies γ((A,B)) with D∩sphere(ζ,r); its endpoints have norm
one. The interval length is less than one period, so γ is injective on [A,B]. Compactness
and continuity identify its closed-interval image with the closure of its open image.
Writing ζ=exp(i arg ζ) gives γ(t)=ζ+r exp(i(t+arg ζ)). Translate by arg ζ using the
measure-preserving measurable embedding of ℝ. The translated interval lies in one half-open
interval of length 2π. Periodicity makes the density invariant under integer multiples of
2π; the fundamental-domain lower-integral identity equates its integral over any such full
period with its integral over (−π,π]. Null endpoints identify this with E(r). Monotonicity
therefore bounds the arc energy by E(r), including when the original arc crosses the polar
seam and without assuming angular-slice finiteness in advance.

6. On J put S(t)=r|φ′(γ(t))| and let L=∫⁻_J ofReal(S(t))dt. All derivatives here are at points of
D. The angular functions are Borel. Apply the ENNReal Hölder inequality with p=q=2 to |φ′∘γ| and
the constant 1 under μ=volume.restrict J. Its constant squared integral is μ(J)=ofReal(B−A), by
the exact real interval-volume theorem. The preceding angular-energy comparison yields
L≤(ofReal(r²)E(r))^(1/2) times ofReal(2π)^(1/2)<∞. The scaled energies tend to zero
by the explicit recursion bound. Continuity of ENNReal powers and multiplication by the finite
constant makes this bound tend to zero; squeezing gives L_n→0 entirely in ENNReal. No
a.e.-to-pointwise differentiability inference or bounded derivative near an endpoint is used.

7. For every A<s≤t<B, the compact interval [s,t] maps by γ into D. Complex smoothness of φ
restricts to real C¹ with the canonical ℝ→ℂ scalar tower; composition with the real-smooth circle
map is C¹ on [s,t]. Apply real scalar restriction and composition with the explicit
inclusion γ([s,t])⊆D. The rotated circle derivative is γ′(u)=ζr exp(iu)i, of norm r. The mixed real/complex scalar chain rule then gives the real derivative of ψ=φ∘γ as
φ′(γ(u))γ′(u), with norm S(u), throughout [s,t]. The C¹ displacement estimate gives
|ψ(t)−ψ(s)|≤∫⁻_[s,t]ofReal(S(u))du. Real Lebesgue null singletons identify this integral with its
open-interval version. Summing over any ordered finite partition with points in J and using finite
disjoint-union additivity bounds the sum of chord lengths by L. This proves the open image arc is
rectifiable directly from the partition definition of length, without differentiating its eventual
boundary completion.

8. The speed lower integral L is finite. The public interior variation theorem applies to
ψ=φ∘γ, which is real C¹ on J. Its conclusion and the exact derivative-speed identity give
variation(ψ,J)≤L<∞. Bounded variation in complete ℂ supplies both one-sided endpoint limits;
Mathlib proves this using the Cauchy estimates for variation on shrinking interval tails. This
is the same finite-length endpoint-completion step implicit in Tao's rectifiability paragraph,
without compactness of Q or a boundary regularity assumption.

9. Apply the public bounded-variation interval completion theorem. It uses `extendFrom` to
choose the one-sided limits at the two endpoints and agrees with ψ throughout J. The result Ψ
is continuous on [A,B]. Adjoining a point where the one-sided limit agrees with the endpoint
value does not change extended variation; applying this once at B and once at A gives exactly
variation(Ψ,[A,B])=variation(ψ,J)≤L. Injectivity inside J follows from the injectivity of φ and γ.
No distinctness of the two endpoint values is assumed. Since L_n tends to zero, the completed
variations tend to zero by squeezing in ENNReal.

10. Since ψ(t)∈Q on J, the limits a,b lie in closure(Q). If a belonged to the open set Q, the
continuous inverse homeomorphism φ⁻¹:Q→D would imply γ(t)=φ⁻¹(ψ(t))→φ⁻¹(a)∈D as t→A. But the
explicit circle parametrization has γ(t)→γ(A)∈S¹. Uniqueness of limits in ℂ would give
φ⁻¹(a)=γ(A), contradicting |γ(A)|=1. The same argument excludes b∈Q. As Q is open,
closure(Q)\Q=∂Q, so both endpoints lie on ∂Q. This does not identify different endpoints of the
completed image curve; a=b is permitted.

For the exported parametrization, rotate the angular coordinate by the argument of ζ. The source
interval [α+π−β, α+π+β] becomes [π−β, π+β], with β=arccos(r/2). Translation of angular Lebesgue
measure and the periodic fundamental-domain identity preserve every energy and speed estimate. Its
closed-interval image is precisely the closure of the open source arc. The source-circle endpoints
are distinct; the completed image endpoints need not be. Finally, the length bounds give
convergence in ENNReal as well as in real length.
-/
theorem exists_short_crosscuts {Q : Set ℂ} (hQ : IsOpen Q)
    (e : (Metric.ball (0 : ℂ) 1) ≃ₜ Q)
    (hhol : DifferentiableOn ℂ (diskExtension e) (Metric.ball (0 : ℂ) 1))
    (henergy : (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖deriv (diskExtension e) z‖ ^ 2) ∂volume) < ⊤)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ∃ (r : ℕ → ℝ) (Ψ : ℕ → ℝ → ℂ),
      StrictAnti r ∧
      (∀ n, 0 < r n ∧ r n < 1) ∧
      Tendsto r atTop (𝓝 0) ∧
      (∀ n,
        arcStart (r n) < arcEnd (r n) ∧
        arcEnd (r n) - arcStart (r n) < 2 * Real.pi ∧
        ContinuousOn (circleArcMap ζ (r n)) (Icc (arcStart (r n)) (arcEnd (r n))) ∧
        InjOn (circleArcMap ζ (r n)) (Icc (arcStart (r n)) (arcEnd (r n))) ∧
        circleArcMap ζ (r n) '' Ioo (arcStart (r n)) (arcEnd (r n)) =
          Metric.ball (0 : ℂ) 1 ∩ Metric.sphere ζ (r n) ∧
        circleArcMap ζ (r n) '' Icc (arcStart (r n)) (arcEnd (r n)) =
          closure (Metric.ball (0 : ℂ) 1 ∩ Metric.sphere ζ (r n)) ∧
        ‖circleArcMap ζ (r n) (arcStart (r n))‖ = 1 ∧
        ‖circleArcMap ζ (r n) (arcEnd (r n))‖ = 1 ∧
        ContinuousOn (Ψ n) (Icc (arcStart (r n)) (arcEnd (r n))) ∧
        EqOn (Ψ n) (diskExtension e ∘ circleArcMap ζ (r n))
          (Ioo (arcStart (r n)) (arcEnd (r n))) ∧
        InjOn (Ψ n) (Ioo (arcStart (r n)) (arcEnd (r n))) ∧
        eVariationOn (Ψ n) (Icc (arcStart (r n)) (arcEnd (r n))) < ⊤ ∧
        Ψ n (arcStart (r n)) ∈ frontier Q ∧
        Ψ n (arcEnd (r n)) ∈ frontier Q) ∧
      Tendsto (fun n ↦ eVariationOn (Ψ n) (Icc (arcStart (r n)) (arcEnd (r n))))
        atTop (𝓝 0) := by
  classical
  let F : ℂ → ℝ≥0∞ := (Metric.ball (0 : ℂ) 1).indicator
    (fun z ↦ ENNReal.ofReal (‖deriv (diskExtension e) z‖ ^ 2))
  let E : ℝ → ℝ≥0∞ := fun r ↦ ∫⁻ t in Ioo (-Real.pi) Real.pi,
    F (ζ + Complex.polarCoord.symm (r, t)) ∂volume
  have hsmall : ∀ {δ ε : ℝ}, 0 < δ → 0 < ε →
      ∃ r ∈ Ioo (0 : ℝ) δ, ENNReal.ofReal (r ^ 2) * E r < ENNReal.ofReal ε := by
    intro δ ε hδ hε
    exact HolomorphicAnosov.Analysis.exists_small_disk_derivative_radius
      (diskExtension e) hhol henergy ζ hδ hε
  let b : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 2)
  have hb : ∀ n, 0 < b n := by intro n; dsimp [b]; positivity
  have hchoose : ∀ (n : ℕ) (x : {x : ℝ // 0 < x}),
      ∃ y : {y : ℝ // 0 < y},
        y.val < min (1 / 2) (min (x.val / 2) (b n)) ∧
        ENNReal.ofReal (y.val ^ 2) * E y.val < ENNReal.ofReal (b n ^ 2) := by
    intro n x
    obtain ⟨y, hy, hEy⟩ := hsmall
      (show 0 < min (1 / 2 : ℝ) (min (x.val / 2) (b n)) from
        lt_min (by norm_num) (lt_min (half_pos x.property) (hb n)))
      (sq_pos_of_pos (hb n))
    exact ⟨⟨y, hy.1⟩, hy.2, hEy⟩
  choose next hnext using hchoose
  let u : ℕ → {x : ℝ // 0 < x} :=
    fun n ↦ Nat.rec (next 0 ⟨1, by norm_num⟩) (fun k x ↦ next (k + 1) x) n
  let r : ℕ → ℝ := fun n ↦ (u n).val
  have hrpos : ∀ n, 0 < r n := fun n ↦ (u n).property
  have hrspec : ∀ n, r n < (1 / 2 : ℝ) ∧ r n < b n ∧
      ENNReal.ofReal (r n ^ 2) * E (r n) < ENNReal.ofReal (b n ^ 2) := by
    intro n
    cases n with
    | zero =>
      have h := hnext 0 ⟨1, by norm_num⟩
      exact ⟨lt_of_lt_of_le h.1 (min_le_left _ _),
        lt_of_lt_of_le h.1 ((min_le_right _ _).trans (min_le_right _ _)), h.2⟩
    | succ n =>
      have h := hnext (n + 1) (u n)
      exact ⟨lt_of_lt_of_le h.1 (min_le_left _ _),
        lt_of_lt_of_le h.1 ((min_le_right _ _).trans (min_le_right _ _)), h.2⟩
  have hrhalf : ∀ n, r (n + 1) < r n / 2 := by
    intro n
    exact lt_of_lt_of_le (hnext (n + 1) (u n)).1
      ((min_le_right _ _).trans (min_le_left _ _))
  have hranti : StrictAnti r := strictAnti_nat_of_succ_lt fun n ↦
    (hrhalf n).trans (half_lt_self (hrpos n))
  have hrunit : ∀ n, 0 < r n ∧ r n < 1 := fun n ↦
    ⟨hrpos n, (hrspec n).1.trans (by norm_num)⟩
  have hbzero : Tendsto b atTop (𝓝 0) := by
    simpa [b, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hrzero : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ (hrpos n).le) (fun n ↦ (hrspec n).2.1.le) hbzero
  have hEfinite : ∀ n, E (r n) < ⊤ := by
    intro n
    apply lt_top_iff_ne_top.mpr
    intro he
    have hc : ENNReal.ofReal (r n ^ 2) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hrpos n)))
    have h := (hrspec n).2.2
    simp [he, hc] at h
  have hboundzero : Tendsto (fun n ↦ ENNReal.ofReal (b n ^ 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hbzero.pow 2)
  have henergyzero :
      Tendsto (fun n ↦ ENNReal.ofReal (r n ^ 2) * E (r n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundzero
      (fun _ ↦ bot_le) (fun n ↦ (hrspec n).2.2.le)
  have hζne : ζ ≠ 0 := by intro hz; simp [hz] at hζ
  have harc : ∀ n, arcStart (r n) < arcEnd (r n) ∧
      arcEnd (r n) - arcStart (r n) < 2 * Real.pi := by
    intro n
    have hp : 0 < Real.arccos (r n / 2) := Real.arccos_pos.mpr (by linarith [(hrunit n).2])
    have hq : Real.arccos (r n / 2) < Real.pi / 2 :=
      Real.arccos_lt_pi_div_two.mpr (half_pos (hrpos n))
    dsimp [arcStart, arcEnd]
    constructor <;> linarith [Real.pi_pos]
  have hcont : ∀ n, ContinuousOn (circleArcMap ζ (r n))
      (Icc (arcStart (r n)) (arcEnd (r n))) := by
    intro n
    unfold circleArcMap
    fun_prop
  have hinj : ∀ n, InjOn (circleArcMap ζ (r n))
      (Icc (arcStart (r n)) (arcEnd (r n))) := by
    intro n a ha b hb hab
    apply eq_of_circleMap_eq (c := (0 : ℂ)) (ne_of_gt (hrpos n))
    · rw [abs_lt]
      constructor <;> linarith [(harc n).2, ha.1, ha.2, hb.1, hb.2]
    · exact mul_left_cancel₀ hζne (add_left_cancel hab)
  have hnormsq : ∀ n t, ‖circleArcMap ζ (r n) t‖ ^ 2 =
      1 + r n ^ 2 + 2 * r n * Real.cos t := by
    intro n t
    have hfactor : circleArcMap ζ (r n) t = ζ * (1 + circleMap 0 (r n) t) := by
      dsimp [circleArcMap]; ring
    rw [hfactor, norm_mul, hζ, one_mul, ← Complex.normSq_eq_norm_sq]
    rw [circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    nlinarith [mul_nonneg (sq_nonneg (r n)) (sq_nonneg (Real.sin t)),
      congrArg (fun x : ℝ ↦ (r n)^2 * x) (Real.sin_sq_add_cos_sq t)]
  have hendpoints : ∀ n, ‖circleArcMap ζ (r n) (arcStart (r n))‖ = 1 ∧
      ‖circleArcMap ζ (r n) (arcEnd (r n))‖ = 1 := by
    intro n
    have hc : Real.cos (Real.arccos (r n / 2)) = r n / 2 :=
      Real.cos_arccos (by linarith [hrpos n]) (by linarith [(hrunit n).2])
    constructor
    · have h := hnormsq n (arcStart (r n))
      change ‖circleArcMap ζ (r n) (arcStart (r n))‖ ^ 2 =
        1 + r n ^ 2 + 2 * r n * Real.cos (Real.pi - Real.arccos (r n / 2)) at h
      rw [Real.cos_pi_sub, hc] at h
      nlinarith [norm_nonneg (circleArcMap ζ (r n) (arcStart (r n)))]
    · have h := hnormsq n (arcEnd (r n))
      change ‖circleArcMap ζ (r n) (arcEnd (r n))‖ ^ 2 =
        1 + r n ^ 2 + 2 * r n * Real.cos (Real.pi + Real.arccos (r n / 2)) at h
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi, hc] at h
      nlinarith [norm_nonneg (circleArcMap ζ (r n) (arcEnd (r n)))]
  have hinside : ∀ n, MapsTo (circleArcMap ζ (r n))
      (Ioo (arcStart (r n)) (arcEnd (r n))) (Metric.ball (0 : ℂ) 1) := by
    intro n t ht
    have ha : |t - Real.pi| < Real.arccos (r n / 2) := by
      rw [abs_lt]; dsimp [arcStart, arcEnd] at ht; constructor <;> linarith [ht.1, ht.2]
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (t - Real.pi))
      (Real.arccos_le_pi (r n / 2)) ha
    rw [Real.cos_arccos (by linarith [hrpos n]) (by linarith [(hrunit n).2]),
      Real.cos_abs, Real.cos_sub_pi] at hc
    have hm := mul_lt_mul_of_pos_left hc (hrpos n)
    have hn := hnormsq n t
    simp only [Metric.mem_ball, dist_zero_right]
    nlinarith [norm_nonneg (circleArcMap ζ (r n) t)]
  have hsphere : ∀ n t, circleArcMap ζ (r n) t ∈ Metric.sphere ζ (r n) := by
    intro n t
    simp [circleArcMap, hζ,
      norm_circleMap_zero, abs_of_pos (hrpos n)]
  have hperiod : ∀ n, Function.Periodic
      (fun t ↦ F (ζ + circleMap 0 (r n) t)) (2 * Real.pi) := by
    intro n t
    dsimp only
    rw [periodic_circleMap 0 (r n) t]
  have hfullperiod : ∀ n a,
      (∫⁻ t in Ioc a (a + 2 * Real.pi), F (ζ + circleMap 0 (r n) t)) =
        ∫⁻ t in Ioc (-Real.pi) Real.pi, F (ζ + circleMap 0 (r n) t) := by
    intro n a
    have : VAddInvariantMeasure (AddSubgroup.zmultiples (2 * Real.pi)) ℝ volume :=
      ⟨fun c s _ ↦ measure_preimage_add _ _ _⟩
    have h := (isAddFundamentalDomain_Ioc (by positivity : 0 < 2 * Real.pi) a volume).setLIntegral_eq
      (isAddFundamentalDomain_Ioc (by positivity : 0 < 2 * Real.pi) (-Real.pi) volume)
      (fun t ↦ F (ζ + circleMap 0 (r n) t)) (hperiod n).map_vadd_zmultiples
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using h
  have hrotate : ∀ n t, circleArcMap ζ (r n) t =
      ζ + circleMap 0 (r n) (t + ζ.arg) := by
    intro n t
    have hz : ζ = Complex.exp (ζ.arg * Complex.I) := by
      have hh := Complex.norm_mul_exp_arg_mul_I ζ
      rw [hζ] at hh
      simpa using hh.symm
    simp only [circleArcMap, circleMap_zero]
    rw [show ((t + ζ.arg : ℝ) : ℂ) * Complex.I =
      ζ.arg * Complex.I + (t : ℂ) * Complex.I by push_cast; ring, Complex.exp_add]
    nth_rw 2 [hz]
    ring
  have hpolar : ∀ n t, circleMap 0 (r n) t = Complex.polarCoord.symm (r n, t) := by
    intro n t
    simp only [circleMap_zero, Complex.polarCoord_symm_apply,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hangleenergy : ∀ n,
      (∫⁻ t in Ioo (arcStart (r n)) (arcEnd (r n)), F (circleArcMap ζ (r n) t)) ≤ E (r n) := by
    intro n
    simp_rw [hrotate n]
    rw [(measurePreserving_add_right volume ζ.arg).setLIntegral_comp_emb
      (Homeomorph.addRight ζ.arg).measurableEmbedding
      (fun t ↦ F (ζ + circleMap 0 (r n) t)) (Ioo (arcStart (r n)) (arcEnd (r n)))]
    have hsub : (fun t : ℝ ↦ t + ζ.arg) '' Ioo (arcStart (r n)) (arcEnd (r n)) ⊆
        Ioc (arcStart (r n) + ζ.arg) (arcStart (r n) + ζ.arg + 2 * Real.pi) := by
      rintro x ⟨t, ht, rfl⟩
      exact ⟨by linarith [ht.1], by linarith [ht.2, (harc n).2]⟩
    refine (lintegral_mono_set hsub).trans_eq ?_
    rw [hfullperiod]
    simp_rw [hpolar n]
    exact congrArg (fun μ : Measure ℝ ↦ ∫⁻ t, F (ζ + Complex.polarCoord.symm (r n, t)) ∂μ)
      (restrict_Ioo_eq_restrict_Ioc (μ := (volume : Measure ℝ))).symm
  have hclosedimage : ∀ n,
      circleArcMap ζ (r n) '' Icc (arcStart (r n)) (arcEnd (r n)) =
        closure (circleArcMap ζ (r n) '' Ioo (arcStart (r n)) (arcEnd (r n))) := by
    intro n
    have hcl : closure (Ioo (arcStart (r n)) (arcEnd (r n))) =
        Icc (arcStart (r n)) (arcEnd (r n)) := closure_Ioo (harc n).1.ne
    simpa only [hcl] using image_closure_of_isCompact
      (show IsCompact (closure (Ioo (arcStart (r n)) (arcEnd (r n)))) by
        rw [hcl]; exact isCompact_Icc)
      (show ContinuousOn (circleArcMap ζ (r n))
          (closure (Ioo (arcStart (r n)) (arcEnd (r n)))) by
        rw [hcl]; exact hcont n)
  have hopenimage_subset : ∀ n,
      circleArcMap ζ (r n) '' Ioo (arcStart (r n)) (arcEnd (r n)) ⊆
        Metric.ball (0 : ℂ) 1 ∩ Metric.sphere ζ (r n) := by
    rintro n z ⟨t, ht, rfl⟩
    exact ⟨hinside n ht, hsphere n t⟩
  have hclosedimage_subset : ∀ n,
      circleArcMap ζ (r n) '' Icc (arcStart (r n)) (arcEnd (r n)) ⊆
        closure (Metric.ball (0 : ℂ) 1 ∩ Metric.sphere ζ (r n)) := by
    intro n
    rw [hclosedimage]
    exact closure_mono (hopenimage_subset n)
  have hopenimage : ∀ n,
      circleArcMap ζ (r n) '' Ioo (arcStart (r n)) (arcEnd (r n)) =
        Metric.ball (0 : ℂ) 1 ∩ Metric.sphere ζ (r n) := by
    intro n
    apply Subset.antisymm (hopenimage_subset n)
    intro z hz
    let v : ℂ := -(z - ζ) / ζ
    have hvnorm : ‖v‖ = r n := by
      dsimp [v]
      rw [norm_div, norm_neg, hζ, div_one]
      simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz.2
    have hzrep : circleArcMap ζ (r n) (Real.pi + v.arg) = z := by
      have hv := Complex.norm_mul_exp_arg_mul_I v
      rw [hvnorm] at hv
      simp only [circleArcMap, circleMap_zero, Complex.ofReal_add, add_mul,
        Complex.exp_add, Complex.exp_pi_mul_I]
      calc
        ζ + ζ * ((r n : ℂ) * (-1 * Complex.exp (v.arg * Complex.I))) =
            ζ - ζ * ((r n : ℂ) * Complex.exp (v.arg * Complex.I)) := by ring
        _ = ζ - ζ * v := by rw [hv]
        _ = z := by dsimp [v]; field_simp; ring
    have hcos : r n / 2 < Real.cos v.arg := by
      have hn := hnormsq n (Real.pi + v.arg)
      rw [hzrep, Real.cos_add, Real.cos_pi, Real.sin_pi] at hn
      have hzlt : ‖z‖ < 1 := by simpa using hz.1
      have hzsq : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
      have hm : 0 < r n := hrpos n
      nlinarith
    have harg : |v.arg| < Real.arccos (r n / 2) := by
      by_contra h
      have hle := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg (r n / 2))
        (Complex.abs_arg_le_pi v) (le_of_not_gt h)
      rw [Real.cos_abs, Real.cos_arccos (by linarith [hrpos n])
        (by linarith [(hrunit n).2])] at hle
      exact (not_le_of_gt hcos) hle
    refine ⟨Real.pi + v.arg, ?_, hzrep⟩
    rw [abs_lt] at harg
    dsimp [arcStart, arcEnd]
    exact ⟨by linarith [harg.1], by linarith [harg.2]⟩
  have hclosedimage_exact : ∀ n,
      circleArcMap ζ (r n) '' Icc (arcStart (r n)) (arcEnd (r n)) =
        closure (Metric.ball (0 : ℂ) 1 ∩ Metric.sphere ζ (r n)) := by
    intro n
    rw [hclosedimage, hopenimage]
  have hFmeas : Measurable F := by
    have hc : ContinuousOn (fun z ↦ ENNReal.ofReal (‖deriv (diskExtension e) z‖ ^ 2))
        (Metric.ball (0 : ℂ) 1) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (((hhol.deriv Metric.isOpen_ball).continuousOn.norm).pow 2)
    exact hc.measurable_piecewise continuousOn_const Metric.isOpen_ball.measurableSet
  let S : ℕ → ℝ → ℝ≥0∞ := fun n t ↦
    ENNReal.ofReal (r n) * F (circleArcMap ζ (r n) t) ^ (1 / 2 : ℝ)
  let L : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ t in Ioo (arcStart (r n)) (arcEnd (r n)), S n t
  have hSmeas : ∀ n, Measurable (S n) := by
    intro n
    apply measurable_const.mul
    apply Measurable.pow_const
    apply hFmeas.comp
    unfold circleArcMap
    fun_prop
  have hSsq : ∀ n t, S n t ^ (2 : ℝ) =
      ENNReal.ofReal (r n ^ 2) * F (circleArcMap ζ (r n) t) := by
    intro n t
    dsimp [S]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_natCast, ENNReal.ofReal_pow (hrpos n).le]
  have hSactual : ∀ n t, t ∈ Ioo (arcStart (r n)) (arcEnd (r n)) →
      S n t = ENNReal.ofReal (r n * ‖deriv (diskExtension e) (circleArcMap ζ (r n) t)‖) := by
    intro n t ht
    dsimp [S, F]
    rw [indicator_of_mem (hinside n ht), ENNReal.ofReal_pow (norm_nonneg _) 2]
    have hh := ENNReal.pow_rpow_inv_natCast (by decide : (2 : ℕ) ≠ 0)
      (ENNReal.ofReal ‖deriv (diskExtension e) (circleArcMap ζ (r n) t)‖)
    norm_num only [Nat.cast_ofNat, inv_eq_one_div] at hh
    rw [hh]
    exact (ENNReal.ofReal_mul (hrpos n).le).symm
  have hLbound : ∀ n, L n ≤
      (ENNReal.ofReal (r n ^ 2) * E (r n)) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (2 * Real.pi) ^ (1 / 2 : ℝ) := by
    intro n
    have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq
      (volume.restrict (Ioo (arcStart (r n)) (arcEnd (r n))))
      Real.HolderConjugate.two_two (hSmeas n).aemeasurable
      (measurable_const.aemeasurable : AEMeasurable (fun _ : ℝ ↦ (1 : ℝ≥0∞)) _)
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one,
      Measure.restrict_apply_univ, Real.volume_Ioo] at hh
    simp_rw [hSsq n] at hh
    have hsint : (∫⁻ t in Ioo (arcStart (r n)) (arcEnd (r n)),
        ENNReal.ofReal (r n ^ 2) * F (circleArcMap ζ (r n) t)) =
        ENNReal.ofReal (r n ^ 2) *
          ∫⁻ t in Ioo (arcStart (r n)) (arcEnd (r n)), F (circleArcMap ζ (r n) t) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [hsint] at hh
    exact hh.trans (mul_le_mul'
      (ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (hangleenergy n)) (by norm_num))
      (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (harc n).2.le) (by norm_num)))
  have hLfinite : ∀ n, L n < ⊤ := by
    intro n
    exact (hLbound n).trans_lt (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hEfinite n)).ne)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  have hLzero : Tendsto L atTop (𝓝 0) := by
    have hroot : Tendsto (fun n ↦ (ENNReal.ofReal (r n ^ 2) * E (r n)) ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
        (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp henergyzero
    have hbound := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal (2 * Real.pi) ^ (1 / 2 : ℝ)) hroot
      (Or.inr (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
        ENNReal.ofReal_ne_top).ne)
    simp only [zero_mul] at hbound
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ ↦ bot_le) hLbound
  let ψ : ℕ → ℝ → ℂ := fun n ↦ diskExtension e ∘ circleArcMap ζ (r n)
  have hγderiv : ∀ n t, HasDerivAt (circleArcMap ζ (r n))
      (ζ * (circleMap 0 (r n) t * Complex.I)) t := by
    intro n t
    exact ((hasDerivAt_circleMap 0 (r n) t).const_mul ζ).const_add ζ
  have hψderiv : ∀ n t, t ∈ Ioo (arcStart (r n)) (arcEnd (r n)) →
      HasDerivAt (ψ n) (deriv (diskExtension e) (circleArcMap ζ (r n) t) *
        (ζ * (circleMap 0 (r n) t * Complex.I))) t := by
    intro n t ht
    exact ((hhol _ (hinside n ht)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hinside n ht))).hasDerivAt.comp t (hγderiv n t)
  have hψspeed : ∀ n t, t ∈ Ioo (arcStart (r n)) (arcEnd (r n)) →
      ‖deriv (ψ n) t‖ₑ = S n t := by
    intro n t ht
    rw [(hψderiv n t ht).deriv, hSactual n t ht]
    rw [← ofReal_norm]
    congr 1
    simp [hζ, norm_circleMap_zero, abs_of_pos (hrpos n), mul_comm]
  have hψsmooth : ∀ n, ContDiffOn ℝ 1 (ψ n) (Ioo (arcStart (r n)) (arcEnd (r n))) := by
    intro n
    apply ((hhol.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ).comp
    · exact (contDiff_const.add (contDiff_const.mul (contDiff_circleMap 0 (r n)))).contDiffOn
    · exact hinside n
  have hψinj : ∀ n, InjOn (ψ n) (Ioo (arcStart (r n)) (arcEnd (r n))) := by
    intro n a ha b hb heq
    apply hinj n (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb)
    have he : e ⟨circleArcMap ζ (r n) a, hinside n ha⟩ =
        e ⟨circleArcMap ζ (r n) b, hinside n hb⟩ := by
      apply Subtype.ext
      simpa only [ψ, Function.comp_apply, diskExtension, dite_eq_left (hinside n ha),
        dite_eq_left (hinside n hb)] using heq
    exact congrArg Subtype.val (e.injective he)
  have hvariation : ∀ n, eVariationOn (ψ n)
      (Ioo (arcStart (r n)) (arcEnd (r n))) ≤ L n := by
    intro n
    refine (HolomorphicAnosov.Analysis.eVariationOn_Ioo_le_lintegral_deriv_of_contDiffOn
      (hψsmooth n)).trans_eq ?_
    exact setLIntegral_congr_fun measurableSet_Ioo (hψspeed n)
  have hBV : ∀ n, BoundedVariationOn (ψ n)
      (Ioo (arcStart (r n)) (arcEnd (r n))) :=
    fun n ↦ ((hvariation n).trans_lt (hLfinite n)).ne
  choose Ψ hΨcont hΨeq hΨvariation using fun n ↦
    HolomorphicAnosov.Analysis.exists_continuousOn_Icc_eqOn_variation_of_boundedVariationOn
      (harc n).1 (hψsmooth n).continuousOn (hBV n)
  have hΨbound : ∀ n, eVariationOn (Ψ n)
      (Icc (arcStart (r n)) (arcEnd (r n))) ≤ L n := by
    intro n
    rw [hΨvariation n]
    exact hvariation n
  have hfrontier : ∀ n c, c ∈ Icc (arcStart (r n)) (arcEnd (r n)) →
      ‖circleArcMap ζ (r n) c‖ = 1 →
      (𝓝[Ioo (arcStart (r n)) (arcEnd (r n))] c).NeBot → Ψ n c ∈ frontier Q := by
    intro n c hc hunit hne
    let J := Ioo (arcStart (r n)) (arcEnd (r n))
    let K : Filter J := Filter.comap Subtype.val (𝓝[J] c)
    have : (𝓝[J] c).NeBot := hne
    have : K.NeBot := Filter.comap_coe_neBot_of_le_principal inf_le_right
    let x : J → Metric.ball (0 : ℂ) 1 := fun t ↦
      ⟨circleArcMap ζ (r n) t, hinside n t.property⟩
    have ht : Tendsto (Subtype.val : J → ℝ) K (𝓝[J] c) := Filter.tendsto_comap
    have hγ : Continuous (circleArcMap ζ (r n)) := by
      unfold circleArcMap
      exact continuous_const.add (continuous_const.mul (continuous_circleMap 0 (r n)))
    have hx : Tendsto (fun t ↦ (x t : ℂ)) K (𝓝 (circleArcMap ζ (r n) c)) :=
      hγ.continuousAt.tendsto.comp (ht.mono_right nhdsWithin_le_nhds)
    have hp : circleArcMap ζ (r n) c ∉ Metric.ball (0 : ℂ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right, hunit, lt_self_iff_false, not_false_eq_true]
    have hy : Tendsto (fun t ↦ (e (x t) : ℂ)) K (𝓝 (Ψ n c)) := by
      have ht' := ht.mono_right (nhdsWithin_mono c Ioo_subset_Icc_self)
      have h := (hΨcont n c hc).tendsto.comp ht'
      convert h using 1
      funext t
      rw [Function.comp_apply, hΨeq n t.property]
      simp only [ψ, Function.comp_apply, diskExtension, dite_eq_left (hinside n t.property), x]
    exact HolomorphicAnosov.Topology.Homeomorph.limit_mem_frontier e hQ x hx hp hy
  refine ⟨r, Ψ, hranti, hrunit, hrzero, ?_, ?_⟩
  · intro n
    refine ⟨(harc n).1, (harc n).2, hcont n, hinj n, hopenimage n, hclosedimage_exact n,
      (hendpoints n).1, (hendpoints n).2, hΨcont n, hΨeq n, ?_,
      (hΨbound n).trans_lt (hLfinite n), ?_, ?_⟩
    · intro a ha b hb heq
      apply hψinj n ha hb
      rwa [← hΨeq n ha, ← hΨeq n hb]
    · exact hfrontier n _ ⟨le_rfl, (harc n).1.le⟩ (hendpoints n).1
        (left_nhdsWithin_Ioo_neBot (harc n).1)
    · exact hfrontier n _ ⟨(harc n).1.le, le_rfl⟩ (hendpoints n).2
        (right_nhdsWithin_Ioo_neBot (harc n).1)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hLzero
      (fun _ ↦ bot_le) hΨbound


end HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts
