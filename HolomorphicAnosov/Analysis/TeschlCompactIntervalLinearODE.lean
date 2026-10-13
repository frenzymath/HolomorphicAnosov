import HolomorphicAnosov.Analysis.TeschlPicardOperator
import HolomorphicAnosov.Analysis.TeschlPicardOperatorApply
import HolomorphicAnosov.Analysis.TeschlPicardIterateBound
import HolomorphicAnosov.Analysis.TeschlPicardFixedPoint
import HolomorphicAnosov.Analysis.TeschlWholeIntegralSolution
import HolomorphicAnosov.Analysis.TeschlLinearODEUniqueness
import HolomorphicAnosov.Analysis.TeschlIntegralSolutionDerivative
import HolomorphicAnosov.Analysis.TeschlCompactIntegralSolution
import HolomorphicAnosov.Analysis.TeschlSolutionContDiffOne
import HolomorphicAnosov.Analysis.TeschlSolutionContDiffInfinity
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Linear ODEs on an entire compact coefficient interval

Source: Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*,
AMS-authorized author preliminary version, April 2012, Corollary 2.6, printed p.41
(PDF p.52), the factorial Picard estimate (2.29), printed pp.40–41, and the
homogeneous linear specialization Theorem 3.9, printed p.81 (PDF p.92).
Local source: `literature/Teschl-Ordinary-Differential-Equations-Dynamical-Systems-2012.pdf`.
DAG node: `analysis.teschl_compact_interval_linear_ode`.

The coefficient and solution are represented by total real functions, with hypotheses
and identities only on the stated interval. Uniqueness is equality on that interval;
values of a totalization outside it are not constrained. One-sided derivatives use
`Ici a` and `Iic b`, which have the correct interval germs because `a < b`.
A smooth coefficient extension is a separate function agreeing with the coefficient
on the interval; the coefficient's arbitrary totalization need not be smooth.
-/

open Set Function MeasureTheory Metric intervalIntegral
open scoped Interval ContDiff NNReal Nat Topology _root_.Topology

namespace HolomorphicAnosov



/-- Teschl's whole-interval linear initial-value theorem, with the integral formulation,
interior and one-sided endpoint calculus, converse, and smooth extension.

Source: Teschl, Corollary 2.6 and estimate (2.29), printed pp.40–41, and Theorem 3.9,
printed p.81, in the local April 2012 AMS-authorized author preliminary version.
The current DAG proof is reproduced below. Its auxiliary extensions in the endpoint
calculus are not global ODE hypotheses or assertions about arbitrary totalizations.

Natural-language proof:
First suppose t0=a. Continuity on the compact interval gives K≥1 with ||A(t)||≤K. Set x_0(t)=x0
and x_(m+1)(t)=x0+∫_a^t A(s)x_m(s)ds on ALL of [a,b]. The integrands A(s)x_m(s) are continuous on
the compact real interval [a,b]. Apply mathlib.continuousOn_integrableOn_compact with real
Lebesgue volume and codomain R^n, then restrict from Icc a b to each Ioc a t, to obtain
integrability before forming or subtracting interval integrals. Their primitives are continuous:
locally their increments are bounded by the interval length times a compact bound for the
integrand, using the registered constant norm-integral estimate. Thus every iterate is defined on
all of [a,b]. There is no state-domain restriction: A(t)x is defined for every x, which is
precisely the distinction in Teschl Cor2.6 between the entire space C([a,b],R^n) and the local
closed ball.

Write d_m=x_(m+1)−x_m and L=b−a. The first difference has ||d_0(t)||≤K||x0||(t−a) by the constant
norm-integral bound. For a≤t≤b subtract the two integrable Picard integrals to obtain
d_(m+1)(t)=∫_a^t A(s)d_m(s)ds. If the induction bound is ||d_m(s)||≤||x0||
K^(m+1)(s−a)^(m+1)/(m+1)!, then ||A(s)d_m(s)||≤g(s), where g(s)=||x0|| K^(m+2)(s−a)^(m+1)/(m+1)!.
The polynomial g is continuous on Icc a t, hence integrable there by
mathlib.continuousOn_integrableOn_compact, and integrable for volume restricted to Ioc a t by
restriction. Apply mathlib.norm_integral_le_of_norm_le with that restricted measure, vector
integrand A(s)d_m(s) and scalar majorant g; the bound holds pointwise on Ioc a t, hence almost
everywhere for the restricted measure. Because a≤t, the interval integral is exactly this Ioc set
integral. Thus ||d_(m+1)(t)||≤∫_a^t g(s)ds. Its polynomial primitive has full derivatives on the
real line, so the named FTC evaluates this as ||x0|| K^(m+2)(t−a)^(m+2)/(m+2)!. This proves
||d_m(t)||≤||x0|| K^(m+1)(t−a)^(m+1)/(m+1)! by induction. At t=a both integrals are zero. This is
the actual variable-majorant integral step of Teschl (2.29); using only length times the constant
supremum would lose the required factorial denominator.

Let c_m=||x0||(KL)^(m+1)/(m+1)!. Choose N so m+2≥2KL for m≥N. Then c_(m+1)≤c_m/2. Hence c_m→0 and
each tail Σ_(m=r)^q c_m≤2c_r once r≥N, by the finite geometric-sum identity. The telescoping
estimate ||x_q(t)−x_r(t)||≤Σ_(m=r)^(q−1)c_m makes x_m(t) Cauchy for each t, and the bound is
uniform in t. Completeness of R^n supplies a pointwise limit x(t); passing q to infinity in this
estimate proves uniform convergence. The uniform-limit continuity theorem then gives continuity of
x. This writes out the convergence normally supplied by the iterated contraction theorem in the
source, without requiring a separate theorem about completeness of the function space.

The norm bound gives ||∫_a^t A(s)(x_m(s)−x(s))ds||≤KL sup_[a,b]||x_m−x||, so the Picard identities
converge uniformly to x(t)=x0+∫_a^t A(s)x(s)ds. Put f(s)=A(s)x(s), continuous on [a,b]. Extend f
to all real s by f(a) for s<a and f(b) for s>b; the resulting f_ext is continuous, including at
both endpoints. Define the primitive H(t)=x0+∫_a^t f_ext(s)ds for all real t. For every real t,
including a,b, the difference quotient minus f_ext(t) equals h^(-1)∫_t^(t+h)(f_ext(s)−f_ext(t))ds;
its norm is bounded by the supremum of ||f_ext(s)−f_ext(t)|| on that short segment and tends to
zero by continuity. Thus H has FULL HasDerivAt with derivative f_ext at every t, and H agrees with
x on [a,b]. Restriction supplies the stated interior and one-sided endpoint derivatives without
claiming full endpoint derivatives for an arbitrary totalization of x. Conversely let z be any
continuous differential solution on [a,b], with right derivative A(a)z(a) at a and left derivative
A(b)z(b) at b. Extend it to real t by z_ext(t)=z(a)+(t−a)A(a)z(a) for t<a and
z_ext(t)=z(b)+(t−b)A(b)z(b) for t>b, leaving it equal to z on [a,b]. At a the left difference
quotient is identically A(a)z(a) and the right quotient has the same limit by hypothesis;
splitting a punctured neighborhood into its two sides proves FULL HasDerivAt there. At b the
identical argument gives derivative A(b)z(b). At each interior t it agrees locally with z and has
derivative A(t)z(t). Extend A(t)z(t) continuously and constantly beyond a,b if a total derivative
function is needed. It is interval-integrable by mathlib.continuousOn_integrableOn_compact on
every retained compact subinterval, followed by restriction to the corresponding half-open
interval. The named intervalIntegral_integral_eq_sub_of_hasDerivAt now applies to z_ext on
uIcc(t0,t), with full derivatives at every point INCLUDING its endpoints, yielding
z(t)−z(t0)=∫_(t0)^t A(s)z(s)ds for all t∈[a,b], for either order of the two times. All extensions
serve only this endpoint calculus argument and assert no differential equation outside [a,b].

The field v(t,z)=A(t)z is globally Lipschitz with constant K, with range set all of R^n. Thus the
registered right-interval ODE uniqueness theorem identifies any two solutions with equal value at
a, with all continuity and right-derivative hypotheses just verified. For an arbitrary t0, apply
the construction on [t0,b], and on [a,t0] reverse time u=t0−t and coefficient −A(t0−u). Glue the
two solutions at x0. Their derivatives agree at t0 because both limits are A(t0)x0, so the glued
solution satisfies the integral identity everywhere. Uniqueness on each side follows from the same
theorem after reversal. If one side has zero length it contributes only the value x0; no
derivative is inferred from a singleton alone.

If A extends smoothly to an open neighborhood of [a,b], choose slightly larger a′<a<b<b′ within
that neighborhood. Apply the same compact-interval existence with initial time t0 on [a′,b′];
uniqueness identifies its restriction with x. Since x′=Ax, repeated product differentiation shows
x is smooth on (a′,b′). For n=0 the only solution is zero. For A=0 the integral construction is
constantly x0, and for x0=0 it is constantly zero. The auxiliary K≥1 prevents division by a zero
bound; the proof permits arbitrarily large KL. A degenerate interval is not part of the a<b
statement and requires only the initial-value identity.

For the formal interval representation, all solution comparisons are `EqOn` the
original closed interval. The converse retains the initial value, the differential
equation on the open interval, and both one-sided endpoint derivatives. Smooth
extension is applied to any actual smooth coefficient extension `B` on an open `U`;
only a possibly smaller open coefficient neighborhood is used for the solution.
No positivity of `n`, smallness of the coefficient bound, or bound on `x0` is assumed.
-/
theorem teschl_compact_interval_linear_ode
    (n : ℕ) (a b t0 : ℝ) (hab : a < b) (ht0 : t0 ∈ Icc a b)
    (A : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ContinuousOn A (Icc a b)) (x0 : EuclideanSpace ℝ (Fin n)) :
    ∃ x : ℝ → EuclideanSpace ℝ (Fin n),
      ContinuousOn x (Icc a b) ∧
      (∀ t ∈ Icc a b, x t = x0 + ∫ s in t0..t, A s (x s)) ∧
      (∀ y : ℝ → EuclideanSpace ℝ (Fin n),
        ContinuousOn y (Icc a b) →
        (∀ t ∈ Icc a b, y t = x0 + ∫ s in t0..t, A s (y s)) →
        EqOn y x (Icc a b)) ∧
      ContDiffOn ℝ 1 x (Ioo a b) ∧
      (∀ t ∈ Ioo a b, HasDerivAt x (A t (x t)) t) ∧
      HasDerivWithinAt x (A a (x a)) (Ici a) a ∧
      HasDerivWithinAt x (A b (x b)) (Iic b) b ∧
      (∀ y : ℝ → EuclideanSpace ℝ (Fin n),
        ContinuousOn y (Icc a b) →
        (∀ t ∈ Ioo a b, HasDerivAt y (A t (y t)) t) →
        HasDerivWithinAt y (A a (y a)) (Ici a) a →
        HasDerivWithinAt y (A b (y b)) (Iic b) b →
        y t0 = x0 → EqOn y x (Icc a b)) ∧
      (∀ (U : Set ℝ)
        (B : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        IsOpen U → Icc a b ⊆ U → ContDiffOn ℝ ∞ B U → EqOn B A (Icc a b) →
        ∃ (V : Set ℝ) (y : ℝ → EuclideanSpace ℝ (Fin n)),
          IsOpen V ∧ Icc a b ⊆ V ∧ V ⊆ U ∧ ContDiffOn ℝ ∞ y V ∧ EqOn y x (Icc a b)) := by
  obtain ⟨x, hx, heq, hd⟩ := compact_integral_solution hab.le ht0 A hA x0
  have hx0 : x t0 = x0 := by simpa using heq t0 ht0
  have hx' : ∀ t ∈ Ioo a b, HasDerivAt x (A t (x t)) t :=
    fun t ht ↦ hd t (Ioo_subset_Icc_self ht)
  have hxa := (hd a ⟨le_rfl, hab.le⟩).hasDerivWithinAt (s := Ici a)
  have hxb := (hd b ⟨hab.le, le_rfl⟩).hasDerivWithinAt (s := Iic b)
  have huniq (y : ℝ → EuclideanSpace ℝ (Fin n)) (hy : ContinuousOn y (Icc a b))
      (hy' : ∀ t ∈ Ioo a b, HasDerivAt y (A t (y t)) t)
      (hya : HasDerivWithinAt y (A a (y a)) (Ici a) a)
      (hyb : HasDerivWithinAt y (A b (y b)) (Iic b) b)
      (hy0 : y t0 = x0) : EqOn y x (Icc a b) :=
    linear_ode_unique hab ht0 A hA x y hx.continuousOn hy hx' hy' hxa hya hxb hyb
      (hy0.trans hx0.symm)
  refine ⟨x, hx.continuousOn, heq, ?_,
    solution_contDiff_one A (hA.mono Ioo_subset_Icc_self) hx.continuousOn hx',
    hx', hxa, hxb, huniq, ?_⟩
  · intro y hy heqy
    obtain ⟨hy', hya, hyb⟩ := integral_solution_deriv hab ht0 A hA x0 y hy heqy
    exact huniq y hy hy' hya hyb (by simpa using heqy t0 ht0)
  · intro U B hU hsub hB hBA
    -- Enlarge the closed interval inside the given smooth coefficient neighborhood.
    obtain ⟨l, r, ⟨hla, har⟩, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hU.mem_nhds (hsub ⟨le_rfl, hab.le⟩))
    obtain ⟨l', r', ⟨hlb, hbr⟩, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hU.mem_nhds (hsub ⟨hab.le, le_rfl⟩))
    let a' := (l + a) / 2
    let b' := (b + r') / 2
    have hla' : l < a' := by dsimp [a']; linarith
    have ha'a : a' < a := by dsimp [a']; linarith
    have hbb' : b < b' := by dsimp [b']; linarith
    have hb'r : b' < r' := by dsimp [b']; linarith
    have ha'b' : a' < b' := ha'a.trans (hab.trans hbb')
    have hlarge : Icc a' b' ⊆ U := by
      intro t ht
      by_cases hta : t ≤ a
      · exact hleft ⟨hla'.trans_le ht.1, hta.trans_lt har⟩
      by_cases hbt : b ≤ t
      · exact hright ⟨hlb.trans_le hbt, ht.2.trans_lt hb'r⟩
      exact hsub ⟨(not_le.mp hta).le, (not_le.mp hbt).le⟩
    have hsmall : Icc a b ⊆ Icc a' b' := Icc_subset_Icc ha'a.le hbb'.le
    obtain ⟨y, hy, heqy, hdy⟩ := compact_integral_solution ha'b'.le (hsmall ht0) B
      (hB.continuousOn.mono hlarge) x0
    have hy0 : y t0 = x0 := by simpa using heqy t0 (hsmall ht0)
    have hdsmall : ∀ t ∈ Icc a b, HasDerivAt y (A t (y t)) t := by
      intro t ht
      simpa only [hBA ht] using hdy t (hsmall ht)
    refine ⟨Ioo a' b', y, isOpen_Ioo, ?_, Ioo_subset_Icc_self.trans hlarge,
      solution_contDiff_infty B (hB.mono (Ioo_subset_Icc_self.trans hlarge)) hy.continuousOn
        (fun t ht ↦ hdy t (Ioo_subset_Icc_self ht)), ?_⟩
    · intro t ht
      exact ⟨ha'a.trans_le ht.1, ht.2.trans_lt hbb'⟩
    · exact huniq y hy.continuousOn (fun t ht ↦ hdsmall t (Ioo_subset_Icc_self ht))
        (hdsmall a ⟨le_rfl, hab.le⟩).hasDerivWithinAt
        (hdsmall b ⟨hab.le, le_rfl⟩).hasDerivWithinAt hy0

end HolomorphicAnosov
