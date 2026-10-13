import HolomorphicAnosov.Analysis.Regularity.ApproximationFirstJetHasFDerivAt
import HolomorphicAnosov.Analysis.Regularity.ApproximationFirstJetComparison
import HolomorphicAnosov.Analysis.Regularity.ApproximationContinuousFDerivAt
import HolomorphicAnosov.Analysis.Regularity.ApproximationCoordinateDerivativeError
import HolomorphicAnosov.Analysis.Regularity.ApproximationCoordinateDerivativeHypothesis
import HolomorphicAnosov.Analysis.Regularity.ApproximationDegreeZeroLocalBound
import HolomorphicAnosov.Analysis.Regularity.ApproximationContDiffOn
import HolomorphicAnosov.Analysis.Regularity.ApproximationIteratedFDerivLocalBound
import HolomorphicAnosov.Analysis.Regularity.PolynomialBallDerivativeEstimate
import HolomorphicAnosov.Analysis.Regularity.ApproximationPolynomialDifferenceBound
import HolomorphicAnosov.Analysis.Regularity.ApproximationPolynomialJetComparison
import HolomorphicAnosov.Analysis.Regularity.ApproximationRemainderFDerivAt
import HolomorphicAnosov.Analysis.Regularity.PolynomialFirstJet
import HolomorphicAnosov.Analysis.Regularity.PolynomialFirstJetSingle
import HolomorphicAnosov.Analysis.Regularity.PolynomialTranslateDerivatives
import HolomorphicAnosov.Analysis.Regularity.HolderOnWithNormBound
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualCoordinate
import HolomorphicAnosov.Analysis.Regularity.EuclideanDualNorm
import HolomorphicAnosov.Analysis.Regularity.IteratedFDerivSuccDifferenceBound
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Campanato regularity from uniform local polynomial approximation

Source: Campanato, Proprietà di una famiglia di spazi funzionali (1964), §§2–6,
printed pp.140–156, especially Theorem [6.I] p.156; Journé, A regularity lemma for
functions of several variables (1988), printed pp.187 and 192.

DAG node: analysis.campanato_uniform_polynomial_approximation_regularity.
The formal proof below is an agent-written direct induction on the degree of the
supplied pointwise approximants, using the separately stated polynomial-ball estimate.
It is not the source's minimizing-polynomial construction reproduced in the main
docstring. The imported polynomial-ball theorem still carries an admitted proof;
therefore this module's completed local proof is not an axiom-free project result.
-/

namespace HolomorphicAnosov

open Filter
open scoped Topology _root_.Topology

/-- Uniform local polynomial approximation implies regularity of the original function.

The ambient function `h` represents its restriction to the open set `Ω`; no hypothesis
or conclusion concerns its values outside `Ω`. Each center has one polynomial that
works at every point of the same common-radius ball. The degree bound is total degree,
not a coordinatewise degree bound. On the open domain, `ContDiffOn` states classical
continuous differentiability through order `n`, and `iteratedFDeriv` is the actual
unrestricted derivative of this same pointwise function. Its local Hölder estimate is
in the continuous multilinear operator norm. This is equivalent in finite Euclidean
dimension to the local Hölder condition on all order-`n` classical partial derivatives.
The positivity hypotheses ensure that the exponent `α.toNNReal` has real value `α`.

Source: Campanato §§2–6, printed pp.140–156, specialized to q=2, k=h=n,
λ=N+2(n+α), interior balls; Journé printed pp.187,192.

Implemented proof (agent-written): the polynomial-ball estimate controls the first
jet difference of two approximants on an overlap ball. The pointwise remainder at a
center is little-o of distance, so its first derivative vanishes. Consequently each
actual coordinate derivative admits the differentiated polynomial approximation,
with total degree and approximation exponent both reduced by exactly one. Induct on
the degree. Finite coordinate reconstruction and the open-domain successor criterion
give C^n regularity. Degree zero gives a local Hölder bound directly; in the successor
step, intersect the finitely many coordinate neighborhoods and add their constants.
The iterated-derivative currying isometry and evaluation by unit coordinate vectors
bound the original multilinear operator norm by this sum. This proves the original
pointwise conclusion, without an added premise or a choice of representative.

The following natural-language proof from the DAG is the alternative published
minimizer route. It is retained as source context, not as a description of the
implemented direct induction:

P1. If Ω=∅ the conclusion is vacuous. Fix a₀∈Ω and V,C,r,P_a as in the statement. Since a∈B(a,r)⊆Ω
for each a∈V, V⊆Ω. Choose R>0 with 4R<r and closedBall(a₀,4R)⊆V; let G=B(a₀,R) and u=h|G. The closed
ball is compact in finite-dimensional Euclidean space, so continuity gives a finite H≥0 with |h|≤H
on closedBall(a₀,4R). In particular u and u² are integrable on G and ∫G|u|²<∞; the compact
integrability leaf applies to h and h² on the closed ball and restriction to the measurable subset G
preserves integrability. This fixes one bounded connected ball, one common error constant and one
common radius. No boundary smoothness of Ω is assumed.

P2. Verify the exact hypotheses of Campanato’s space rather than insert a regularity hypothesis. For
a∈closure G and 0<ρ≤diam G=2R set t=ρ/(2R) and b=(1−t)a+t a₀. Then |b−a₀|≤R−ρ/2 and |b−a|≤ρ/2, so
B(b,ρ/4)⊆G∩B(a,ρ). Therefore |G∩B(a,ρ)|≥ω_N(ρ/4)^N, where ω_N=|B(0,1)| is finite and strictly
positive. Translation and the dilation z↦b+(ρ/4)z give this volume by the Jacobian formula;
bounded-ball finiteness and open-set positivity justify the finite positive normalizations. This is
property (I), printed p.138. Since a∈closure G⊆V and ρ≤2R<r, the original P_a gives
∫_{G∩B(a,ρ)}|u−P_a|²≤C²ρ^{2(n+α)}|B(a,ρ)|=C²ω_Nρ^λ with λ=N+2(n+α). The Jacobian formula also gives
|B(a,ρ)|=ω_Nρ^N. Thus sup_{a∈closure G,0<ρ≤2R}ρ^(−λ) inf_{deg P≤n}∫_{G∩B(a,ρ)}|u−P|²≤M², with
M=C√ω_N. Along with u∈L²(G), this is precisely definition (1.6), q=2,k=n. All radii in that
definition are covered because the localization chose 2R<r; there is no unproved large-radius case.
Theorem [6.I] p.156 has 0≤h≤k and N+hq<λ<N+(h+1)q: set h=k=n to obtain N+2n<λ<N+2(n+1) and output
exponent α. The degree-reduction lemma of §6 is the identity when k=h, so the proof needed is the
printed §§3–5 proof of [5.I].

P3. Here is Campanato’s minimizing-polynomial construction (3.1)–(3.2), pp.143–144, on the interior
balls needed for the local conclusion. For a∈G and 0<ρ<dist(a,∂G), minimize F(P)=∫_{B(a,ρ)}|u−P|²
over the finite-dimensional space of total degree≤n polynomials. Write P(x)=Σ_{|β|≤n}a_β(x−a)^β/β!,
so a_β=D^βP(a). On this fixed ball h and every monomial are bounded and integrable; expanding the
square expresses F as a finite quadratic polynomial in the coefficients with finite real integral
coefficients. Hence F is continuous. The polynomial-ball estimate bounds every a_β by a fixed
constant times ||P||_{L²(B(a,ρ))}; summing the finitely many squared coefficient bounds yields
||coeff P||≤A_{a,ρ}||P||₂. The L² triangle inequality gives ||u−P||₂≥||P||₂−||u||₂. To see this
inequality with no norm-equivalence assumption, expand ||f+g||₂² and bound the cross integral by
Cauchy–Schwarz (the p=q=2 Holder leaf); taking square roots gives the triangle inequality. Thus
F(P)→∞ as the Euclidean coefficient norm tends to infinity. Choose a coefficient closed ball
containing zero outside which F>F(0)+1; compactness and the minimum leaf give a global minimizer. It
is unique: F((P+Q)/2)=(F(P)+F(Q))/2−(1/4)∫|P−Q|², so two minimizers have zero difference L² norm;
the polynomial estimate forces all its coefficients to be zero. Denote the minimizer by Q_{a,ρ}, its
coefficients a_β(a,ρ). Its residual obeys ∫_{B(a,ρ)}|u−Q_{a,ρ}|²≤M²ρ^λ by P2. The original fixed P_a
only supplies this bound; it is not used as the limiting polynomial.

P4. Work on U=B(a₀,R/2) with common ρ₀=R/8; all B(a,2ρ₀), a∈U, lie in G. For 0<ρ≤ρ₀, on B(a,ρ/2) the
inequality |Q_{a,ρ}−Q_{a,ρ/2}|²≤2|Q_{a,ρ}−u|²+2|u−Q_{a,ρ/2}|² gives
∫|Q_{a,ρ}−Q_{a,ρ/2}|²≤2M²(ρ^λ+(ρ/2)^λ). Apply the derivative estimate on B(a,ρ/2): for |β|≤n,
|a_β(a,ρ)−a_β(a,ρ/2)|≤A M ρ^{s−|β|}, where s=n+α and A depends only on N,n,α. This is the q=2
interior-ball version of Lemmas [3.I],[3.III], pp.144–146. It uses integrals over the smaller common
ball, never the sup norm of u−Q. Since θ_β=s−|β|≥α>0, summing over ρ_j=2^(−j)ρ₀ gives
|a_β(a,ρ_i)−a_β(a,ρ_j)|≤A M ρ_i^{θ_β}/(1−2^(−θ_β)) for j>i, uniformly in a∈U. Completeness of ℝ
gives limits v_β(a) and |a_β(a,ρ_j)−v_β(a)|≤A_β Mρ_j^{θ_β}.

P5. These limits are independent of scale and the convergence holds for every positive radius, as in
Lemma [3.IV], (3.10)–(3.15), pp.146–148. Given 0<ρ≤ρ₀, choose j with ρ_j/2<ρ≤ρ_j. Compare Q_{a,ρ}
and Q_{a,ρ_j} on B(a,ρ), whose radius is at least ρ_j/2. The same two-residual inequality gives its
difference L² norm≤A Mρ_j^{λ/2}, and the polynomial estimate at a gives |a_β(a,ρ)−a_β(a,ρ_j)|≤A
Mρ_j^{θ_β}≤A′Mρ^{θ_β}. Combine with P4 to obtain |a_β(a,ρ)−v_β(a)|≤L_β Mρ^{θ_β}, uniformly for a∈U.
This also proves that a different starting radius gives the same limit. The coefficients and limits
are uniformly bounded on U: the competitor zero gives ||u−Q_{a,ρ₀}||₂≤||u||₂ on the ball, so
||Q_{a,ρ₀}||₂≤2H√ω_Nρ₀^{N/2}; the polynomial estimate bounds every a_β(a,ρ₀), and P4 bounds its
distance to v_β(a). No continuity of a↦Q_{a,ρ} is assumed.

P6. For a,b∈U and d=|b−a| with 0<2d≤ρ₀, the ball B(a,d) lies in B(a,2d)∩B(b,2d). Comparing
Q_{a,2d},Q_{b,2d} there gives ∫_{B(a,d)}|Q_{b,2d}−Q_{a,2d}|²≤A M²d^λ. Consequently
|D^β(Q_{b,2d}−Q_{a,2d})(a)|≤A_β M d^{s−|β|}. For |β|=n, the derivative of any degree≤n polynomial is
constant, so this is |a_β(b,2d)−a_β(a,2d)|≤A_β M d^α. The two coefficient-limit errors from P5
therefore give |v_β(b)−v_β(a)|≤L M d^α. This is precisely Lemma [3.II] p.145 and Theorem [4.I]
pp.148–149, specialized locally. On W=B(a₀,ρ₀/8), all pairs have 2d<ρ₀, so this is one Hölder
constant for all pairs in W. Equality handles a=b without a radius-zero estimate. For all a∈U it
proves local continuity of the top-order v_β; no uniform polygon bound for arbitrary connected
domains is invoked.

P7. Follow the printed downward induction of Theorem [4.II], pp.149–151, rather than differentiate
an unproved limiting jet. Suppose all v_γ with |γ|>|β| are continuous, where |β|≤n−1. Fix a∈U, a
coordinate i, a signed nonzero ε small enough that b=a+εe_i∈U and ρ=2|ε|≤ρ₀. Set T=Q_{b,ρ}−Q_{a,ρ}.
Exact finite polynomial Taylor expansion about b gives
a_β(b,ρ)−a_β(a,ρ)=D^βT(a)−Σ_{j=1}^{n−|β|}((-ε)^j/j!)a_{β+je_i}(b,ρ). Divide by ε. By the general-β
comparison in P6, D^βT(a)/ε=O(M|ε|^{s−|β|−1})→0. By P5, replacing either a_β endpoint by v_β changes
this quotient by the same order, because |ε|^(s−|β|−1)→0. The j=1 term has sign + and tends to
v_{β+e_i}(a): its coefficient-limit error tends to zero and that higher coefficient function is
continuous. Every j≥2 term tends to zero, since its coefficients are uniformly bounded by P5 and
|ε|^{j−1}→0. Thus the signed difference quotient [v_β(a+εe_i)−v_β(a)]/ε tends to v_{β+e_i}(a). The
real slope criterion proves ∂_i v_β(a)=v_{β+e_i}(a), for every i and every a∈U. The strict exponent
needed here is s−|β|−1≥α>0. This is the content of (4.7)–(4.12); the estimate concerns minimizing
polynomials on an overlap ball and does not assume the conclusion C¹.

P8. Make explicit the elementary continuous-partials conclusion used in the source’s induction. The
partial derivatives just proved are the continuous higher functions v_{β+e_i}. On a small closed
coordinate box around a contained in U they are bounded. Join a to a+s by the N coordinate segments
in the box. Each restricted one-variable function has the derivative given in P7 throughout the
segment, including endpoints; the mean-value bound shows |v_β(a+s)−v_β(a)|≤BΣ_i|s_i|, so v_β is
continuous. Apply the mean-value bound once more to each coordinate segment after subtracting the
linear function of slope v_{β+e_i}(a). Its derivative is v_{β+e_i}(z)−v_{β+e_i}(a), uniformly
tending to zero as the box shrinks by higher-function continuity. Summing gives |v_β(a+s)−v_β(a)−Σ_i
v_{β+e_i}(a)s_i|≤Σ_i|s_i|ω_a(|s|)≤√N|s|ω_a(|s|), with ω_a(t)→0. The little-o/Fréchet criterion
identifies its derivative with L_β(a)s=Σ_i v_{β+e_i}(a)s_i; the entries are continuous, hence so is
this derivative. At the top order P6 starts the induction; P7 and this argument successively yield
all lower functions continuous with these derivatives, down to v₀.

P9. Theorem [4.III] p.152 now follows without a formal jet assumption: induction on the order of
coordinate differentiation gives D^βv₀=v_β for |β|≤n. All these classical derivatives are continuous
by P6–P8. For the equivalent finite-dimensional Fréchet convention collect v_{e_{i₁}+…+e_{i_k}} as
the finitely many coordinate entries of the k-linear derivative, differentiate those entries using
P8 and the Pi derivative leaf, and expand arbitrary vectors on the coordinate bases; this proves the
iterated Fréchet derivatives through order n. For |β|=n, P6 supplies an α-Hölder bound on W. Finite
coordinate expansion of an n-linear map bounds its operator norm by the sum of the absolute values
of its at most N^n entries, so the top Fréchet derivative is also locally α-Hölder. Thus v₀ is
locally C^{n,α} on U, with an α-Hölder bound on W.

P10. Identify the representative by the actual printed §5 argument, Theorem [5.I] pp.152–154, rather
than the old pointwise identity P_a(a)=h(a). Extend u by zero outside G, obtaining f on ℝᴺ. Both f
and f² are integrable: h and h² are integrable on the compact closed ball and bounded there, and
their indicators on the measurable G are integrable; the indicator integral identifies the
restricted integrals. Hence both are locally integrable. Canonical Euclidean volume is additive
Haar, locally finite and has the Borel structure; finite-dimensional Haar doubling supplies uniform
local doubling. Euclidean space is second-countable and Real is a complete real normed target. Apply
the average differentiation leaf separately to f and f², with centers constantly a and positive
radii ρ→0 (K=1). Intersect the two full-measure sets. Open and closed balls differ by a sphere of
zero volume since N≥1, so the same averages converge on open balls. For almost every a∈G and all
sufficiently small ρ the balls lie in G; therefore avg_{B(a,ρ)}u→u(a) and avg_{B(a,ρ)}u²→u(a)².
Expanding the square and using integral linearity gives avg_{B(a,ρ)}|u−u(a)|²=avg u²−2u(a)avg
u+u(a)²→0. This is exactly the q=2 Lebesgue-point assertion (5.2). A countable sequence is
unnecessary: the leaf supplies the full positive-radius limit.

P11. At any such Lebesgue point a∈U use the source’s three-term inequality (5.3), p.153:
|a₀(a,ρ)−u(a)|²≤3 avg_{B(a,ρ)}(|Q_{a,ρ}−a₀(a,ρ)|²+|Q_{a,ρ}−u|²+|u−u(a)|²). Here a₀ denotes the
coefficient for the zero multi-index, not the neighborhood’s center. The second average is
≤(M²/ω_N)ρ^{λ−N}→0 because λ−N=2s>0. For the first average expand
Q_{a,ρ}−a₀(a,ρ)=Σ_{1≤|β|≤n}a_β(a,ρ)(x−a)^β/β!. The square of a sum of m terms is ≤m times the sum of
squares, each |(x−a)^β|≤ρ^{|β|}, and every a_β(a,ρ) is bounded as ρ→0 by P5. Thus that average is at
most a finite constant times Σ_{1≤|β|≤n}ρ^{2|β|}→0. The third average tends to zero by P10. Hence
a₀(a,ρ)→u(a); P5 gives the same limit v₀(a), so v₀=u almost everywhere on U. This proves the
representative assertion by minimizing-polynomial residuals and Lebesgue differentiation, as in
(5.2)–(5.4). No uniqueness of the originally supplied P_a or fixed-polynomial jet is used.

P12. Finally h|U and v₀ are both continuous. If h(a)−v₀(a)≠0 at a∈U, continuity gives a nonempty
open ball in U on which this difference stays bounded away from zero. Its positive Lebesgue measure
contradicts P11’s almost-everywhere equality. Therefore h=v₀ at every point of U, and P9 proves the
exact original pointwise function locally C^{n,α} near a₀. Repeat for arbitrary a₀∈Ω. On overlaps
the resulting derivatives are the classical derivatives of the same pointwise h and so agree,
without any representative-choice or polynomial-choice hypothesis. This finishes the Campanato
specialization cited by Journé, with the exact original statement unchanged.

The empty open domain is vacuous. In dimension N=1 the same argument applies.
For n=1 the higher-power sum in the coefficient differentiation is empty. No endpoint
α=0 or α=1, global Hölder constant, boundary extension, connectedness assumption on Ω,
or change to an almost-everywhere representative is asserted.
-/
theorem campanato_uniform_polynomial_approximation_regularity
    {N n : ℕ} (hN : 1 ≤ N) (_hn : 1 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin N))} (hΩ : IsOpen Ω)
    {α : ℝ} (hαpos : 0 < α) (_hαlt : α < 1)
    (h : EuclideanSpace ℝ (Fin N) → ℝ) (hh : ContinuousOn h Ω)
    (happrox : ∀ a₀ ∈ Ω,
      ∃ V : Set (EuclideanSpace ℝ (Fin N)), IsOpen V ∧ a₀ ∈ V ∧
        ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧
          ∀ a ∈ V, ∃ P : MvPolynomial (Fin N) ℝ,
            P.totalDegree ≤ n ∧ Metric.ball a r ⊆ Ω ∧
              ∀ y ∈ Metric.ball a r,
                |h y - MvPolynomial.eval (fun i ↦ y i) P| ≤
                  C * ‖y - a‖ ^ ((n : ℝ) + α)) :
    ContDiffOn ℝ (n : WithTop ℕ∞) h Ω ∧
      ∀ a₀ ∈ Ω, ∃ V : Set (EuclideanSpace ℝ (Fin N)),
        IsOpen V ∧ a₀ ∈ V ∧ V ⊆ Ω ∧
          ∃ K : NNReal, HolderOnWith K α.toNNReal (iteratedFDeriv ℝ n h) V := by
  refine ⟨approximation_contDiffOn hN hΩ hαpos h hh happrox, ?_⟩
  intro a₀ ha₀
  obtain ⟨V, hV, haV, hVΩ, C, hC, hbound⟩ :=
    approximation_iteratedFDeriv_local_bound hN hΩ hαpos h hh happrox a₀ ha₀
  refine ⟨V, hV, haV, hVΩ, ⟨C, hC⟩, ?_⟩
  apply holderOnWith_of_norm_bound
  intro a ha b hb
  change ‖iteratedFDeriv ℝ n h a - iteratedFDeriv ℝ n h b‖ ≤
    C * ‖a - b‖ ^ (α.toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hαpos.le]
  exact hbound a ha b hb



end HolomorphicAnosov
