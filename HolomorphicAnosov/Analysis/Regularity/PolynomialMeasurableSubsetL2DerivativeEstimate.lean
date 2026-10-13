import HolomorphicAnosov.Analysis.Regularity.EuclideanPolynomialMixedPartial
import HolomorphicAnosov.Analysis.Regularity.PolynomialCoefficientCompactModel
import HolomorphicAnosov.Analysis.Regularity.PolynomialUnitSphereSubsetL2LowerBoundG3
import HolomorphicAnosov.Analysis.Regularity.PolynomialAffineMixedPartialIdentityG3
import HolomorphicAnosov.Analysis.Regularity.CampanatoMeasurableSubsetCompositionG3
import HolomorphicAnosov.Analysis.Measure.AnalyticZeroSetNull
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Campanato (1964), Lemma [2.I], printed pp.140–143, q=2 integral estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HolomorphicAnosov.Analysis.Regularity

/-- Campanato's q = 2 measurable-subset L² derivative estimate.

Source: S. Campanato, Proprietà di una famiglia di spazi funzionali, Annali della Scuola Normale
Superiore di Pisa, Classe di Scienze, serie3,18(1)(1964),137–160, Lemma[2.I] printed140–143;
literature/campanato-functional-spaces-1964.pdf PDF5–8. This is the q=2 measurable-subset
specialization of the printed theorem, following the actual coefficient-sphere/admissible-weight
minimization(2.3)–(2.11) and affine scaling(2.12).

`NullMeasurableSet E volume` expresses classical Lebesgue measurability, including completed-only
sets. The finite-volume and integrability helper ensures that the displayed real volume and
integral are genuine finite quantities. The centre is not required to belong to E. A single K
works for all polynomials, centres, radii, measurable subsets, and derivative orders.

Natural-language proof (the source-backed DAG proof E1–E7):

E1. Fix N≥1,n≥0 and A∈(0,v_N]. Let B=B(0,1) in the original Euclidean space ℝ^N. Write
P_c(y)=Σ_{|γ|≤n}c_γ y^γ and let S={c:Σc_γ²=1}. The constant coefficient shows S is nonempty. The
original finite coefficient Euclidean space is proper; continuity of the coefficient norm makes S
closed inside its compact closed unit ball, hence compact. A convergent sequence of coefficients
gives uniform convergence of the associated polynomials on every compact subset, by their finite
monomial expansion. This is Campanato(2.3) and the polynomial subsequence argument on p141.

E2. Use the printed admissible-weight class F_A of measurable real functions f with f=0 almost
everywhere outside B, 0≤f≤1 almost everywhere and ∫_B f≥A. It is nonempty: the indicator of B is
admissible. Work with the SAME restricted measure μ=volume.restrict B and the real space H=Lp ℝ 2 μ;
restriction identifies these weights with their μ-almost-everywhere classes, while zero extension
returns to the printed whole-space model. B is measurable and bounded, so μ(univ)=volume(B)<∞ and
isFiniteMeasure_restrict supplies the finite-measure instance. Measurable bounded f is
AEStronglyMeasurable, and MemLp.of_bound with bound1 packages it as h_f in H. Lp.norm_toLp and the
p=2 eLpNorm integral formula give ‖h_f‖²=∫_B|f|²≤v_N, hence ‖h_f‖≤sqrt(v_N). No norm on a finite
coefficient array is identified with this L² norm. Polynomials and their squares are continuous and
bounded on the compact closed unit ball and integrable there, and their integrals on B are obtained
by restriction. For c∈S and f∈F_A put J(c,f)=∫_B|P_c|²f and γ(A)=inf_{S×F_A}J. These integrals are
finite and nonnegative. This is the actual q=2 version of Campanato(2.4)–(2.6), with the finite
restricted-measure model made explicit; measurable representatives and their zero extensions are
taken only up to the corresponding almost-everywhere equality.

E3. Choose a minimizing sequence (c_j,f_j) with γ(A)≤J(c_j,f_j)<γ(A)+1/(j+1). Compactness of S gives
a coefficient-convergent subsequence c_j→c_*∈S. For that SAME subsequence let h_j be the L² classes
from E2, in H=Lp ℝ 2 (volume.restrict B). The original finite Euclidean Borel measurable space is
countably generated (a countable rational-coordinate box basis generates its open sets), and μ is
finite, hence s-finite. Apply measure_isSeparable_of_countablyGenerated_sFinite to this actual μ.
With p=2, the facts 1≤2 and 2≠∞, and separability of ℝ, lp_secondCountableTopology gives
SecondCountableTopology H; the existing second-countable-to-separable instance gives SeparableSpace
H. The actual Lp completeness instance, using CompleteSpace ℝ and 1≤2, and L2.innerProductSpace give
a complete real Hilbert space with its ORIGINAL L² norm and integral inner product. These canonical
Euclidean Borel/finite-measure instance binders must be instantiated on this μ; no separability of
an arbitrary measure is presumed.

Let R=InnerProductSpace.toDual ℝ H. This real linear isometric equivalence sends h_j to the
continuous functional y↦⟪h_j,y⟫. Since ‖h_j‖≤sqrt(v_N), all R(h_j) lie in the strong-dual closed
ball about0 of that radius. View these same functionals in WeakDual ℝ H. The real scalar field is
proper, and WeakDual.isSeqCompact_closedBall applies because H is separable. It supplies a further
strictly increasing subsequence converging in the weak-star topology to φ whose strong-dual
counterpart remains in that ball. Define h_*=R.symm(WeakDual.toStrongDual φ). For every fixed y∈H,
WeakDual.eval_continuous gives ⟪h_j,y⟫→⟪h_*,y⟫ along this further subsequence. Coefficient
convergence survives that subsequence. This is an actual Riesz/weak-dual-ball realization of the
bounded-L² weak-subsequence step asserted on printedp141; finite-dimensional coefficient compactness
alone is not used for the L² sequence.

To retain the admissible bounds use the stronger ALL-L² tests available from this Mathlib binding,
rather than claim a smooth-test density theorem. For each measurable s with μ(s)<∞, the actual
indicatorConstLp 2 s 1 lies in H. The Riesz evaluation has order ⟪h_j,1_s⟫; REAL inner-product
symmetry changes it to ⟪1_s,h_j⟫, to which L2.inner_indicatorConstLp_one applies. Thus ∫_s f_j
dμ→∫_s h_* dμ. The original 0≤f_j≤1 implies 0≤∫_s f_j≤μ.real(s), so both inequalities pass to the
real limit. integrableOn_Lp_of_measure_ne_top at univ makes the representative of h_* integrable for
finite μ; constants0 and1 are integrable as well. Apply ae_le_of_forall_setIntegral_le first to
(0,h_*) and then to (h_*,1), obtaining 0≤h_*≤1 μ-almost everywhere. Take s=univ to pass ∫f_j≥A to
∫h_*≥A. Choose a measurable representative of this L² class and extend it by0 outside B;
restricted-measure almost-everywhere equality gives a member f_* of the printed admissible class.
This replaces the support/positivity conclusion of footnote6 by exact generic
indicator/integral-detection APIs on the same weights. The source itself uses smooth
supported/nonnegative tests; no unprinted smooth-test approximation or new Hilbert compactness
theorem is asserted here.

E4. For the coefficient and weight limits supplied by E3, finite coefficient convergence gives
uniform convergence |P_cj|²→|P_c*|² on the closed unit ball. Split the difference of J(c_j,f_j) and
J(c_*,f_*) as ∫_B(|P_cj|²−|P_c*|²)f_j plus ∫_B|P_c*|²(f_j−f_*). The first tends to0 since 0≤f_j≤1
and its absolute value is at most v_N times the uniform error. For the second use the fixed actual
test w(y)=|P_c*(y)|² in H=Lp ℝ 2 μ, μ=volume.restrict B. This function is bounded and measurable on
that finite measure, so MemLp.of_bound supplies its L² class. E3's weak evaluations against w and
L2.inner_def identify its pairings with the actual integrals ∫_B|P_c*|²f_j and ∫_B|P_c*|²f_*. They
converge, making the second term tend to0. The test is the restricted-ball L² function; in the
printed whole-space model it is its zero extension 1_B|P_c*|², never the uncut polynomial on all
ℝ^N. Therefore γ(A)=J(c_*,f_*) is attained, exactly Campanato(2.7)–(2.8) and p142's displayed limit.
Actual finite coefficient, representative and real-inner-product integral identities refer to these
SAME functions and μ.

E5. Campanato next states γ(A)>0 on p142. Bind its nonzero-polynomial zero-set step to the actual
source theorem analysis.mityagin_real_analytic_zero_set_null_g6, from Mityagin’s obtained author
preprint arXiv:1512.07276v1 (22 December 2015), Proposition0 and Claims1–2 pp1–3. Form the original
formal polynomial p_c*=Σ_{|γ|≤n}C(c_*γ)X^γ in MvPolynomial (Fin N) ℝ. Its finite evaluation equals
P_c* by mvPolynomial_eval_eq. The actual Euclidean coordinate projections are real linear maps and
continuous by finite-dimensional continuity, hence are continuous linear maps f_i:E→L[ℝ]ℝ on the
ORIGINAL Euclidean norm. analyticOnNhd_eval_continuousLinearMap gives real analyticity of x↦eval(f_i
x)p_c* on all of E, without imposing a Pi supremum norm. The canonical EuclideanSpace.equiv
identifies coordinate assignments bijectively, with the original Euclidean model retained. If P_c*
were zero everywhere, use mvPolynomial_funext_set with all side sets Ioo(−1,1), infinite by
set_Ioo_infinite, to obtain p_c*=0. Equality of its original monomial coefficients would then force
every c_*γ=0, contrary to c_*∈S. Thus P_c* is nonzero at some point. The whole Euclidean space is
open and connected, so the Mityagin theorem applies and gives its zero set Lebesgue-null. This
invoked author-preprint source theorem is complete at its own SOURCE/API level, with native analytic
finite-order, true derivative, ordered classical-partial and one-ball Taylor bindings supplied in
its M3–M4 decomposition; this application does not verify their native formal realization or
transitive/kernel completion. Its M2 binds regular chart nullity to the same-E proper-submodule and
differentiable-null-image sources, while M3–M4 supply the analytic certificates; their lower
formal/API implementation remains the responsibility of those inputs, not this caller.

Using the named zero-set-null conclusion, |P_c*|²>0 almost everywhere. If J(c_*,f_*)=0,
nonnegativity forces f_*=0 almost everywhere outside the null zero set, contradicting ∫f_*≥A>0. This
proves γ(A)>0 at this node relative to the named, own-level-complete Mityagin source theorem;
verification of its lower native/formal inputs is not supplied by this positive-minimum application.
E6–E7 explicitly give the finite formal-coefficient and classical mixed-derivative/Taylor
identities; their future formal implementation must retain the stated polynomial, coefficients,
variables and derivative notion. Vanishing on an open box supplies the nontrivial-function premise
only, and is not substituted for zero-set nullity.

E6. For the full classical Lebesgue-measurable set E⊆B with volume(E)≥A, work with the ORIGINAL
Borel additive Haar measure μ on the original Euclidean space. Its completed measurable sets are
represented by NullMeasurableSet E μ; the stated real integral on E is the ordinary integral for
μ.restrict E. The generic null-measurable-set theorem supplies a Borel-measurable B₀⊆E with B₀=E
μ-almost everywhere. Hence B₀ remains inside the SAME unit ball. measure_congr_ae gives μ(B₀)=μ(E),
and measure_restrict_congr_set gives μ.restrict B₀=μ.restrict E, so all real masses and all
restricted polynomial integrals coincide. Take the indicator of this BOREL B₀ as the admissible
weight in (2.7), as printed footnote 7; it is measurable in the original sigma algebra and has the
same required mass. No measurability of the completed-only E indicator in the original Borel sigma
algebra is assumed. The coefficient inequality for B₀ therefore gives precisely the original E
integral inequality below. Thus every coefficient-unit polynomial has ∫_E|P|²≥γ(A). For a nonzero
coefficient vector c apply this to c/‖c‖₂: ∫_E|P_c|²≥γ(A)Σ|c_γ|². Consequently each
|c_β|≤γ(A)^(-1/2)(∫_E|P_c|²)^(1/2), the q=2 version of(2.11). The zero polynomial is immediate. For
the derivative-coefficient calculation use the fixed original Euclidean coordinate functions,
without changing their Euclidean norm. Let I={γ∈ℕ^N:|γ|≤n}, a finite set containing the zero
multi-index, and write P_c(x)=∑_{γ∈I}c_γ∏_j x_j^{γ_j}. For a fixed coordinate j hold all other
coordinates constant and differentiate its REAL scalar variable β_j times. Each scalar monomial
power is smooth, so it satisfies the ContDiffAt Real β_j premise of iteratedDeriv_fun_sum and
iteratedDeriv_const_mul at every real point. These exact APIs pass the derivative through the finite
sum and the constant factors. The power formula iteratedDeriv_pow yields (γ_j.descFactorial
β_j)x_j^{γ_j−β_j}; when β_j>γ_j the descending factorial is zero and the entire term is zero,
despite truncated exponent subtraction. Apply this calculation successively to the coordinates in
the defining mixed derivative order. For terms with β≤γ coordinatewise it gives
D^βP_c(x)=∑_{γ∈I, β≤γ}c_γ∏_j[(γ_j.descFactorial β_j)x_j^{γ_j−β_j}],
while all terms with some β_j>γ_j vanish. The successive functions remain finite polynomial sums and
hence satisfy the same smoothness premises at every stage; no commutation of nonsmooth derivatives
or alternate Pi-sup state norm is used. At x=0, if γ≠β and β≤γ, some positive exponent gives a zero
factor. The sole surviving term γ=β has each power 0^0=1 and each descending factorial equal to β_j!
by nat_descFactorial_self. Thus D^βP_c(0)=β!c_β exactly. Order β=0 is included, n=0 leaves I={0} and
evaluation of a constant, and the zero polynomial has every derivative zero. Taking the finite
maximum K₀ of the positive numbers β!γ(A)^(-1/2), |β|≤n, gives K₀>0 because the nonempty index set
contains β=0. Combining the normalized coefficient inequality above with this identity gives the
first center estimate uniformly in β. This expands the finite Taylor/coefficient dictionary implicit
in Campanato (2.11)–(2.12), printed pp.142–143; its constant uses the positive minimum proved in E5
relative to the named Mityagin source theorem and its lower analytic obligations.

E7. AFFINE NORMALIZATION ON THE SAME FULL LEBESGUE SET. Let μ be the original Borel additive
Haar/Lebesgue measure on Euc=EuclideanSpace Real (Fin N), and let E⊆B(a,ρ) be the stated classical
Lebesgue-measurable set, represented by NullMeasurableSet E μ. Choose the SAME type of Borel B₀⊆E
with B₀=E μ-almost everywhere using the null-measurable-set theorem. The mass and restricted measure
equalities follow from measure_congr_ae and measure_restrict_congr_set, so this replacement changes
neither the real volume nor any stated polynomial integral and imposes no Borel restriction on the
public theorem.
Set T(y)=a+ρy with ρ>0, S₀=T⁻¹(B₀), E′=T⁻¹(E), and Q(y)=P(T(y)). T is the actual affine
homeomorphism, inverse x↦ρ⁻¹(x−a), so S₀ is Borel and T''S₀=B₀. The Euclidean equality ‖T(y)−a‖=ρ‖y‖
shows S₀⊆B(0,1). To bind the possibly completed-only E′, let H={x:(x∈B₀)≠(x∈E)}; B₀=E almost
everywhere gives μ(H)=0. measure_preimage_add for the translation a+· applies to this ARBITRARY set
H and gives μ({z:a+z∈H})=0. Thus the translated membership predicates are equal μ-almost everywhere.
Scalar multiplication by ρ is QuasiMeasurePreserving on this original finite-dimensional normed
Borel Haar space because ρ≠0. Apply quasiMeasurePreserving_ae_eq_comp with codomain Prop to those
translated predicates. It yields S₀=E′ μ-almost everywhere. Consequently E′ is null measurable,
since it is almost everywhere equal to the Borel S₀, and measure_congr_ae and
measure_restrict_congr_set give their exact masses and restricted integrals equal. No inverse
measurable hull, independent completed-measure target or unsupported preimage-measurability theorem
is used.
Apply the named real change-of-variables theorem ONLY to the BOREL S₀. At EVERY y∈S₀, T has real
derivative ρ·id: T(y+h)−T(y)−ρh=0, so the derivative remainder is identically zero; it is injective
since ρ≠0. The canonical Euclidean finrank theorem gives finrank Real Euc=N on the original
Euclidean norm. linearMap_det_smul and linearMap_det_id therefore give det(DT)=ρ^N and
|det(DT)|=ρ^N>0. First take the constant integrand 1. setIntegral_const identifies the two real
finite masses, and integral_const_mul extracts the positive constant, giving μ.real(B₀)=ρ^N
μ.real(S₀). Then use the REAL integrand g(x)=|P(x)|²: the same theorem and scalar extraction give
∫_{B₀}|P|² dμ=ρ^N ∫_{S₀}|Q|² dμ.
These are actual finite integrals: the polynomial and its square are continuous and bounded on their
encompassing compact closed balls; continuousOn_integrableOn_compact and integrableOn_mono_set
provide integrability on the Borel sets, and equality of restricted measures transfers it to E and
E′. The closed balls are compact in the finite-dimensional proper original model, and their bounded
volumes are finite. Dividing by the positive ρ^N and using the earlier almost-everywhere set
identifications yields exactly
volume(E′)=ρ^(−N)volume(E)≥A,  ∫_{E′}|Q|²=ρ^(−N)∫_E|P|².
Finally use the original finite Taylor expansion at a, as printed on p.143. The coordinatewise
monomial differentiation in E6 proves its coefficients are D^βP(a)/β!: apply the same formula to the
translated polynomial z↦P(a+z), or expand each original monomial by the finite binomial identity and
compare coefficients. Thus Q(y)=P(a+ρy) has coefficient ρ^{|β|}D^βP(a)/β! at y^β, and
D^βQ(0)=ρ^{|β|}D^βP(a), with the same classical mixed derivatives. This includes β=0, n=0 and the
zero polynomial. Apply E6 to the normalized Q and full null-measurable E′, using its Borel
representative S₀ as admissible indicator. Divide by positive ρ^{|β|}; the square root of the
positive scaling factor is ρ^(−N/2). The result is the exact public estimate
K₀ρ^(−|β|−N/2)(∫_E|P|²)^(1/2). This is Campanato (2.12) and the final derivative calculation, with
the normalized positive minimum established in E5 relative to the named Mityagin source theorem and
its lower analytic obligations; there is no change to the Euclidean model or classical
derivative/integral meanings.


This lemma retains the normalized positive-minimum, classical mixed-derivative and
affine-scaling obligations E1–E7. Its proof is not yet formalized. -/
theorem polynomial_measurable_subset_l2_derivative_estimate
    (N n : ℕ) (hN : 1 ≤ N) (A : ℝ) (hA : 0 < A)
    (hAv : A ≤ volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (P : MvPolynomial (Fin N) ℝ) (a : EuclideanSpace ℝ (Fin N))
        (ρ : ℝ) (E : Set (EuclideanSpace ℝ (Fin N))),
        P.totalDegree ≤ n → 0 < ρ → NullMeasurableSet E volume →
        E ⊆ Metric.ball a ρ → A * ρ ^ N ≤ volume.real E →
        ∀ β : Fin N → ℕ, (∑ i, β i) ≤ n →
          |euclideanPolynomialMixedPartial P β a| ≤
            K * Real.rpow ρ (-((∑ i, β i) : ℝ) - (N : ℝ) / 2) *
              Real.sqrt (∫ y in E, |euclideanPolynomialEval P y| ^ 2) := by
  exact campanato_measurable_subset_composition_g3 N n hN A hA hAv
    (polynomial_unitSphere_subset_l2_lower_bound_g3 N n hN A hA hAv)

end HolomorphicAnosov.Analysis.Regularity
