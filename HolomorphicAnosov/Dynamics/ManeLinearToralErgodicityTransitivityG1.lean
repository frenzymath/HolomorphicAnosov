import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_one
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_continuous
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_surjective
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.IntegralToralMap_measurePreserving
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.CircleCharacter_sum
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.MFourier_integralToralMap
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.No_periodic_complex_vector
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Matrix_pow_mulVec
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Transpose_frequency_orbit_injective
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Invariant_l2_ae_const
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Dense_forward_orbit_of_ergodic

/-!
# Ergodicity and a dense forward orbit of an integral toral automorphism

Source: Ricardo Mañé, *Ergodic Theory and Differentiable Dynamics* (Springer, 1987),
II§3 Theorem 3.1 and Lemma 3.3, pp. 107–108; II§2 Proposition 2.6, pp. 104–105;
I§11 Proposition 11.4, pp. 69–70; I§7 Corollary 7.2, p. 47.
DAG node: `dynamics.mane_linear_toral_ergodicity_transitivity_g1`.

This module proves the result for the canonical period-one torus and the existing integer
ROW action `integralToralMap`. The measure is the literal finite product of normalized circle
Haar measures. The proof uses the native Fourier Hilbert basis, spectral mapping, invariant
function constancy and ergodicity to construct a dense forward orbit, including dimension zero.
No Anosov hypothesis, hyperbolicity, mixing, transpose spectral hypothesis or positive-dimensional
restriction is part of the statement.
-/

namespace HolomorphicAnosov.Dynamics

open MeasureTheory

noncomputable section

/-- An integral toral automorphism with no root-of-unity eigenvalue is ergodic and has a dense
forward orbit, including dimension zero.

Source: Mañé II§3 Theorem 3.1 and Lemma 3.3, pp. 107–108; II§2 Proposition 2.6,
pp. 104–105; I§11 Proposition 11.4, pp. 69–70; I§7 Corollary 7.2, p. 47.

Complex eigenvalues are those of the complex-cast matrix acting by row-times-column on
complex coordinate vectors. `HasEigenvalue` means existence of a nonzero eigenvector.
`IsOfFinOrder μ` is exactly the existence of a strictly positive exponent `r` with `μ ^ r = 1`.
The integer general linear group supplies an inverse integral matrix. `Ergodic` includes
measure preservation and the zero-or-conull law for measurable EXACTLY invariant sets.
`DenseRange` of the natural-number iterate map is density of the forward orbit, including
its time-zero point. In dimension zero there are no nonzero eigenvectors and the torus is a
singleton, so the spectral premise is vacuous and its unique forward orbit is dense.

Natural-language proof (the full one-level proof of the matching DAG node):

1. Canonical toral group automorphism and invariant normalized Haar measure. Put
T=UnitAddTorus(Fin n) and F=integralToralMap A. The coordinate finite-sum formula is additive and
continuous, because integer scalar multiplication, addition and finite products are continuous in
AddCircle1. The same formula for the inverse integral matrix gives F_A F_(A^-1)=F_(A^-1) F_A=id by
finite distributivity and the inverse-matrix equations. Thus F is a continuous group automorphism
and a Borel measurable equivalence. Let mu be the canonical product volume, the product of
period-one normalized circle Haar probabilities; mu(T)=1 and it is an additive Haar measure. The
named continuous-surjective Haar homomorphism theorem proves F preserves mu. This is precisely the
surjectivity/measure-preservation guard needed in Mañé I7 Corollary7.2 p47 and II3 p106. Only
invertible integral matrices are used here; the wording of Theorem3.1 is not used to claim that a
nonsurjective homomorphism preserves Haar measure. Dependencies: zhang.def_real_torus_model,
mathlib.addMonoidHom_haar_measurePreserving_g1

2. The actual L2 Fourier Hilbert basis and character covariance. Use the named Mathlib Fourier
Hilbert basis b_k=mFourierLp2(k), k in Z^n, in complex L2(T,mu). Its continuous representatives
are chi_k(pi x)=exp(2 pi i sum_j k_j x_j), well-defined because changing x by an integer vector
changes the exponential by an integral multiple of 2 pi i. In particular chi_0=1. Finite
multiplication of these exponentials gives chi_k(F(pi x))=chi_(A^t k)(pi x); the quotient map is
onto, so chi_k∘F=chi_(A^t k) on T. This is the literal character calculation of Mañé Lemma3.3(b).
Its complete Fourier basis assertion is now supplied directly by Mathlib, rather than a new
cube-to-torus assembly theorem. For every phi in L2, the named Hilbert repr formula gives
c_k=inner(b_k,phi) as its coordinates; the linear isometric equivalence repr is injective. Thus
equal coefficients imply equality in L2, hence almost everywhere equality of represented
functions. Dependencies: mathlib.unitAddTorus_mFourier_hilbertBasis_g1,
mathlib.hilbertBasis_repr_inner_g1

3. No root of unity implies distinct nonzero transpose frequency iterates. Assume n>0. For every
r>=1, (A^t)^r-I is invertible over C. Indeed transpose has the same characteristic polynomial,
hence the same complex eigenvalues, as A, by det(B^t)=det(B). In the nontrivial finite-dimensional
complex endomorphism algebra, apply the named polynomial spectral mapping theorem to p(X)=X^r-1.
The spectrum of p(A^t) is {lambda^r-1:lambda an eigenvalue of A^t}; it excludes0 by the
no-root-of-unity hypothesis. The definition of scalar spectrum then says p(A^t) is a unit. This is
the eigenvalue-power inference explicitly used in Mañé p108, with its algebraic prerequisite
named. If (A^t)^i k=(A^t)^j k for i<j, invertibility of A^t reduces this to ((A^t)^(j-i)-I)k=0.
Its invertibility forces k=0. Consequently for k≠0 the forward transpose frequencies are pairwise
distinct. Dependencies: mathlib.complex_banach_spectrum_polynomial_g1

4. Invariant L2 functions have only the constant Fourier coefficient. Let phi in L2 satisfy
phi∘F=phi almost everywhere. The Haar-preserving Borel equivalence F preserves the integral of
every complex integrable function: apply the existing real-valued integral_comp separately to real
and imaginary parts. Products of L2 functions defining the inner product are integrable by the L2
inner-product construction. Hence inner(phi1∘F,phi2∘F)=inner(phi1,phi2). The character identity in
the previous step gives c_(A^t k)=inner(b_k∘F,phi∘F)=c_k, and induction gives c_((A^t)^j k)=c_k
for all j>=0. For k≠0, apply finite Bessel to the first N distinct frequencies. It gives
N*abs(c_k)^2<=norm(phi)^2 for every positive integer N, which forces c_k=0 by the Archimedean
property. This is exactly the finite-sum version of the square-summability argument printed on
Mañé p108. The coefficients of phi and c_0*1 agree for every k: orthonormality gives the
coefficient c_0 at0 and zero elsewhere. The Hilbert coordinate formula and injectivity of repr
therefore yield phi=c_0*1 in L2. No smoothness, continuous Fourier series, pointwise convergence,
or Riemann-Lebesgue assertion is imposed on phi. Dependencies:
mathlib.measurePreserving_integral_comp, mathlib.unitAddTorus_mFourier_hilbertBasis_g1,
mathlib.hilbertBasis_repr_inner_g1, mathlib.orthonormal_finite_bessel_g1

5. Ergodicity without adding it as a hypothesis. For any measurable exactly F-invariant set E, its
indicator phi=1_E is bounded and belongs to L2 because mu(T)=1. It is an invariant L2 function.
The preceding step makes phi almost everywhere constant. As the measure is nonzero and phi takes
only values0 or1, that constant must be0 or1; consequently mu(E)=0 or mu(E^c)=0. This proves
PreErgodic from its definition; together with the already proved measure preservation it proves
Ergodic F mu. This indicator specialization is the source invariant-function criterion used in
Theorem3.1, and does not use the converse Mathlib theorem that assumes ergodicity to obtain
invariant-function constancy. Dependencies: mathlib.unitAddTorus_mFourier_hilbertBasis_g1,
mathlib.hilbertBasis_repr_inner_g1, mathlib.orthonormal_finite_bessel_g1

6. Positive open sets and the written inverse-iterate union argument. Let U be any nonempty open
subset of T. Its Haar measure is positive by IsOpen.measure_pos. Put S_U=union_(j>=0) F^(-j)(U).
It is open and measurable, contains U, and F^(-1)(S_U)⊆S_U. The source Proposition2.6 calls S_U
invariant; the literal equality can fail, so apply instead the named exact ergodic
backwards-semistable-set theorem. Its hypotheses hold since mu is finite and S_U is measurable. It
makes S_U null or conull, and the positive measure of U excludes the null case. Every nonempty
open set has positive measure, so the conull open S_U is dense: otherwise its complement contains
a nonempty open set of positive measure. This is the actual written inverse-iterate union proof of
Mañé Proposition2.6 pp104–105, with the omitted finite-measure invariance guard made exact. No
flow suspension or ergodicity-to-periodicity inference is used. Dependencies:
mathlib.ergodic_backward_semistable_set_g1, mathlib.isOpen_measure_pos

7. Written countable-base Baire proof of a dense forward orbit. The finite product of circles T is
a nonempty compact metrizable second-countable Hausdorff space and hence Baire. Choose a countable
base of nonempty open sets U_l. For every l and N>=0, W_(l,N)=union_(j>=N)
F^(-j)(U_l)=F^(-N)(S_(U_l)) is open and dense; density follows from the preceding step and the
fact that F^N is a homeomorphism. The named Baire theorem makes the countable intersection over
(l,N) dense and hence nonempty, using the named dense-intersection-with-open theorem with the
nonempty open whole space. A point x in that intersection visits every U_l at arbitrarily large
forward times. Every nonempty open set contains a U_l, so the forward orbit is dense (indeed its
omega-limit set is T). This is the literal countable-base residual-set proof of Mañé I11
Proposition11.4(c)⇒(b) printedpp69–70, applied at the toral homeomorphism scope. If n=0, T is the
singleton, F its identity, Haar its unit point mass, all measurable sets have measure0 or1 and its
unique point has dense forward orbit. Thus the conclusion includes n=0 without applying a
nontrivial matrix spectrum argument. Dependencies: mathlib.baireSpace_locallyCompact_r1,
mathlib.dense_iInter_of_isOpen, mathlib.dense_inter_open_nonempty_g8

Lean proof route: the countable intersection of the conull inverse-iterate unions already
contains a point visiting every basis open set. This replaces the optional Baire refinement
above; arbitrarily late visits are not needed for the stated dense forward orbit.
-/
theorem mane_linear_toral_ergodicity_transitivity_g1 (n : ℕ)
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hroot : ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ →
        ¬ IsOfFinOrder μ) :
    Ergodic (integralToralMap A) (maneUnitTorusHaar n) ∧
      ∃ x : UnitAddTorus (Fin n),
        DenseRange (fun j : ℕ ↦ (integralToralMap A)^[j] x) := by
  classical
  have hmp := integralToralMap_measurePreserving A
  by_cases hn : n = 0
  · subst n
    have hpre : PreErgodic (integralToralMap A) (maneUnitTorusHaar 0) :=
      ⟨fun _ _ _ ↦ Filter.EventuallyConst.of_subsingleton_left⟩
    have he : Ergodic (integralToralMap A) (maneUnitTorusHaar 0) := ⟨hmp, hpre⟩
    exact ⟨he, dense_forward_orbit_of_ergodic _ (integralToralMap_continuous A) he⟩
  · let : NeZero n := ⟨hn⟩
    have hpre : PreErgodic (integralToralMap A) (maneUnitTorusHaar n) := by
      constructor
      intro s hs hsinv
      let g : UnitAddTorus (Fin n) → ℂ := s.indicator (fun _ ↦ 1)
      have hmem : MemLp g 2 (maneUnitTorusHaar n) := (memLp_const (1 : ℂ)).indicator hs
      let φ := hmem.toLp g
      have hgf : g ∘ integralToralMap A = g := by
        funext x
        have hx : integralToralMap A x ∈ s ↔ x ∈ s := Set.ext_iff.mp hsinv x
        simp only [g, Function.comp_apply, Set.indicator_apply, hx]
      have hφinv : φ ∘ integralToralMap A =ᵐ[maneUnitTorusHaar n] φ := by
        have hφg : (φ : UnitAddTorus (Fin n) → ℂ) =ᵐ[maneUnitTorusHaar n] g :=
          hmem.coeFn_toLp
        filter_upwards [hmp.quasiMeasurePreserving.ae_eq_comp hφg, hφg] with x hx hy
        exact hx.trans ((congrFun hgf x).trans hy.symm)
      obtain ⟨c, hc⟩ := invariant_l2_ae_const A hroot φ hφinv
      have hgc : g =ᵐ[maneUnitTorusHaar n] fun _ ↦ c := hmem.coeFn_toLp.symm.trans hc
      obtain ⟨x, hx⟩ := hgc.exists
      have hc01 : c = 0 ∨ c = 1 := by
        by_cases hxs : x ∈ s
        · exact Or.inr (by simpa [g, hxs] using hx.symm)
        · exact Or.inl (by simpa [g, hxs] using hx.symm)
      apply Filter.eventuallyEmptyOrUniv_iff.mpr
      rcases hc01 with rfl | rfl
      · right
        filter_upwards [hgc] with y hy
        intro hys
        simp [g, hys] at hy
      · left
        filter_upwards [hgc] with y hy
        by_contra hys
        simp [g, hys] at hy
    have he : Ergodic (integralToralMap A) (maneUnitTorusHaar n) := ⟨hmp, hpre⟩
    exact ⟨he, dense_forward_orbit_of_ergodic _ (integralToralMap_continuous A) he⟩


end

end HolomorphicAnosov.Dynamics
