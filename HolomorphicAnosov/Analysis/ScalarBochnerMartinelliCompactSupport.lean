import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliRegularizedIntegrationByParts
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCauchyNormalization
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliSingularIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliKernelNormBound
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Algebra.Support
import Mathlib.Data.Nat.Factorial.Basic
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliRegularizedRadialMass
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCoordinateTransport
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Scalar Bochner–Martinelli formula with compact support

Source: Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012,
I §3.A (3.2), p.21, and I §3.D (3.21)–(3.26), pp.25–27.

The coordinate space is `Fin n → ℂ`. Its `volume` is the product of standard planar
Lebesgue measures: `MeasureTheory.MeasureSpace.pi` and `MeasureTheory.volume_pi`
(Mathlib/MeasureTheory/Constructions/Pi.lean), with normalization fixed by
`Complex.volume_preserving_equiv_real_prod`
(Mathlib/MeasureTheory/Measure/Lebesgue/Complex.lean). Thus the positive real measure
is that of the ordered coordinates (x₁,y₁,…,xₙ,yₙ), not a signed differential-form
measure. The kernel uses the explicit Euclidean radius below; the function-space
norm on coordinate tuples is not used as its radius.
-/

noncomputable section

open MeasureTheory ContinuousLinearMap Filter
open scoped BigOperators ContDiff Classical Topology _root_.Topology

namespace HolomorphicAnosov.Analysis

/-- The Euclidean radius in the coordinates of Demailly I §3.D, pp.25–26. -/
def bochnerMartinelliEuclideanNorm {n : ℕ} (w : Fin n → ℂ) : ℝ :=
  Real.sqrt (∑ j, ‖w j‖ ^ 2)

/-- The coordinate Wirtinger derivative `(∂x_j + i ∂y_j)/2`, as in
Demailly I §3.A, p.21. The real Fréchet derivative is applied to the actual real
coordinate vectors `1` and `i` in the j-th complex coordinate. -/
def antiholomorphicPartial {n : ℕ} (u : (Fin n → ℂ) → ℂ) (j : Fin n)
    (ζ : Fin n → ℂ) : ℂ :=
  ((fderiv ℝ u ζ) (Pi.single j 1) +
    Complex.I * (fderiv ℝ u ζ) (Pi.single j Complex.I)) / 2

/-- The j-th scalar kernel coefficient of Demailly I §3.D, pp.26–27, with the
Euclidean radius and the value zero assigned on the diagonal by totalized division.
The corrected scalar sign is placed in the theorem's overall coefficient. -/
def scalarBochnerMartinelliKernel {n : ℕ} (j : Fin n) (z ζ : Fin n → ℂ) : ℂ :=
  star (ζ j - z j) / (bochnerMartinelliEuclideanNorm (ζ - z) : ℂ) ^ (2 * n)

/--
The compact-support scalar Bochner–Martinelli formula, including absolute
integrability, the off-diagonal singularity bound, independence of the kernel's
diagonal values, and its one-dimensional Cauchy specialization. Compact support
and the bound are asserted separately for every coordinate derivative; their
constants may depend on u, z and j. The `Integrable` assertions are Bochner
integrability over complex-valued functions, hence include absolute integrability.
For n=1, the final formula uses the unique coordinate, under the canonical
identification `Fin 1 → ℂ ≃ ℂ`, with its product measure.

Source:
Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §3.A scalar Cauchy formula
(3.2), printed p.21; I §3.D Newton kernel (3.21)–(3.22), p.25 and radial fundamental-solution
calculation and (3.23)–(3.25), p.26; scalar compact-support specialization of Koppelman (3.26),
p.27. The scalar kernel sign is corrected to agree with (3.2) and the stated real orientation; see
source_discrepancy.

Natural-language proof (the complete proof of the DAG node):

1. Work with the Euclidean norm on C^n, i.e. |w|^2=sum_j(x_j^2+y_j^2), and positive Lebesgue
   measure in the ordered coordinates (x1,y1,...,xn,yn). Applying Complex.measurableEquivRealProd
   in each coordinate and reindexing the finite product identifies this measure with coordinate
   real volume. PiLp.volume_preserving_ofLp identifies it with volume of the real Euclidean space
   of dimension 2n used by the radial formulas. The product-coordinate sup norm is used only to
   specify a coordinate box; it is never substituted for the Euclidean radius in the kernel. Put
   c=(n-1)!/pi^n.

2. For epsilon>0 set D_epsilon(w)=|w|^2+epsilon^2, F_epsilon,j(w)=bar(w_j)*D_epsilon(w)^(-n) and
   rho_epsilon(w)=n*epsilon^2*D_epsilon(w)^(-(n+1)). These are globally smooth functions of the
   real coordinates since D_epsilon>0. Direct Wirtinger differentiation gives dbar_j(bar(w_j))=1,
   dbar_j(|w|^2)=w_j, and dbar_j F_epsilon,j=D_epsilon^(-n)-n*|w_j|^2*D_epsilon^(-(n+1)). Summing
   yields sum_j dbar_j F_epsilon,j=rho_epsilon. This is the coefficient version of the smooth
   epsilon regularization used in Demailly p.26; unlike differentiating the Newton expression it
   is valid for n=1 without dividing by n-1.

3. Let q(r)=r^(2n-1)/(1+r^2)^(n+1), r>0. It is integrable near zero since q(r)<=r^(2n-1), and at
   infinity since q(r)<=r^(-3) for r>=1. The existing rpow integrability leaves prove both bounds;
   domination proves IntegrableOn q (Ioi 0). The elementary primitive H(r)=r^(2n)/(2n*(1+r^2)^n)
   has derivative q(r), value H(0)=0, and limit 1/(2n) at infinity. Apply the finite-interval
   fundamental theorem and then convergence of interval integrals to the integral over Ioi 0. Thus
   integral q=1/(2n). The public `scalar_bochnermartinelli_regularized_radial_mass` theorem packages
   this radial normalization, using its public radial primitive dependency. The radial integrability theorem
   gives integrability of (1+|w|^2)^(-(n+1)).
   The radial integral formula and the even-dimensional unit-ball volume alpha_2n=pi^n/n! give
   integral rho_1 = n*(2n*alpha_2n)*(1/(2n))=n*alpha_2n=pi^n/(n-1)!=c^(-1). This expands
   Demailly's Im=sigma_(m-1)/m computation with m=2n.

4. Fix a compactly supported smooth complex test h. It is bounded by some B. The change of
   variables w=epsilon*y gives integral rho_epsilon(w)*h(w) dw = integral rho_1(y)*h(epsilon*y)
   dy. Use the existing Jacobian theorem on the entire real Euclidean space with dilation y ->
   epsilon*y: its derivative is epsilon*Id, its determinant is epsilon^(2n), and it is bijective
   since epsilon>0. The powers cancel because rho_epsilon(epsilon*y)=epsilon^(-2n)*rho_1(y).
   Integrability is verified separately from the integrable rho_1 majorant B*rho_1, not inferred
   from the totalized change-of-variables identity. Use the countably generated right-hand
   neighborhood filter epsilon -> 0+ on Real. Along it, h(epsilon*y) tends to h(0) at every y; the
   same majorant allows dominated convergence. Hence integral rho_epsilon*h tends to c^(-1)*h(0).

5. Put F_j(w)=bar(w_j)/|w|^(2n) for w!=0 and F_j(0)=0. On the punctured space F_epsilon,j -> F_j
   and |F_epsilon,j(w)|<=|w|^(-(2n-1)), uniformly in epsilon>0, since |w_j|<=|w| and
   D_epsilon>=|w|^2. The radial-integrability theorem, with the cutoff radius-R function r ->
   1_(0<r<R)*r^(-(2n-1)), reduces integrability of this majorant near zero to integral_0^R r^0 dr.
   Therefore F_j is locally integrable. A change in its value at 0 has no effect: the point has
   zero real Lebesgue measure, as can also be seen by enclosing it in balls whose volumes
   alpha_2n*r^(2n) tend to zero. All these estimates use n>=1 and real dimension 2n.

6. Choose a coordinate box Q=[-R,R]^(2n) whose interior contains the topological support of h. The
   derivative topological support is contained in that of h, so h and each dbar_j h vanish outside
   a smaller box and near every face of Q. Form the complex-valued coordinate vector field
   G_epsilon with components G_(x_j)=h*F_epsilon,j/2 and G_(y_j)=i*h*F_epsilon,j/2. Its real
   divergence is sum_j dbar_j(h*F_epsilon,j). Apply the general coordinate-box divergence theorem
   with E=Complex, m=2n-1, s=empty, f=G_epsilon and fprime its real derivative. G_epsilon is
   globally smooth and continuous on Q; its divergence is continuous on compact Q and therefore
   integrable there. Every face integral is zero because h vanishes near the box boundary. Outside
   Q the integrand is also zero by support. The product rule therefore gives integral
   h*rho_epsilon = -sum_j integral F_epsilon,j*dbar_j h. This supplies the integration-by-parts
   sign and applies in every n>=1.

7. Each dbar_j h is bounded and compactly supported. The radius cutoff majorant from step 5 times
   this bound is integrable and dominates |F_epsilon,j*dbar_j h|. All functions are measurable:
   smooth away from zero, with an arbitrary assigned value at one null point. Dominated
   convergence gives integral F_epsilon,j*dbar_j h -> integral F_j*dbar_j h, and proves absolute
   integrability of the latter via domination. There are finitely many j, so take the limit in the
   sum in step 6 and combine it with step 4 to obtain c^(-1)*h(0)=-sum_j integral F_j*dbar_j h.
   The pairing is complex-linear in h with no conjugation, exactly matching the transposed
   derivative convention.

8. For the given u and z take h(w)=u(z+w). It is smooth with compact support and dbar_j
   h(w)=dbar_j u(z+w). Translate the integral back to zeta=z+w; this affine map is injective and
   onto, has identity real derivative and determinant one, so the existing Jacobian formula
   preserves the positive Lebesgue measure. Multiply the identity of step 7 by c to obtain exactly
   the displayed scalar formula and its absolute-integrability assertion. Compact support is used
   throughout only for boundedness and the vanishing box faces.

9. When n=1, c=1/pi and F_1(w)=bar(w)/|w|^2=1/w away from zero. The conclusion becomes
   u(z)=-integral dbar u(zeta)/(pi*(zeta-z)), agreeing with Demailly (3.2) p.21. The mass
   calculation is integral epsilon^2/(|w|^2+epsilon^2)^2=pi, so this case was included in the
   regularization argument rather than supplied by a singular n-1 denominator. n=0 stays excluded.
   The existing source_discrepancy about printed (3.23)-(3.24) is retained; no signed
   differential-form identity from those inconsistent lines is used as a premise.

Source discrepancy retained:
With the PDF real orientation dλ=(i/2)^n(−1)^(n(n−1)/2) dz₁∧⋯∧dz_n∧dbar z₁∧⋯∧dbar z_n, printed
(3.23) uses (−1)^j, j=1,…,n. Already at n=1 this gives k_BM=−dz/(2πiz) and dbar k_BM=−δ₀, contrary
to printed (3.24) and the positive fundamental solution (3.4). The first coefficient-divergence
line of the p.26 proof has the negative sign, whereas its subsequent Newton-kernel line changes
that sign. Under the displayed orientation, printed K_BM^(0,0)∧dbar u has coefficient +(n−1)!/π^n
Σ_j(bar ζ_j−bar z_j)|ζ−z|^(−2n)∂bar_j u; its negative is required. This node states that corrected
scalar formula explicitly, derived by smooth epsilon regularization, dilation and the positive
radial mass normalization and checked against (3.2), and does not import the inconsistent printed
sign.
-/
theorem scalar_bochnermartinelli_compact_support
    {n : ℕ} (hn : 1 ≤ n) (u : (Fin n → ℂ) → ℂ)
    (hu : ContDiff ℝ ∞ u) (hsupport : HasCompactSupport u) :
    ∀ z : Fin n → ℂ,
      (∀ j : Fin n,
        Integrable (fun ζ ↦ scalarBochnerMartinelliKernel j z ζ *
          antiholomorphicPartial u j ζ) volume ∧
        HasCompactSupport (antiholomorphicPartial u j) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : Fin n → ℂ, ζ ≠ z →
          ‖scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ‖ ≤
            C / bochnerMartinelliEuclideanNorm (ζ - z) ^ (2 * n - 1)) ∧
      Integrable (fun ζ ↦ ∑ j : Fin n,
        scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ) volume ∧
      u z = -((Nat.factorial (n - 1) : ℂ) / (Real.pi : ℂ) ^ n) *
        (∫ ζ, ∑ j : Fin n,
          scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ ∂volume) ∧
      (∀ a : Fin n → ℂ,
        (∫ ζ, ∑ j : Fin n,
          (if ζ = z then a j else scalarBochnerMartinelliKernel j z ζ) *
            antiholomorphicPartial u j ζ ∂volume) =
        ∫ ζ, ∑ j : Fin n,
          scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ ∂volume) ∧
      (n = 1 → ∀ j : Fin n,
        u z = -(∫ ζ, antiholomorphicPartial u j ζ /
          ((Real.pi : ℂ) * (ζ j - z j)) ∂volume)) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro z
  have hpartialSupport (j : Fin n) : HasCompactSupport (antiholomorphicPartial u j) := by
    have hx := hsupport.fderiv_apply ℝ (Pi.single j (1 : ℂ))
    have hy := hsupport.fderiv_apply ℝ (Pi.single j Complex.I)
    unfold antiholomorphicPartial
    simp only [div_eq_mul_inv]
    exact (hx.add (hy.mul_left (f := fun _ ↦ Complex.I))).mul_right
        (f' := fun _ ↦ (2 : ℂ)⁻¹)
  have hdiagonal (a : Fin n → ℂ) :
      (∫ ζ, ∑ j : Fin n,
        (if ζ = z then a j else scalarBochnerMartinelliKernel j z ζ) *
          antiholomorphicPartial u j ζ ∂volume) =
      ∫ ζ, ∑ j : Fin n,
        scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ ∂volume := by
    apply integral_congr_ae
    filter_upwards [volume.ae_ne z] with ζ hζ
    simp only [ite_eq_right_iff.mpr (fun h ↦ (hζ h).elim)]
  have hsingularity (j : Fin n) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ ζ : Fin n → ℂ, ζ ≠ z →
        ‖scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ‖ ≤
          C / bochnerMartinelliEuclideanNorm (ζ-z) ^ (2*n-1) := by
    have hderiv := hu.continuous_fderiv (by simp)
    have hcontinuous : Continuous (antiholomorphicPartial u j) := by
      unfold antiholomorphicPartial
      exact ((hderiv.clm_apply continuous_const).add
        (continuous_const.mul (hderiv.clm_apply continuous_const))).div_const _
    obtain ⟨C, hC⟩ := (hpartialSupport j).exists_bound_of_continuous hcontinuous
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z)
    refine ⟨C, hC0, ?_⟩
    intro ζ hζ
    have hkernel : ‖scalarBochnerMartinelliKernel j z ζ‖ ≤
        1 / bochnerMartinelliEuclideanNorm (ζ-z) ^ (2*n-1) :=
      scalar_bochnerMartinelli_kernel_norm_bound hn (ζ-z) (sub_ne_zero.mpr hζ) j
    rw [norm_mul]
    calc
      _ ≤ (1 / bochnerMartinelliEuclideanNorm (ζ-z) ^ (2*n-1)) * C :=
        mul_le_mul hkernel (hC ζ) (norm_nonneg _)
          (div_nonneg zero_le_one (pow_nonneg (Real.sqrt_nonneg _) _))
      _ = _ := by ring
  have hintegrable (j : Fin n) : Integrable (fun ζ ↦
      scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ) volume := by
    have hderiv := hu.continuous_fderiv (by simp)
    have hcontinuous : Continuous (antiholomorphicPartial u j) := by
      unfold antiholomorphicPartial
      exact ((hderiv.clm_apply continuous_const).add
        (continuous_const.mul (hderiv.clm_apply continuous_const))).div_const _
    have hkernel : Measurable (fun ζ ↦ scalarBochnerMartinelliKernel j z ζ) := by
      unfold scalarBochnerMartinelliKernel bochnerMartinelliEuclideanNorm
      fun_prop
    obtain ⟨C, hC, hb⟩ := hsingularity j
    exact scalar_bochnerMartinelli_singular_integrable hn _
      (hkernel.mul hcontinuous.measurable).aestronglyMeasurable
      ((hpartialSupport j).mul_left) z hC hb
  have hsumIntegrable : Integrable (fun ζ ↦ ∑ j : Fin n,
      scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ) volume :=
    integrable_finsetSum Finset.univ (fun j _ ↦ hintegrable j)
  have hcauchy (hformula : u z = -((Nat.factorial (n - 1) : ℂ) / (Real.pi : ℂ) ^ n) *
      (∫ ζ, ∑ j : Fin n, scalarBochnerMartinelliKernel j z ζ *
        antiholomorphicPartial u j ζ ∂volume)) :
      n = 1 → ∀ j : Fin n, u z = -(∫ ζ, antiholomorphicPartial u j ζ /
        ((Real.pi : ℂ) * (ζ j - z j)) ∂volume) := by
    intro hn1
    subst n
    intro j
    calc
      u z = _ := hformula
      _ = _ := scalar_bochnerMartinelli_cauchy_normalization
        (fun k ζ ↦ antiholomorphicPartial u k ζ) z j
  let test : (Fin n → ℂ) → ℂ := fun w ↦ u (z + w)
  have htest : ContDiff ℝ ∞ test := hu.comp (contDiff_const.add contDiff_id)
  have htestSupport : HasCompactSupport test :=
    hsupport.comp_homeomorph (Homeomorph.addLeft z)
  have htestPartial (j : Fin n) (w : Fin n → ℂ) :
      antiholomorphicPartial test j w = antiholomorphicPartial u j (z + w) := by
    simp only [antiholomorphicPartial, test, fderiv_comp_add_left]
  have hregularizedIBP (ε : ℝ) (hε : 0 < ε) :=
    scalar_bochnerMartinelli_regularized_integration_by_parts ε hε test htest htestSupport
  have hdivergence (ε : ℝ) (hε : 0 < ε) (w : Fin n → ℂ) :
      let g := fun (j : Fin n) (x : Fin n → ℂ) ↦
        star (x j) / ((∑ k : Fin n, ‖x k‖ ^ 2) + ε ^ 2 : ℂ) ^ n
      (∑ j : Fin n, (fderiv ℝ (g j) w (Pi.single j 1) +
        Complex.I * fderiv ℝ (g j) w (Pi.single j Complex.I)) / 2) =
      (n : ℂ) * (ε : ℂ) ^ 2 /
        ((∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 : ℂ) ^ (n + 1) := by
    classical
    cases n with
    | zero => simp
    | succ n =>
      let D := fun x : Fin (n+1) → ℂ ↦ ((∑ k, ‖x k‖ ^ 2) + ε ^ 2 : ℂ)
      let P := fun j : Fin (n+1) ↦ (ContinuousLinearMap.proj j : (Fin (n+1) → ℂ) →L[ℝ] ℂ)
      let K := fun j : Fin (n+1) ↦ Complex.conjCLE.toContinuousLinearMap.comp (P j)
      let dD : (Fin (n+1) → ℂ) →L[ℝ] ℂ :=
        ∑ j, (star (w j) • P j + w j • K j)
      have hP (j) : HasFDerivAt (fun x : Fin (n+1) → ℂ ↦ x j) (P j) w := (P j).hasFDerivAt
      have hK (j) : HasFDerivAt (fun x : Fin (n+1) → ℂ ↦ star (x j)) (K j) w :=
        Complex.conjCLE.hasFDerivAt.comp w (hP j)
      have hD : HasFDerivAt D dD w := by
        have H := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ (hK j).mul (hP j))).add_const
          ((ε : ℂ) ^ 2)
        convert H using 1
        ext x
        simp only [D, ← Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow, Pi.mul_apply]
        rfl
      have hDne : D w ≠ 0 := by
        have : 0 < (∑ k, ‖w k‖ ^ 2) + ε ^ 2 :=
          add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (sq_pos_of_pos hε)
        dsimp [D]
        exact_mod_cast this.ne'
      have hdD (j : Fin (n+1)) (v : ℂ) :
          dD (Pi.single j v) = star (w j) * v + w j * star v := by
        simp only [dD, sum_apply, add_apply, smul_apply, smul_eq_mul, K,
          ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, P, proj_apply]
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hkj
          simp [hkj]
        · simp
      have hgj (j : Fin (n+1)) :
          fderiv ℝ (fun x : Fin (n+1) → ℂ ↦ star (x j) / D x ^ (n+1)) w =
          star (w j) • (((n+1 : ℂ) * (D w)⁻¹ ^ n) •
            ((-ContinuousLinearMap.mulLeftRight ℝ ℂ (D w)⁻¹ (D w)⁻¹).comp dD)) +
            (D w)⁻¹ ^ (n+1) • K j := by
        have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hDne).comp w hD
        simpa [div_eq_mul_inv, inv_pow, Nat.succ_sub_one, nsmul_eq_mul, Pi.mul_def] using ((hK j).mul (hi.pow (n+1))).fderiv
      have hcoord (j : Fin (n+1)) :
          ((fderiv ℝ (fun x : Fin (n+1) → ℂ ↦ star (x j) / D x ^ (n+1)) w)
              (Pi.single j 1) + Complex.I *
            (fderiv ℝ (fun x : Fin (n+1) → ℂ ↦ star (x j) / D x ^ (n+1)) w)
              (Pi.single j Complex.I)) / 2 =
          (D w)⁻¹ ^ (n+1) - (n+1 : ℂ) * (star (w j) * w j) * (D w)⁻¹ ^ (n+2) := by
        rw [hgj]
        simp only [add_apply, smul_apply,
          smul_eq_mul, ContinuousLinearMap.comp_apply, neg_apply,
          ContinuousLinearMap.mulLeftRight_apply, hdD]
        simp [K, P, pow_succ]
        ring_nf
        simp [Complex.I_sq]
        ring
      dsimp only
      change (∑ j : Fin (n+1),
        ((fderiv ℝ (fun x : Fin (n+1) → ℂ ↦ star (x j) / D x ^ (n+1)) w)
            (Pi.single j 1) + Complex.I *
          (fderiv ℝ (fun x : Fin (n+1) → ℂ ↦ star (x j) / D x ^ (n+1)) w)
            (Pi.single j Complex.I)) / 2) = _
      simp_rw [hcoord]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
      have hs : (∑ j, star (w j) * w j) = D w - (ε : ℂ)^2 := by
        simp [D, Complex.conj_mul', Complex.ofReal_sum, Complex.ofReal_pow]
      rw [hs]
      change _ = ((n+1 : ℕ) : ℂ) * (ε : ℂ)^2 / D w ^ (n+1+1)
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      simp only [inv_pow]
      field_simp [hDne]
      ring
  have hregularizedMassIBP (ε : ℝ) (hε : 0 < ε) :
      (∫ w : Fin n → ℂ, ∑ j : Fin n,
        (star (w j) / ((∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 : ℂ) ^ n) *
          antiholomorphicPartial test j w) =
      -(∫ w : Fin n → ℂ, ((n : ℂ) * (ε : ℂ)^2 /
        ((∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 : ℂ) ^ (n+1)) * test w) := by
    calc
      _ = -(∫ w : Fin n → ℂ, ∑ j : Fin n,
          antiholomorphicPartial (fun x : Fin n → ℂ ↦
            star (x j) / ((∑ k : Fin n, ‖x k‖ ^ 2) + ε ^ 2 : ℂ) ^ n) j w * test w) :=
        hregularizedIBP ε hε
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w ↦ by
          dsimp only
          rw [← Finset.sum_mul]
          congr 1
          exact hdivergence ε hε w
  -- The radial density is integrable; this is the real-dimensional bridge used
  -- by the coordinate transport below.  The exponent is chosen so that
  -- `integrable_rpow_neg_one_add_norm_sq` applies directly.
  have hrealIntegrable : Integrable (fun x : EuclideanSpace ℝ (Fin (2*n)) ↦
      (n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1)) volume := by
    have hr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2*n))) : ℝ) <
        2 * (n + 1) := by simp
    have hbase := integrable_rpow_neg_one_add_norm_sq
      (E := EuclideanSpace ℝ (Fin (2*n)))
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin (2*n)))))
      (r := 2 * (n + 1 : ℝ)) hr
    have hbase' : Integrable (fun x : EuclideanSpace ℝ (Fin (2*n)) ↦
        (1 + ‖x‖ ^ 2) ^ (-(n + 1 : ℝ))) volume := by
      simpa [show -(2 * (n + 1 : ℝ)) / 2 = -(n + 1 : ℝ) by ring] using hbase
    have hmul := hbase'.const_mul (n : ℝ)
    apply hmul.congr
    filter_upwards [] with x
    rw [Real.rpow_neg (by positivity)]
    have he : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
    simp [div_eq_mul_inv, add_comm]
  let coordinateEquiv := bochnerMartinelliCoordinateEquiv n
  let radialComplex : EuclideanSpace ℝ (Fin (2*n)) → ℂ := fun x ↦
    (n : ℂ) / ((‖x‖ ^ 2 + 1 : ℝ) : ℂ) ^ (n + 1)
  let unitDensity : (Fin n → ℂ) → ℂ := fun y ↦
    (n : ℂ) / ((∑ k : Fin n, ‖y k‖ ^ 2) + 1 : ℂ) ^ (n + 1)
  have hrealComplex : Integrable (fun x : EuclideanSpace ℝ (Fin (2*n)) ↦
      Complex.ofReal ((n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1))) volume :=
    (Integrable.ofReal (𝕜 := ℂ) hrealIntegrable)
  have hradialComplex : Integrable radialComplex volume := by
    apply hrealComplex.congr
    filter_upwards [] with x
    simp [radialComplex, div_eq_mul_inv, Complex.ofReal_pow]
  have hunitDensity : Integrable unitDensity volume := by
    have hcomp :=
      (bochnerMartinelliCoordinateEquiv_measurePreserving n).integrable_comp_of_integrable
        hradialComplex
    apply hcomp.congr
    filter_upwards [] with y
    dsimp [coordinateEquiv, radialComplex, unitDensity]
    have hs := bochnerMartinelliCoordinateEquiv_norm y
    have hnonneg : 0 ≤ ∑ j : Fin n, ‖y j‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    rw [hs, Real.sq_sqrt hnonneg]
    simp [div_eq_mul_inv, Complex.ofReal_pow]
  have hunitMass : (∫ y : Fin n → ℂ, unitDensity y) =
      ((Real.pi : ℂ)^n / (Nat.factorial (n - 1) : ℂ)) := by
    have hcomp :=
      (bochnerMartinelliCoordinateEquiv_measurePreserving n).integral_comp'
        radialComplex
    have hcast : (∫ x : EuclideanSpace ℝ (Fin (2*n)),
        Complex.ofReal ((n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1))) =
        Complex.ofReal (∫ x : EuclideanSpace ℝ (Fin (2*n)),
          (n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1)) := by
      simpa only [Complex.ofRealCLM_apply] using
        (ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hrealIntegrable)
    have hpoint : (fun y : Fin n → ℂ ↦ radialComplex (coordinateEquiv y)) =
        unitDensity := by
      funext y
      dsimp [coordinateEquiv, radialComplex, unitDensity]
      have hs := bochnerMartinelliCoordinateEquiv_norm y
      have hnonneg : 0 ≤ ∑ j : Fin n, ‖y j‖ ^ 2 :=
        Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
      rw [hs, Real.sq_sqrt hnonneg]
      simp [div_eq_mul_inv, Complex.ofReal_pow]
    have hradial : (∫ x : EuclideanSpace ℝ (Fin (2*n)),
        (n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1)) =
        (Real.pi : ℝ)^n / (Nat.factorial (n - 1) : ℝ) :=
      scalar_bochnermartinelli_regularized_radial_mass hn
    calc
      _ = ∫ y : Fin n → ℂ, radialComplex (coordinateEquiv y) := by rw [hpoint]
      _ = ∫ x : EuclideanSpace ℝ (Fin (2*n)), radialComplex x := hcomp
      _ = ∫ x : EuclideanSpace ℝ (Fin (2*n)),
          Complex.ofReal ((n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1)) := by
            congr 1
            funext x
            simp [radialComplex, div_eq_mul_inv, Complex.ofReal_pow]
      _ = Complex.ofReal (∫ x : EuclideanSpace ℝ (Fin (2*n)),
          (n : ℝ) / (‖x‖ ^ 2 + 1) ^ (n + 1)) := hcast
      _ = _ := by rw [hradial]; norm_num
  have hscaleMass (ε : ℝ) (hε : 0 < ε) :
      (∫ w : Fin n → ℂ, ((n : ℂ) * (ε : ℂ)^2 /
        ((∑ k : Fin n, ‖w k‖ ^ 2) + ε^2 : ℂ)^(n+1)) * test w) =
      ∫ y : Fin n → ℂ, unitDensity y * test (ε • y) := by
    let F : (Fin n → ℂ) → ℂ := fun w ↦
      ((n : ℂ) * (ε : ℂ)^2 /
        ((∑ k : Fin n, ‖w k‖^2) + ε^2 : ℂ)^(n+1)) * test w
    have hscale := MeasureTheory.Measure.integral_comp_smul_of_nonneg
      (volume : Measure (Fin n → ℂ)) F ε (hR := hε.le)
    have hdim : Module.finrank ℝ (Fin n → ℂ) = 2*n := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
    rw [hdim] at hscale
    have hpoint : ∀ y : Fin n → ℂ,
        (ε : ℂ)^(2*n) * F (ε • y) =
          ((n : ℂ) /
            ((∑ k : Fin n, ‖y k‖^2) + 1 : ℂ)^(n+1)) * test (ε • y) := by
      intro y
      dsimp only [F]
      have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have hnorm (k : Fin n) : ‖(ε • y) k‖ ^ 2 = ε^2 * ‖y k‖^2 := by
        rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        ring
      have hsum0 : (∑ k : Fin n, ‖(ε • y) k‖ ^ 2) =
          ε ^ 2 * (∑ k : Fin n, ‖y k‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        exact hnorm k
      rw [hsum0]
      have hden : ((ε ^ 2 * (∑ k : Fin n, ‖y k‖ ^ 2) : ℝ) : ℂ) + (ε : ℂ)^2 =
          (ε : ℂ)^2 * (((∑ k : Fin n, ‖y k‖ ^ 2 : ℝ) : ℂ) + 1) := by
        push_cast
        ring
      rw [hden, mul_pow, ← pow_mul]
      have hexp : 2 * (n + 1) = 2*n + 2 := by omega
      rw [hexp, pow_add]
      field_simp [hεc]
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have hscaleC : (∫ y : Fin n → ℂ, F (ε • y)) =
        ((ε : ℂ)^(2*n))⁻¹ * ∫ w, F w := by
      simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow] using hscale
    calc
      _ = (ε : ℂ)^(2*n) * (∫ y : Fin n → ℂ, F (ε • y)) := by
        rw [hscaleC, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hεc), one_mul]
      _ = ∫ y : Fin n → ℂ, (ε : ℂ)^(2*n) * F (ε • y) :=
        (integral_const_mul _ _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall hpoint)
  obtain ⟨B, hB⟩ := htestSupport.exists_bound_of_continuous htest.continuous
  have hunitLimit : Tendsto (fun ε : ℝ ↦
      ∫ y : Fin n → ℂ, unitDensity y * test (ε • y)) (𝓝 0)
      (𝓝 (((Real.pi : ℂ)^n / (Nat.factorial (n - 1) : ℂ)) * u z)) := by
    have hlim : Tendsto (fun ε : ℝ ↦
        ∫ y : Fin n → ℂ, unitDensity y * test (ε • y)) (𝓝 0)
        (𝓝 (∫ y : Fin n → ℂ, unitDensity y * test 0)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (μ := volume) (l := 𝓝 (0 : ℝ))
        (F := fun ε y ↦ unitDensity y * test (ε • y))
        (f := fun y ↦ unitDensity y * test 0)
        (fun y ↦ B * ‖unitDensity y‖) ?_ ?_ (hunitDensity.norm.const_mul B) ?_
      · apply Filter.Eventually.of_forall
        intro ε
        have hsmul : Continuous (fun y : Fin n → ℂ ↦ ε • y) := by fun_prop
        have hcont : Continuous (fun y : Fin n → ℂ ↦ test (ε • y)) :=
          htest.continuous.comp hsmul
        exact hunitDensity.aestronglyMeasurable.mul hcont.aestronglyMeasurable
      · apply Filter.Eventually.of_forall
        intro ε
        filter_upwards [] with y
        calc
          ‖unitDensity y * test (ε • y)‖ =
            ‖unitDensity y‖ * ‖test (ε • y)‖ := norm_mul _ _
          _ ≤ ‖unitDensity y‖ * B :=
            mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
          _ = B * ‖unitDensity y‖ := mul_comm _ _
      · apply Filter.Eventually.of_forall
        intro y
        have hy : Tendsto (fun ε : ℝ ↦ ε • y) (𝓝 0)
            (𝓝 (0 : Fin n → ℂ)) := by
          have hcont : Continuous (fun ε : ℝ ↦ ε • y) :=
            continuous_id.smul continuous_const
          simpa using hcont.tendsto (0 : ℝ)
        exact tendsto_const_nhds.mul (htest.continuous.continuousAt.tendsto.comp hy)
    simpa only [integral_mul_const, hunitMass, test, add_zero] using hlim
  have hmassLimit : Tendsto (fun ε : ℝ ↦ ∫ w : Fin n → ℂ,
      ((n : ℂ) * (ε : ℂ)^2 /
        ((∑ k : Fin n, ‖w k‖ ^ 2) + ε^2 : ℂ)^(n+1)) * test w)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.pi : ℂ)^n / (Nat.factorial (n - 1) : ℂ)) * u z)) := by
    apply (hunitLimit.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hscaleMass ε hε).symm
  have hkernelDen (j : Fin n) (ζ : Fin n → ℂ) :
      scalarBochnerMartinelliKernel j z ζ =
        star (ζ j - z j) / ((∑ k : Fin n, ‖(ζ-z) k‖^2 : ℝ) : ℂ)^n := by
    unfold scalarBochnerMartinelliKernel bochnerMartinelliEuclideanNorm
    rw [pow_mul, ← Complex.ofReal_pow,
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))]
  let reg : ℝ → Fin n → (Fin n → ℂ) → ℂ := fun ε j ζ ↦
    star (ζ j-z j) / ((∑ k : Fin n, ‖(ζ-z) k‖^2) + ε^2 : ℂ)^n *
      antiholomorphicPartial u j ζ
  have hsumPos (ζ : Fin n → ℂ) (hζ : ζ ≠ z) :
      0 < ∑ k : Fin n, ‖(ζ-z) k‖^2 := by
    apply lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    intro hzero
    have hsum : ∑ k : Fin n, ‖(ζ-z) k‖^2 = 0 := hzero.symm
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ ↦ sq_nonneg ‖(ζ-z) k‖)).mp hsum
    apply hζ
    funext k
    exact sub_eq_zero.mp (norm_eq_zero.mp
      (sq_eq_zero_iff.mp (hz k (Finset.mem_univ k))))
  have hregMeasurable (ε : ℝ) (j : Fin n) : Measurable (reg ε j) := by
    have hderiv := hu.continuous_fderiv (by simp)
    have hc : Continuous (antiholomorphicPartial u j) := by
      unfold antiholomorphicPartial
      exact ((hderiv.clm_apply continuous_const).add
        (continuous_const.mul (hderiv.clm_apply continuous_const))).div_const _
    dsimp [reg]
    exact (by fun_prop : Measurable (fun ζ : Fin n → ℂ ↦
      star (ζ j-z j) / ((∑ k : Fin n, ‖(ζ-z) k‖^2) + ε^2 : ℂ)^n)).mul hc.measurable
  have hregBound (ε : ℝ) (j : Fin n) : ∀ᵐ ζ ∂volume,
      ‖reg ε j ζ‖ ≤ ‖scalarBochnerMartinelliKernel j z ζ *
        antiholomorphicPartial u j ζ‖ := by
    filter_upwards [volume.ae_ne z] with ζ hζ
    rw [hkernelDen]
    let S : ℝ := ∑ k : Fin n, ‖(ζ-z) k‖^2
    have hS : 0 < S := hsumPos ζ hζ
    have hεnorm : ‖((S : ℂ) + (ε : ℂ)^2)‖ = S + ε^2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (add_nonneg hS.le (sq_nonneg ε))]
    dsimp only [reg]
    simp only [norm_mul, norm_div, norm_star, norm_pow]
    change ‖ζ j-z j‖ / ‖(S : ℂ) + (ε : ℂ)^2‖^n *
      ‖antiholomorphicPartial u j ζ‖ ≤
      ‖ζ j-z j‖ / ‖(S : ℂ)‖^n * ‖antiholomorphicPartial u j ζ‖
    rw [hεnorm, Complex.norm_real, Real.norm_of_nonneg hS.le]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hS _)
      (pow_le_pow_left₀ hS.le (le_add_of_nonneg_right (sq_nonneg ε)) _)
  have hregIntegrable (ε : ℝ) (j : Fin n) : Integrable (reg ε j) volume :=
    (hintegrable j).norm.mono' (hregMeasurable ε j).aestronglyMeasurable
      (hregBound ε j)
  have hkernelLimit (j : Fin n) :
      Tendsto (fun ε : ℝ ↦ ∫ ζ, reg ε j ζ) (𝓝 (0 : ℝ))
        (𝓝 (∫ ζ, scalarBochnerMartinelliKernel j z ζ *
          antiholomorphicPartial u j ζ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun ζ ↦ ‖scalarBochnerMartinelliKernel j z ζ * antiholomorphicPartial u j ζ‖)
    · exact Filter.Eventually.of_forall (fun ε ↦ (hregMeasurable ε j).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun ε ↦ hregBound ε j)
    · exact (hintegrable j).norm
    · filter_upwards [volume.ae_ne z] with ζ hζ
      rw [hkernelDen]
      have hne : ((∑ k : Fin n, ‖(ζ-z) k‖^2 : ℝ) : ℂ)^n ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast (hsumPos ζ hζ).ne')
      let S : ℂ := (∑ k : Fin n, ‖(ζ-z) k‖^2 : ℝ)
      have hd0 : Tendsto (fun ε : ℝ ↦ S + (ε : ℂ)^2) (𝓝 0) (𝓝 S) := by
        simpa using ((tendsto_const_nhds (x := S)).add
          ((Complex.continuous_ofReal.tendsto 0).pow 2))
      have hd := Filter.Tendsto.pow hd0 n
      exact (tendsto_const_nhds.div hd hne).mul tendsto_const_nhds
  have hsumLimit : Tendsto (fun ε : ℝ ↦ ∫ ζ, ∑ j : Fin n, reg ε j ζ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ζ, ∑ j : Fin n, scalarBochnerMartinelliKernel j z ζ *
        antiholomorphicPartial u j ζ)) := by
    have hlim := tendsto_finsetSum Finset.univ (fun j _ ↦ hkernelLimit j)
    simp_rw [← integral_finsetSum _ (fun j _ ↦ hintegrable j)] at hlim
    have heq (ε : ℝ) : (∫ ζ, ∑ j : Fin n, reg ε j ζ) =
        ∑ j : Fin n, ∫ ζ, reg ε j ζ :=
      integral_finsetSum _ (fun j _ ↦ hregIntegrable ε j)
    simpa only [heq] using hlim.mono_left nhdsWithin_le_nhds
  have hregTranslated (ε : ℝ) :
      (∫ ζ, ∑ j : Fin n, reg ε j ζ) =
      ∫ w : Fin n → ℂ, ∑ j : Fin n,
        (star (w j) / ((∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 : ℂ) ^ n) *
          antiholomorphicPartial test j w := by
    rw [← integral_add_left_eq_self (fun ζ ↦ ∑ j : Fin n, reg ε j ζ) z]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w ↦ by
      simp only [reg, htestPartial, add_sub_cancel_left, Pi.add_apply, add_sub_cancel_left]
  have hidentity (ε : ℝ) (hε : 0 < ε) :
      (∫ ζ, ∑ j : Fin n, reg ε j ζ) =
      -(∫ w : Fin n → ℂ, ((n : ℂ) * (ε : ℂ)^2 /
        ((∑ k : Fin n, ‖w k‖ ^ 2) + ε ^ 2 : ℂ) ^ (n+1)) * test w) :=
    (hregTranslated ε).trans (hregularizedMassIBP ε hε)
  have hsumMassLimit : Tendsto (fun ε : ℝ ↦ ∫ ζ, ∑ j : Fin n, reg ε j ζ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(((Real.pi : ℂ)^n / (Nat.factorial (n - 1) : ℂ)) * u z))) := by
    apply hmassLimit.neg.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hidentity ε hε).symm
  have heq := tendsto_nhds_unique hsumLimit hsumMassLimit
  have hformula : u z = -((Nat.factorial (n - 1) : ℂ) / (Real.pi : ℂ) ^ n) *
      (∫ ζ, ∑ j : Fin n, scalarBochnerMartinelliKernel j z ζ *
        antiholomorphicPartial u j ζ) := by
    rw [heq]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hfact : (Nat.factorial (n - 1) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (n - 1)
    field_simp
  exact ⟨fun j ↦ ⟨hintegrable j, hpartialSupport j, hsingularity j⟩,
    hsumIntegrable, hformula, hdiagonal, hcauchy hformula⟩


end HolomorphicAnosov.Analysis
