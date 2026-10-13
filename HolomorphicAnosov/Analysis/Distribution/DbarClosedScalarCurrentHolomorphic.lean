import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CompactEventuallySubsetMollifierDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordinatePullbackIteratedBound
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.FixedSupportFirstDerivativeSections
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullback
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordFixedPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLMApply
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLMLineDeriv
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanVolume
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanRe
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanIm
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanSingleRe
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToOrderedEuclideanSingleIm
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomainRoundtripLe
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.MonoTestLineDeriv
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclideanLineDeriv
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexDistributionDbarEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.EuclideanDbarFirstTranspose
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.OrderedEuclideanSetIntegralTransport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.OrderedEuclideanOpenIntegralTransport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.OrderedEuclideanIntegrableOnTransport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexTestFromEuclideanApply
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexFixedSupportPairing
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffBmKernelFamily
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffBmKernelEuclidean
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffKernelPairing
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffKernelProductIntegrable
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.MollifierDbarPullback
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.MollifierWeakLimitPullback
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ScaledKernelNegTestDerivative
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ScaledKernelDerivativeSectionPairing
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.LocalMollifierFirstDerivativeFromFamily
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.InteriorMollifierSmoothFirstDerivative
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.TransportedMollification
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ExistsNativeComplexRegularization
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ScaledKernelFDerivNeg
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernelSmooth
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernelSupport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.KernelCurrentOfWeakLimits
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.LocalCutoffBmRepresentation
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmKernelSmoothOffDiagonal
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffDbarSmoothSupport
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CutoffDbarSupportSeparated
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.ComplexToRealArrays
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Exists_local_test_cutoff
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Exists_normalized_test_mollifier
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Local_cutoff_product_dbar
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Local_cutoff_product_smooth
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.RealArraysToFin
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.BmSeparatedKernel
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.Kernel_regularized_pairing
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Distribution.MollifierRegularization
import HolomorphicAnosov.Analysis.DistributionSmoothFixedSupportFamily
import HolomorphicAnosov.Analysis.ScalarBochnerMartinelliCompactSupport
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Conformal
import HolomorphicAnosov.Analysis.Distribution.LocalDirectionalIntegrationByParts
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTest
import HolomorphicAnosov.Analysis.Distribution.ScalarDbarTestApply
import HolomorphicAnosov.Analysis.Distribution.LocalAntiholomorphicIntegrationByParts
import HolomorphicAnosov.Analysis.Distribution.SmoothRepresentativeAntiholomorphicPartialEqZero
import HolomorphicAnosov.Analysis.Distribution.ExistsNestedBalls
import HolomorphicAnosov.Analysis.Distribution.SmoothDbarZeroCoordinateSlices
import HolomorphicAnosov.Analysis.Distribution.SmoothDbarZeroHolomorphic

/-!
# Holomorphic regularity of an antiholomorphically closed scalar current

Source: Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012,
Chapter I §3.E, Lemma (3.29)(a), printed pp.28–29, specialized to p=q=0.

The scalar current is expressed directly as a continuous complex-linear
functional on Mathlib's complex-valued smooth test functions with their
canonical LF topology. Coordinate directions `Pi.single j 1` and
`Pi.single j Complex.I` are the real x_j and y_j directions. The derivative
hypothesis is exactly minus the pairing with (∂x_j φ + i ∂y_j φ)/2.
The product is unconjugated throughout.

Test functions are globally defined smooth zero extensions. Quantifying over
tests on U whose closed support lies in V therefore quantifies over exactly
the tests on V, extended by zero to U. A globally defined representative h
is required to be holomorphic only on V; its values outside V are immaterial.
`volume` on the finite product of complex planes is real Lebesgue measure.
-/

open Function Set Filter MeasureTheory TopologicalSpace

namespace HolomorphicAnosov

open Analysis Analysis.Distribution

open Set
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

/--
Source: Demailly, *Complex Analytic and Differential Geometry*, June 21, 2012,
Chapter I §3.E, Lemma (3.29)(a), printed pp.28–29, p=q=0; regularization
I §2.D.3, formula (2.23), p.19; Koppelman formula I.(3.26), p.27.

Natural-language proof:

1. Fix a∈U. Choose r>0 with closedBall(a,4r)⊂U and put Ω=B(a,4r), V=B(a,r). On the
underlying real Euclidean space choose a smooth real cutoff ψ with inner radius 2r and
outer radius 3r. Then ψ=1 on closedBall(a,2r), supp ψ=closedBall(a,3r)⊂Ω, and A=supp dbarψ
is compact in Ω and disjoint from B(a,2r). These are the nested balls/cutoff in Demailly
p.28, without a change-of-coordinate assumption. Construct a nonnegative normalized smooth
kernel ρ at zero using a bump with outer radius 1/2 and division by its positive integral;
its support is contained in B(0,1), and its integral is one. No radial symmetry is
required because the regularization child records the reflected adjoint kernel.
Providers: mathlib.finiteDimensional_hasContDiffBump, mathlib.contDiffBump_contDiff, mathlib.contDiffBump_one_of_mem_closedBall, mathlib.contDiffBump_tsupport_eq, mathlib.contDiffBump_integral_normed.

2. For 0<ε<r/2, the regularization child gives the smooth function f_ε=T⋆ρ_ε on U_ε with
all dbar_j f_ε=0. Every point of closedBall(a,3r) has distance at least r from the
complement of U, so f_ε is defined smoothly on a neighborhood of supp ψ. Define u_ε=ψf_ε
there and zero elsewhere. This extension is globally smooth and compactly supported in Ω:
near any point outside U_ε, ψ is identically zero on a neighborhood. The product rule
gives dbar_j u_ε=(dbar_jψ)f_ε. Apply the explicitly normalized scalar Bochner–Martinelli
representation to u_ε. For z∈V, ψ(z)=1, so f_ε(z)=∫_Ω κ(z,ζ)f_ε(ζ)dλ(ζ), where
κ(z,ζ)=−(n−1)!/π^n Σ_j[(bar ζ_j−bar z_j)/|ζ−z|^(2n)]dbar_jψ(ζ). This formula uses
unconjugated f_ε and the real orientation specified in the child. Its n=1 value agrees
with Cauchy (3.2).
Providers: analysis.local_distribution_mollifier_regularization_g2, analysis.scalar_bochnermartinelli_compact_support_g2.

3. For z∈V and ζ∈A the distance |ζ−z| exceeds r. Define κ as zero where all derivatives of
ψ vanish, including a neighborhood of the diagonal. This gives a jointly smooth function
on V×U, since the rational denominator is nonzero on a neighborhood of V×A and dbarψ
vanishes on a full neighborhood of every possible diagonal point. Its ζ-support lies in
the fixed compact A. Put g(z)=T(κ(z,·)). The smooth fixed-support family theorem implies
g∈C∞(V), with all real z-derivatives obtained by pairing the corresponding derivatives of
κ. This is the smooth scalar content of Demailly p.28 off-diagonal cutoff term; the
doubled holomorphic kernel for general (p,q)-forms is unnecessary once scalar smoothness
is obtained.
Providers: analysis.distribution_smooth_fixed_support_family_g2.

4. To prove equality of currents, fix φ∈C_c^∞(V,ℂ) and define η(ζ)=∫_V φ(z)κ(z,ζ)dλ(z).
The family theorem says η is a test on U with support in A and ∫_V φg=T(η). Multiply the
regularized representation in step2 by φ and integrate in z. Fubini applies because
(z,ζ)↦φ(z)κ(z,ζ)f_ε(ζ) is smooth with compact support in supp φ×A; hence ∫_Vφ f_ε=∫_Ωη
f_ε. The regularization child, applied to the two FIXED tests φ and η extended by zero on
U, gives respectively convergence to T(φ) and T(η). Uniqueness of the scalar limit
therefore gives T(φ)=∫_Vgφ. No pointwise or uniform convergence of f_ε is needed.
Providers: analysis.distribution_smooth_fixed_support_family_g2, analysis.local_distribution_mollifier_regularization_g2, mathlib.integral_integral_swap.

5. Fix j and a test φ supported in V. The definition of dbarT and the equality in step4
give 0=−∫_Vg dbar_jφ. To justify integration by parts on a local function, choose radii
s<t<r with supp φ⊂B(a,s) and take the bump χ centered at a with inner radius s and outer
radius t. Compactness of supp φ and its containment in V give these radii (if supp φ is
empty the test assertion is zero). Thus χ is smooth, compactly supported in V and equal to
one on a neighborhood of supp φ. The global zero extension of χg is smooth, and its real
derivatives equal those of g on supp φ. Apply real bilinear integration by parts to each
of x_j,y_j, with complex multiplication as a continuous real-bilinear map. Its three
integrability guards hold because all products contain φ or its compactly supported
derivative, and χg is smooth with compact support. Taking the combination (∂_xj+i∂_yj)/2
gives ∫_V(dbar_j g)φ=0 for every complex φ. The continuous function dbar_jg is locally
integrable; restricting to real φ, the smooth-test uniqueness theorem makes it zero almost
everywhere on V. Convert to the restricted measure using ae_restrict_iff′. Since it and
zero are continuous on the open V and Lebesgue measure is positive on open sets, the open-
set pointwise theorem gives dbar_jg=0 everywhere on V. This expands Demailly (2.5)–(2.6),
p.15, for the stated scalar convention.
Providers: mathlib.finiteDimensional_hasContDiffBump, mathlib.contDiffBump_contDiff, mathlib.contDiffBump_one_of_mem_closedBall, mathlib.contDiffBump_tsupport_eq, mathlib.integral_bilinear_fderiv_right_eq_neg_left_of_integrable, mathlib.continuousOn_locallyIntegrableOn, mathlib.isOpen_ae_eq_zero_of_integral_contDiff_smul_eq_zero, mathlib.measure_eqOn_open_of_ae_eq, mathlib.ae_restrict_iff_prime.

6. For a coordinate slice of g through any point of V, smoothness gives real
differentiability on its open slice domain. The equation dbar_jg=(∂_xjg+i∂_yjg)/2=0
implies ∂_yjg=i∂_xjg. The exact real-to-complex differentiability criterion therefore
makes each slice complex differentiable. The original g is continuous. Every point b∈V
admits a closed polydisc centered at b with all positive radii and contained in V. Apply
the existing polydisc Cauchy/power-series theorem to g on that polydisc; it gives complex
analyticity near b, hence holomorphy. This uses Demailly I §3.B (3.8)–(3.9), p.22, with
the correct several-variable upgrade, not a one-variable theorem on ℂ^n.
Providers: mathlib.differentiableAt_complex_iff_differentiableAt_real_g2, analysis.polydisc_cauchy_power_series.

7. Take h=g on V. Step4 gives exactly the unconjugated distributional identity in the
statement and step6 gives its holomorphy. The choice of a was arbitrary. No gluing or
pointwise representative for T was assumed; empty U has no a to consider and the zero
distribution yields g=0.

Edge cases: n=0 is excluded by hn; empty U has no a to consider.
Disconnected U needs no gluing. The zero current is represented by h=0.
The equality is distributional and makes no assertion about arbitrary pointwise
representatives. The Euclidean balls in the proof may use the equivalent
Euclidean norm on the finite product; the statement uses its standard product
norm, with the same smoothness, topology, complex differentiability and volume.
-/
theorem dbar_closed_scalar_current_holomorphic
    {n : ℕ} (hn : 1 ≤ n) (U : Opens (Fin n → ℂ))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ (j : Fin n) (φ : TestFunction U ℂ ⊤),
      -T ((2 : ℂ)⁻¹ •
        ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ : TestFunction U ℂ ⊤) +
          Complex.I •
            (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
              TestFunction U ℂ ⊤))) = 0) :
    ∀ a ∈ U, ∃ V : Opens (Fin n → ℂ),
      a ∈ V ∧ V ≤ U ∧
        ∃ h : (Fin n → ℂ) → ℂ,
          DifferentiableOn ℂ h (V : Set (Fin n → ℂ)) ∧
            ∀ φ : TestFunction U ℂ ⊤,
              tsupport (φ : (Fin n → ℂ) → ℂ) ⊆ (V : Set (Fin n → ℂ)) →
                T φ = ∫ z in (V : Set (Fin n → ℂ)), h z * φ z ∂volume := by
  intro a ha
  obtain ⟨P, ψ, haP, hPU, hψ⟩ := exists_local_test_cutoff U a ha
  obtain ⟨Q, f, hQ, hsm, hbar, hweak⟩ := exists_native_complex_regularization hn U T hT
  let e := complexToOrderedEuclidean n
  have hKU : e '' tsupport (ψ : (Fin n → ℂ) → ℂ) ⊆ coordDomain e.symm U := by
    rintro _ ⟨x, hx, rfl⟩
    change e.symm (e x) ∈ U
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ψ.tsupport_subset hx
  obtain ⟨δ, hδ, hmargin⟩ := compact_eventually_subset_mollifierDomain
    (coordDomain e.symm U) (e '' tsupport (ψ : (Fin n → ℂ) → ℂ))
    (ψ.hasCompactSupport.image e.continuous) hKU
  have hψQ (ε : ℝ) (hεδ : ε < δ) : tsupport (ψ : (Fin n → ℂ) → ℂ) ⊆ Q ε := by
    intro x hx
    rw [hQ]
    exact hmargin ε hεδ (Set.mem_image_of_mem e hx)
  have hPQ (ε : ℝ) (hεδ : ε < δ) : P ≤ Q ε := by
    intro x hx
    apply hψQ ε hεδ
    apply subset_tsupport ψ
    rw [Function.mem_support, hψ x hx]
    exact one_ne_zero
  obtain ⟨s, hs, hg, hi⟩ := cutoff_kernel_pairing hn U P T ψ hψ
  let g : (Fin n → ℂ) → ℂ := fun x ↦ T (s x)
  refine ⟨P, haP, hPU, g, ?_⟩
  have hrepr : ∀ φ : TestFunction P ℂ ⊤,
      T (TestFunction.monoCLM ℂ φ) = ∫ z in (P : Set _), g z * φ z := by
    intro φ
    obtain ⟨η, hint, hη, hηsupp, hintpair, hpair⟩ := hi φ
    apply kernel_current_of_weak_limits U P hPU T
      (bmSeparatedKernel (fun j ↦ antiholomorphicPartial ψ j))
      (fun x ↦ T (s x)) φ η hη hpair Q f
    · let φU : TestFunction U ℂ ⊤ := TestFunction.monoCLM ℂ φ
      have hφU (x : Fin n → ℂ) : φU x = φ x := by
        simp [φU, TestFunction.monoCLM_apply, hPU]
      apply (hweak φU).congr'
      filter_upwards [(nhdsWithin_le_nhds (Iio_mem_nhds hδ))] with ε hεδ
      have hzero (x : Fin n → ℂ) (hx : x ∉ P) : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hx' ↦ hx (φ.tsupport_subset hx'))
      have hleft : (∫ x in (Q ε : Set _), f ε x * φU x) = ∫ x, f ε x * φ x := by
        simp only [hφU]
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [hzero x (fun hxP ↦ hx (hPQ ε hεδ hxP)), mul_zero]
      have hright : (∫ x in (P : Set _), f ε x * φ x) = ∫ x, f ε x * φ x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [hzero x hx, mul_zero]
      exact hleft.trans hright.symm
    · exact hweak η
    · filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (Iio_mem_nhds hδ))] with ε hε hεδ
      have he : 0 < ε := hε
      refine ⟨?_, ?_⟩
      · intro p hp
        exact local_cutoff_bm_representation hn U (Q ε) ψ (hψQ ε hεδ)
          (f ε) (hsm ε he) (hbar ε he) p (hψ p hp)
      · exact cutoff_kernel_product_integrable U P (Q ε) ψ hψ φ (f ε)
          ((hsm ε he).continuousOn.mono (hψQ ε hεδ))
  have hrep : ∀ φ : TestFunction U ℂ ⊤,
      tsupport (φ : (Fin n → ℂ) → ℂ) ⊆ (P : Set _) →
      T φ = ∫ z in (P : Set _), g z * φ z := by
    intro φ hφ
    let φP : TestFunction P ℂ ⊤ := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
    have hmono : (TestFunction.monoCLM ℂ φP : TestFunction U ℂ ⊤) = φ := by
      ext x
      simp [TestFunction.monoCLM_apply, hPU, φP]
    have hh := hrepr φP
    rw [hmono] at hh
    exact hh
  refine ⟨?_, hrep⟩
  exact HolomorphicAnosov.smooth_dbar_zero_holomorphic hn P g hg
    (HolomorphicAnosov.smooth_representative_antiholomorphicPartial_eq_zero
      U P hPU T hT g hg hrep)


end HolomorphicAnosov
