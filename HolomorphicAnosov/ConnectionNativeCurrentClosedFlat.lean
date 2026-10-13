import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.NativePullbackCurvatureSequence
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.SmoothOneFormFlatOfWeakClosed
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientHolomorphicDbar
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ClosedTypeOneDbar
import HolomorphicAnosov.Paper.Zhang.InvariantConnection
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus
import HolomorphicAnosov.Geometry.NativeUnstableLeafDataOfAnosov
import HolomorphicAnosov.Geometry.NativeSingleBundleFoliationChart
import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.SubmoduleRealification
import HolomorphicAnosov.Analysis.Distribution.RegularPairingL2Bound
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.CurvatureDecayFactorTendsto
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.CurvatureConormJacobian

open Filter MeasureTheory TopologicalSpace Set
open scoped Manifold ContDiff Topology _root_.Topology BigOperators

attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
universe u
namespace HolomorphicAnosov.ConnectionFlatEstimates

open HolomorphicAnosov QuotientLineConnection

/-! A compactly supported regular current vanishes when its coefficient has
vanishing L² mass. This is the compact-support Cauchy--Schwarz step used in
Zhang's curvature passage (equation (11) to the distributional limit). -/
theorem regular_pairing_tendsto_zero_of_l2_curvature {d : ℕ}
    (Ω : TopologicalSpace.Opens (Fin d → ℂ))
    (b : ℕ → (Fin d → ℂ) → ℂ)
    (hb : ∀ n, ContinuousOn (b n) Ω)
    (φ : TestFunction Ω ℂ ⊤)
    (hL2 : Filter.Tendsto (fun n ↦ ∫ z in tsupport φ,
      ‖b n z‖ ^ 2 ∂volume) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦
      DistributionalSection.regularPairing Ω (b n) φ)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n, ‖DistributionalSection.regularPairing Ω (b n) φ‖ ≤
      Real.sqrt (∫ z in tsupport φ, ‖b n z‖ ^ 2 ∂volume) *
        Real.sqrt (∫ z in tsupport φ, ‖φ z‖ ^ 2 ∂volume) := by
    intro n
    exact DistributionalSection.regular_pairing_l2_bound Ω (b n) (hb n) φ
  apply squeeze_zero_norm hbound
  have hs := (Real.continuous_sqrt.continuousAt.tendsto.comp hL2).mul_const
    (Real.sqrt (∫ z in tsupport φ, ‖φ z‖ ^ 2 ∂volume))
  simpa only [Real.sqrt_zero, zero_mul, Function.comp_def] using hs

/-! The alternating two-direction current term also vanishes under the
curvature L² estimates for the two differentiated tests. -/
theorem alternating_regular_pairing_tendsto_zero_of_l2_curvature {d : ℕ}
    (Ω : TopologicalSpace.Opens (Fin d → ℂ))
    (b : ℕ → (Fin d → ℂ) → ℂ)
    (hb : ∀ n, ContinuousOn (b n) Ω)
    (j₀ : Fin d) (v w : Fin d → ℂ)
    (φ : TestFunction Ω ℂ ⊤)
    (hL2v : Filter.Tendsto (fun n ↦ ∫ z in
      tsupport ((TestFunction.lineDerivCLM ℂ v φ : TestFunction Ω ℂ ⊤)), ‖b n z‖ ^ 2 ∂volume)
      Filter.atTop (nhds 0))
    (hL2w : Filter.Tendsto (fun n ↦ ∫ z in
      tsupport ((TestFunction.lineDerivCLM ℂ w φ : TestFunction Ω ℂ ⊤)), ‖b n z‖ ^ 2 ∂volume)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦
      -DistributionalSection.regularPairing Ω (b n)
          (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
        DistributionalSection.regularPairing Ω (b n)
          (TestFunction.lineDerivCLM ℂ w φ) * v j₀)
      Filter.atTop (nhds 0) := by
  have hv := regular_pairing_tendsto_zero_of_l2_curvature Ω b hb
    (TestFunction.lineDerivCLM ℂ v φ : TestFunction Ω ℂ ⊤) hL2v
  have hw := regular_pairing_tendsto_zero_of_l2_curvature Ω b hb
    (TestFunction.lineDerivCLM ℂ w φ : TestFunction Ω ℂ ⊤) hL2w
  simpa using (hv.neg.mul_const (w j₀)).add (hw.mul_const (v j₀))

/-! Equation (11) is reduced to a scalar squeeze once the geometric
curvature estimate has been integrated over the compact manifold. -/
theorem l2_curvature_tendsto_zero_of_decay
    (I : ℕ → ℝ) (C volume rate : ℝ) (k : ℕ)
    (hI : ∀ n, 0 ≤ I n)
    (hbound : ∀ n, I n ≤ C * ((rate ^ (2 * k))⁻¹) ^ n * volume)
    (hdecay : Filter.Tendsto
      (fun n : ℕ ↦ C * ((rate ^ (2 * k))⁻¹) ^ n * volume)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto I Filter.atTop (nhds 0) := by
  exact squeeze_zero hI hbound hdecay

/-! Source-parameter specialization of the integrated curvature squeeze. -/
theorem l2_curvature_tendsto_zero_of_source_decay {d : ℕ}
    (hd : 3 ≤ d) (I : ℕ → ℝ) (C volume rate : ℝ)
    (hrate : 1 < rate)
    (hI : ∀ n, 0 ≤ I n)
    (hbound : ∀ n, I n ≤
      C * ((rate ^ (2 * (d - 2)))⁻¹) ^ n * volume) :
    Filter.Tendsto I Filter.atTop (nhds 0) := by
  apply l2_curvature_tendsto_zero_of_decay I C volume rate (d - 2) hI hbound
  exact curvature_decay_factor_tendsto hd hrate C volume

/-! Pointwise source-parameter specialization of Zhang equation (10). -/
theorem source_curvature_le_conorm_jacobian {d : ℕ}
    (_hd : 3 ≤ d) {R C q u D μ J : ℝ}
    (hC : 0 ≤ C) (hu : 0 ≤ u) (hμ : 0 < μ)
    (hcurvature : R ≤ C * q ^ 2 * u ^ 2)
    (hdet : u * μ ^ (d - 2) ≤ D)
    (hJ : J = q ^ 2 * D ^ 2) :
    R ≤ C * J / μ ^ (2 * (d - 2)) := by
  exact curvature_le_conorm_jacobian (d - 2) hC hu hμ hcurvature hdet hJ

/-! Sequence-level packaging of the pointwise curvature/Jacobian estimate. -/
theorem l2_curvature_tendsto_zero_of_jacobian_decay {d : ℕ}
    (hd : 3 ≤ d) (I J : ℕ → ℝ) (C volume rate : ℝ)
    (hrate : 1 < rate)
    (hI : ∀ n, 0 ≤ I n)
    (hpoint : ∀ n, I n ≤
      C * ((rate ^ (2 * (d - 2)))⁻¹) ^ n * J n)
    (hJbound : ∀ n, J n ≤ volume) (hC : 0 ≤ C) :
    Filter.Tendsto I Filter.atTop (nhds 0) := by
  apply l2_curvature_tendsto_zero_of_source_decay hd I C volume rate hrate hI
  intro n
  calc
    I n ≤ C * ((rate ^ (2 * (d - 2)))⁻¹) ^ n * J n := hpoint n
    _ ≤ C * ((rate ^ (2 * (d - 2)))⁻¹) ^ n * volume := by
      apply mul_le_mul_of_nonneg_left (hJbound n)
      exact mul_nonneg hC (pow_nonneg (inv_nonneg.mpr (by positivity)) _)

/-! The weak-limit uniqueness substep is independent of the native leaf
construction and is kept public for the eventual Zhang (8)--(11) assembly. -/

theorem weak_limit_current_closed_of_vanishing_curvature {n : ℕ}
    (Ω : TopologicalSpace.Opens (Fin n → ℂ)) (j₀ : Fin n)
    (Tseq : ℕ → TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hweak : ∀ φ : TestFunction Ω ℂ ⊤,
      Filter.Tendsto (fun m ↦ Tseq m φ) Filter.atTop (nhds (T φ)))
    (hcurvature : ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      Filter.Tendsto (fun m ↦
        -Tseq m (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
          Tseq m (TestFunction.lineDerivCLM ℂ w φ) * v j₀)
        Filter.atTop (nhds 0)) :
    ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      -T (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
        T (TestFunction.lineDerivCLM ℂ w φ) * v j₀ = 0 := by
  intro v w φ
  have hlim : Filter.Tendsto (fun m ↦
      -Tseq m (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
        Tseq m (TestFunction.lineDerivCLM ℂ w φ) * v j₀)
      Filter.atTop (nhds (
        -T (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
          T (TestFunction.lineDerivCLM ℂ w φ) * v j₀)) := by
    exact (((hweak (TestFunction.lineDerivCLM ℂ v φ)).neg.mul_const (w j₀)).add
      ((hweak (TestFunction.lineDerivCLM ℂ w φ)).mul_const (v j₀)))
  exact tendsto_nhds_unique hlim (hcurvature v w φ)

/-! The preceding L² estimate can be fed directly into the weak-limit
uniqueness argument once a pointwise weak current limit is supplied. -/
theorem weak_limit_current_closed_of_l2_curvature {d : ℕ}
    (Ω : TopologicalSpace.Opens (Fin d → ℂ))
    (b : ℕ → (Fin d → ℂ) → ℂ)
    (hb : ∀ n, ContinuousOn (b n) Ω)
    (j₀ : Fin d)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hweak : ∀ φ : TestFunction Ω ℂ ⊤,
      Filter.Tendsto (fun n ↦
        DistributionalSection.regularPairing Ω (b n) φ)
        Filter.atTop (nhds (T φ)))
    (hL2 : ∀ (v : Fin d → ℂ) (φ : TestFunction Ω ℂ ⊤),
      Filter.Tendsto (fun n ↦ ∫ z in
        tsupport (TestFunction.lineDerivCLM ℂ v φ : TestFunction Ω ℂ ⊤),
        ‖b n z‖ ^ 2 ∂volume) Filter.atTop (nhds 0)) :
    ∀ (v w : Fin d → ℂ) (φ : TestFunction Ω ℂ ⊤),
      -T (TestFunction.lineDerivCLM ℂ v φ) * w j₀ +
        T (TestFunction.lineDerivCLM ℂ w φ) * v j₀ = 0 := by
  let Tseq : ℕ → TestFunction Ω ℂ ⊤ →L[ℂ] ℂ := fun n ↦
    TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ)
      volume (b n)
  have hTseq (n : ℕ) (φ : TestFunction Ω ℂ ⊤) :
      Tseq n φ = DistributionalSection.regularPairing Ω (b n) φ := by
    rw [DistributionalSection.regularPairing,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ by simp [φ.zero_on_compl hz])]
    rw [show (fun z ↦ b n z * φ z) = (fun z ↦ φ z * b n z) by
      funext z; exact mul_comm _ _]
    exact TestFunction.integralAgainstBilinCLM_eq_integral
      ((hb n).locallyIntegrableOn Ω.isOpen.measurableSet (μ := volume))
  have hweak' : ∀ φ : TestFunction Ω ℂ ⊤,
      Filter.Tendsto (fun n ↦ Tseq n φ) Filter.atTop (nhds (T φ)) := by
    intro φ
    simpa only [hTseq] using hweak φ
  apply weak_limit_current_closed_of_vanishing_curvature Ω j₀ Tseq T hweak'
  intro v w φ
  have hcurv := alternating_regular_pairing_tendsto_zero_of_l2_curvature Ω b hb j₀ v w φ
    (hL2 v φ)
    (hL2 w φ)
  simpa only [hTseq] using hcurv

/-!
The source-level current/curvature provider for Zhang Lemma 2.3.

Source: Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*,
arXiv:2609.37695v1, §2.1, equations (8)--(11), printed pp.6--7; the
distributional passage is Demailly, I §2.B.1 (2.6), printed p.15.

The proof obligation is deliberately named here rather than hidden in the
parent theorem.  In a native holomorphic foliation box, the invariant pullback
connections have coefficients `aₙ dz`; the Anosov quotient and unstable
determinant estimates make their curvature tend to zero in L².  Compactly
supported test functions therefore give the displayed closed-current identity
in the limit.  Directional integration by parts identifies the regular current
with the alternating derivative, and the existing
`smooth_oneForm_flat_of_weak_closed` lemma supplies the classical flatness.
The native-box existence and the L² limit are the remaining source proof
steps; they are not additional hypotheses of Zhang's lemma and are retained as
this named provider's `sorry`.
-/
/-!
Named Zhang (8)--(11) residual for the local weak-current identity. The direct
native single-bundle box construction is available in the proof context. The
source proof chooses the native box, pulls the invariant connection back along
the iterates, and writes its coefficient as `aₙ dz`; the Anosov quotient and
unstable determinant estimates give the L² curvature bound tending to zero.
Equation (10) then makes the curvature contribution vanish against every
compactly supported test, and equation (11), by integration by parts, gives the
displayed alternating derivative identity. The existing weak-limit helper above
performs this last distributional passage once those pullback coefficients and
their L² estimate are supplied. This named theorem records precisely the
remaining source-level construction, with no extra hypothesis added. -/
theorem native_pullback_l2_current_closed
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : Connection U) (hcontinuous : IsContinuous nabla)
    (hcompatible : IsCompatible nabla)
    (hinvariant : IsInvariant nabla f hU) :
    (∀ (V : Opens X) (e : HolomorphicFrame U V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      let Ω : Opens (ComplexModel d) :=
        ⟨c.target ∩ c.symm ⁻¹' (V : Set X), c.isOpen_inter_preimage_symm V.isOpen⟩
      ∀ (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤),
        (∑ j : Fin d,
          (-DistributionalSection.regularPairing Ω
            (fun z ↦ coordinateForm nabla e c z (Pi.single j 1))
            (TestFunction.lineDerivCLM ℂ v φ) * w j +
          DistributionalSection.regularPairing Ω
            (fun z ↦ coordinateForm nabla e c z (Pi.single j 1))
            (TestFunction.lineDerivCLM ℂ w φ) * v j)) = 0 )  := by
  intro V e c hc
  dsimp
  obtain ⟨R, hR, hweak, hL2⟩ := native_pullback_curvature_sequence
    hd f a hstable U hU_real hU nabla hcontinuous hcompatible hinvariant V e c hc
  intro v w φ
  exact tendsto_nhds_unique (hweak v w φ)
    (regular_pairing_tendsto_zero_of_l2_curvature _ (fun n ↦ R n v w)
      (fun n ↦ hR n v w) φ (hL2 v w φ))

/-!
Named final Zhang flatness residual. Once the local weak-current identity is
known, the source passes from the alternating distributional derivative to the
classical curvature coefficient in each normalized holomorphic quotient frame.
The coefficient is represented by the invariant pullback sequence; the same
Anosov L² estimate used by `native_pullback_l2_current_closed` makes its
curvature pairings converge to zero. Directional integration by parts and
uniqueness of continuous regular currents identify the alternating first
derivative with zero. The invariant recurrence then upgrades the limiting
coefficient to the differentiability required by `IsFlat`, and the resulting
coordinate curvature is the zero alternating derivative. This theorem keeps
that source-level regularity/flatness passage named while the parent consumes
it without changing Zhang's statement. -/

/-! The native coordinate form is real smooth after the type-(1,0) equation is
transported through the inverse-chart tangent model. This keeps the real-linear
versus complex-linear distinction explicit; no arbitrary real-linear map is
silently treated as complex-linear. -/
theorem coordinate_form_real_smooth_current
    {n : ℕ} (Ω : Set (Fin n → ℂ))
    (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] ℂ)
    (coeff : Fin n → (Fin n → ℂ) → ℂ)
    (hcoeff : ∀ k, ContDiffOn ℝ ∞ (coeff k) Ω)
    (heval : ∀ z ∈ Ω, ∀ v, A z v = ∑ k : Fin n, v k • coeff k z) :
    ContDiffOn ℝ ∞ A Ω := by
  apply contDiffOn_clm_apply.mpr
  intro v
  have hs : ContDiffOn ℝ ∞ (fun z ↦ ∑ k : Fin n, v k • coeff k z) Ω := by
    apply ContDiffOn.sum
    intro k hk
    exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Fin n → ℂ ↦ v k) Ω).smul (hcoeff k)
  apply hs.congr
  intro z hz
  exact heval z hz v

/--
Source residual for the regularity step.  A continuous coefficient one-form,
the transported type-(1,0) identity, and the finite closed-current equations
are the hypotheses used by the dbar argument to recover smooth coefficients.
The old continuity-only helper was false (a continuous nonsmooth coefficient
can satisfy the type identity), so this declaration keeps the current-based
regularity passage explicit for a later proof.
-/
theorem native_coordinate_form_regular_from_current
    {n : ℕ} (Ω : Opens (Fin n → ℂ))
    (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] ℂ)
    (hAcont : ContinuousOn A Ω)
    (htype : ∀ z ∈ Ω, ∀ v : Fin n → ℂ,
      A z (Complex.I • v) = Complex.I * A z v)
    (T : Fin n → TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ (k : Fin n) (φ : TestFunction Ω ℂ ⊤), T k φ =
      DistributionalSection.regularPairing Ω
        (fun z ↦ A z (Pi.single k 1)) φ)
    (hcurrent : ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      (∑ k : Fin n, (-T k (TestFunction.lineDerivCLM ℂ v φ) * w k +
        T k (TestFunction.lineDerivCLM ℂ w φ) * v k)) = 0) :
    ContDiffOn ℝ ∞ A Ω := by
  let coeff := fun k : Fin n ↦ fun z ↦ A z (Pi.single k 1)
  have hcoeff (k : Fin n) : ContinuousOn (coeff k) Ω :=
    hAcont.clm_apply continuousOn_const
  have hhol (k : Fin n) : DifferentiableOn ℂ (coeff k) (Ω : Set (Fin n → ℂ)) := by
    exact continuous_coefficient_holomorphic_of_current Ω (coeff k) (hcoeff k) (T k) (hT k)
      (closed_typeOne_current_dbar_zero Ω T hcurrent k)
  have hsmooth (k : Fin n) : ContDiffOn ℝ ∞ (coeff k) (Ω : Set (Fin n → ℂ)) := by
    have hcpx : ContDiffOn ℂ ∞ (coeff k) (Ω : Set (Fin n → ℂ)) :=
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.contDiffOn_of_holomorphic Ω.isOpen (hhol k)
    exact hcpx.restrict_scalars ℝ
  apply coordinate_form_real_smooth_current Ω A coeff hsmooth
  intro z hz v
  exact real_linear_type_one_coordinate_sum (A z) (htype z hz) v


/-!
The finite integration bridge is stated with the transported type-(1,0)
identity explicitly.  This premise is necessary because `A` is represented
as a real-linear map: without it, its values on the complex coordinate basis
do not determine `A z w` for arbitrary complex `w`.  Continuity on Ω and compact support of the differentiated test functions
give integrable coordinate summands. Expand the finite coordinate sum using
the type identity, identify the test derivative using lineDerivCLM, and
move the finite sum through the Bochner integral. Outside Ω both integrands
vanish because the differentiated test vanishes. The two resulting sums
are exactly hcurrent. This is Zhang (10)--(11), the coefficient-current
conversion, and needs no derivative of A.
-/
theorem finite_current_integration_bridge {n : ℕ}
    (Ω : Opens (Fin n → ℂ))
    (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] ℂ)
    (hAcont : ContinuousOn A Ω)
    (htype : ∀ z ∈ Ω, ∀ v : Fin n → ℂ,
      A z (Complex.I • v) = Complex.I * A z v)
    (T : Fin n → TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ (k : Fin n) (φ : TestFunction Ω ℂ ⊤), T k φ = DistributionalSection.regularPairing Ω
      (fun z ↦ A z (Pi.single k 1)) φ)
    (hcurrent : ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤), (∑ k : Fin n,
      (-T k (TestFunction.lineDerivCLM ℂ v φ) * w k +
        T k (TestFunction.lineDerivCLM ℂ w φ) * v k)) = 0) :
    ∀ (v w : Fin n → ℂ) (φ : TestFunction Ω ℂ ⊤),
      -(∫ x, A x w * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x v) +
        (∫ x, A x v * fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x w) = 0 := by
  classical
  have hpair (w : Fin n → ℂ) (ψ : TestFunction Ω ℂ ⊤) :
      (∫ x, A x w * ψ x) = ∑ k : Fin n, T k ψ * w k := by
    have hint (k : Fin n) : Integrable (fun x ↦ ψ x * A x (Pi.single k 1)) := by
      exact ψ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
        ((hAcont.clm_apply continuousOn_const).locallyIntegrableOn Ω.isOpen.measurableSet)
    calc
      (∫ x, A x w * ψ x) =
          ∫ x, ∑ k : Fin n, (ψ x * A x (Pi.single k 1)) * w k := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : x ∈ Ω
        · rw [real_linear_type_one_coordinate_sum (A x) (htype x hx) w,
            Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [smul_eq_mul]
          ring
        · simp [ψ.zero_on_compl hx]
      _ = ∑ k : Fin n, (∫ x, ψ x * A x (Pi.single k 1)) * w k := by
        rw [integral_finsetSum _ (fun k hk ↦ (hint k).mul_const (w k))]
        simp only [integral_mul_const]
      _ = ∑ k : Fin n, T k ψ * w k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hT, DistributionalSection.regularPairing,
          setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun x hx ↦ by simp [ψ.zero_on_compl hx])]
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ mul_comm _ _
  intro v w φ
  have hder (u : Fin n → ℂ) (x : Fin n → ℂ) :
      (TestFunction.lineDerivCLM ℂ u φ : TestFunction Ω ℂ ⊤) x =
        fderiv ℝ (φ : (Fin n → ℂ) → ℂ) x u := by
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    exact (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
  have hpv := hpair w (TestFunction.lineDerivCLM ℂ v φ)
  have hpw := hpair v (TestFunction.lineDerivCLM ℂ w φ)
  simp only [hder] at hpv hpw
  rw [hpv, hpw, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  simpa only [neg_mul] using hcurrent v w φ


theorem native_flatness_of_closed_current
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : Connection U) (hcontinuous : IsContinuous nabla)
    (hcompatible : IsCompatible nabla)
    (hinvariant : IsInvariant nabla f hU) :
    IsFlat nabla := by
  have hclosed := native_pullback_l2_current_closed hd f a hstable U hU_real hU nabla
    hcontinuous hcompatible hinvariant
  intro V e c hc
  let Ω : Opens (ComplexModel d) :=
    ⟨c.target ∩ c.symm ⁻¹' (V : Set X), c.isOpen_inter_preimage_symm V.isOpen⟩
  let A := fun z ↦ coordinateForm nabla e c z
  let coeff := fun j : Fin d ↦ fun z ↦ A z (Pi.single j 1)
  have hcoeff (k : Fin d) : ContinuousOn (coeff k) Ω := by
    exact (hcontinuous V e c hc).clm_apply continuousOn_const
  let T (k : Fin d) : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ :=
    TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) volume (coeff k)
  have hT (k : Fin d) (φ : TestFunction Ω ℂ ⊤) :
      T k φ = DistributionalSection.regularPairing Ω (coeff k) φ := by
    rw [DistributionalSection.regularPairing,
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ by simp [φ.zero_on_compl hz])]
    rw [show (fun z ↦ coeff k z * φ z) = (fun z ↦ φ z * coeff k z) by
      funext z; exact mul_comm _ _]
    exact TestFunction.integralAgainstBilinCLM_eq_integral
      ((hcoeff k).locallyIntegrableOn Ω.isOpen.measurableSet (μ := volume))
  have hcurrent : ∀ (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤),
      (∑ k : Fin d, (-T k (TestFunction.lineDerivCLM ℂ v φ) * w k +
        T k (TestFunction.lineDerivCLM ℂ w φ) * v k)) = 0 := by
    intro v w φ
    simpa only [hT] using hclosed V e c hc v w φ
  have hhol (k : Fin d) : DifferentiableOn ℂ (coeff k) (Ω : Set (ComplexModel d)) := by
    exact continuous_coefficient_holomorphic_of_current Ω (coeff k) (hcoeff k) (T k) (hT k)
      (closed_typeOne_current_dbar_zero Ω T hcurrent k)
  have hsmooth (k : Fin d) : ContDiffOn ℝ ∞ (coeff k) (Ω : Set (ComplexModel d)) := by
    have hcpx : ContDiffOn ℂ ∞ (coeff k) (Ω : Set (ComplexModel d)) :=
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.contDiffOn_of_holomorphic Ω.isOpen (hhol k)
    exact hcpx.restrict_scalars ℝ
  have htype : ∀ z ∈ Ω, ∀ v : ComplexModel d,
      A z (Complex.I • v) = Complex.I * A z v := by
    intro z hz v
    exact native_coordinate_form_type_one U nabla hcompatible V e c hc z (by
      simpa [Ω] using hz) v
  have heval : ∀ z ∈ Ω, ∀ v, A z v = ∑ k : Fin d, v k • coeff k z := by
    intro z hz v
    exact real_linear_type_one_coordinate_sum (A z) (htype z hz) v
  have hA : ContDiffOn ℝ ∞ A (Ω : Set (ComplexModel d)) := by
    exact coordinate_form_real_smooth_current Ω A coeff hsmooth heval
  have hderiv : ∀ z ∈ Ω, ∀ v w : ComplexModel d,
      fderiv ℝ A z v w - fderiv ℝ A z w v = 0 := by
    apply smooth_oneForm_flat_of_weak_closed Ω A hA
    exact finite_current_integration_bridge Ω A hA.continuousOn htype T hT hcurrent
  exact ⟨hA.differentiableOn (by simp), hderiv⟩


theorem native_connection_current_closed_and_flat
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : Connection U) (hcontinuous : IsContinuous nabla)
    (hcompatible : IsCompatible nabla)
    (hinvariant : IsInvariant nabla f hU) :
    (∀ (V : Opens X) (e : HolomorphicFrame U V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      let Ω : Opens (ComplexModel d) :=
        ⟨c.target ∩ c.symm ⁻¹' (V : Set X), c.isOpen_inter_preimage_symm V.isOpen⟩
      ∀ (v w : ComplexModel d) (φ : TestFunction Ω ℂ ⊤),
        (∑ j : Fin d,
          (-DistributionalSection.regularPairing Ω
            (fun z ↦ coordinateForm nabla e c z (Pi.single j 1))
            (TestFunction.lineDerivCLM ℂ v φ) * w j +
          DistributionalSection.regularPairing Ω
            (fun z ↦ coordinateForm nabla e c z (Pi.single j 1))
            (TestFunction.lineDerivCLM ℂ w φ) * v j)) = 0) ∧
      IsFlat nabla := by
  refine ⟨native_pullback_l2_current_closed hd f a hstable U hU_real hU nabla
    hcontinuous hcompatible hinvariant, ?_⟩
  exact native_flatness_of_closed_current hd f a hstable U hU_real hU nabla
    hcontinuous hcompatible hinvariant

end HolomorphicAnosov.ConnectionFlatEstimates

