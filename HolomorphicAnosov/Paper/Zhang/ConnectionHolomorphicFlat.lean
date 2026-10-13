import HolomorphicAnosov.Geometry.NativeSingleBundleFoliationChart
import HolomorphicAnosov.Geometry.SingleBundleNativeHolomorphicBox
import HolomorphicAnosov.Geometry.ComplementaryComplexFrame
import HolomorphicAnosov.Geometry.FirstIntegralOfHolomorphicBox
import HolomorphicAnosov.Geometry.FoliationChartOfHolomorphicBox
import HolomorphicAnosov.Analysis.Distribution.HolomorphicSectionCriterion
import HolomorphicAnosov.Analysis.InnerProductSpace.JacobianSingularValues
import HolomorphicAnosov.Geometry.Manifold.CompactVolumeJacobianIntegral
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import HolomorphicAnosov.Paper.Zhang.InvariantConnection
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.WedgeApplyNormLe
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.CurvatureDecayFactorTendsto
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.WeakLimitTransverseDbar
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ClosedTransverseDbar
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.CurvatureConormJacobian
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.WedgeSumSq
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.SubmoduleRealification
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientsEqOn
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientHolomorphic
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ContinuousCoefficientHolomorphicDbar
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.ClosedTypeOneDbar
import HolomorphicAnosov.Paper.Zhang.ConnectionFlat.SmoothOneFormFlatOfWeakClosed
import HolomorphicAnosov.ConnectionNativeCurrentClosedFlat

/-! Holomorphicity of the unstable bundle and holomorphicity and flatness of the compatible
invariant quotient connection. (Zhang, Lemma 2.3, eqs. (7)–(11)) -/

open scoped Manifold ContDiff Topology _root_.Topology BigOperators
open Filter MeasureTheory TopologicalSpace Set

attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
universe u
namespace HolomorphicAnosov

open QuotientLineConnection

/-- For a holomorphic Anosov diffeomorphism in complex dimension at least three with complex stable
rank one, the unstable bundle is holomorphic and every continuous compatible invariant quotient
connection is holomorphic and flat. (Zhang, Lemma 2.3; Demailly, I (3.29)(a)) -/
theorem lemma_2_3_connection_holomorphic_flat
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x) :
    IsHolomorphicTangentSubbundle (d - 1) U ∧
      ∀ (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
          mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
        (nabla : Connection U),
        IsContinuous nabla → IsCompatible nabla → IsInvariant nabla f hU →
          IsHolomorphic nabla ∧ IsFlat nabla := by
  obtain ⟨P, hP, hP_real⟩ := rank_one_stable_holomorphic_unstable (by omega) f a hstable
  have hPU : P = U := by
    funext x
    exact ConnectionFlatEstimates.submodule_eq_of_realification_eq x (P x) (U x)
      ((hP_real x).trans (hU_real x).symm)
  subst P
  refine ⟨hP, ?_⟩
  intro hU nabla hcontinuous hcompatible hinvariant
  have hline : IsQuotientTangentLine U :=
    quotient_line_of_holomorphic_codimension_one (by omega : 1 ≤ d) U hP
  have hcover := ConnectionCalculus.holomorphic_frame_cover U hP hline
  have hInv := unstable_bott_involutive f a U hU_real
  have hcalculus := ConnectionCalculus.zhang_connection_calculus U hP hline hInv
  
  
  
  suffices hclosed :
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
      IsFlat nabla by
    refine ⟨⟨hcompatible.1, ?_⟩, hclosed.2⟩
    intro V e c hc j
    let Ω : Opens (ComplexModel d) :=
      ⟨c.target ∩ c.symm ⁻¹' (V : Set X), c.isOpen_inter_preimage_symm V.isOpen⟩
    let coeff := fun j : Fin d ↦ fun z ↦ coordinateForm nabla e c z (Pi.single j 1)
    have hcoeff (k : Fin d) : ContinuousOn (coeff k) Ω :=
      (hcontinuous V e c hc).clm_apply continuousOn_const
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
      simpa only [hT] using hclosed.1 V e c hc v w φ
    exact ConnectionFlatEstimates.continuous_coefficient_holomorphic_of_current
      Ω (coeff j) (hcoeff j) (T j) (hT j)
      (ConnectionFlatEstimates.closed_typeOne_current_dbar_zero Ω T hcurrent j)
  
  
  
  
  
  
  
  exact ConnectionFlatEstimates.native_connection_current_closed_and_flat
    hd f a hstable U hU_real hU nabla hcontinuous hcompatible hinvariant



end HolomorphicAnosov




