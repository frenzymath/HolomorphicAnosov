import Mathlib.Topology.Constructions
import HolomorphicAnosov.Geometry.FoliationLeafConstantMFDerivKernel
import HolomorphicAnosov.Geometry.OriginalNativeLiftedHolomorphicFoliations
import HolomorphicAnosov.Geometry.FoliationLeafConstantMFDerivSurjective
import HolomorphicAnosov.Geometry.LiftedIntrinsicLeafRangeHomeomorph
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Topology.DiscreteOrbitLimitFixed
import Mathlib.Analysis.Complex.Norm
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import HolomorphicAnosov.Analysis.ComplexPlaneBiholomorphismAffine
import Mathlib.Analysis.Calculus.MeanValue
import HolomorphicAnosov.Paper.Zhang.FixedPointFreeEntireTranslation
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticApplyIff
import HolomorphicAnosov.Paper.Zhang.StableFoliationsDerivativeScalarRestriction
import Mathlib.Topology.Covering.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.LinearDecay
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Logic.Equiv.Set
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf
import HolomorphicAnosov.Geometry.ComplexSubmersionFixedComplement
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Algebra.Module.Submodule.Map
import HolomorphicAnosov.Dynamics.Anosov.LiftedLeafAffineImage.IntrinsicAffine
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.InverseConjugacy
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacyInverseLattice
import HolomorphicAnosov.Geometry.FoliationProjectionOfTransverseSection
import HolomorphicAnosov.Dynamics.Anosov.FullDecaySubmoduleMapsTo
import HolomorphicAnosov.Analysis.LtOneOfGeometricPowerBound
import HolomorphicAnosov.Targets.Theorem12Support.LiftedToralAssembly
import HolomorphicAnosov.Paper.Zhang.CompleteStableCoordinates
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacy
import HolomorphicAnosov.Paper.Zhang.InvariantConnection
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import HolomorphicAnosov.Targets.Theorem11
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealVectorBundle
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealContMDiffOn
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealTangentSmooth
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealContMDiffOnMap
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalNormComparison
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeStableLeafHolomorphicLift
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeStableLeafCoordinateLift
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CoveringConjugacyLiftedDynamics
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.DifferentialClosedAt
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.ComplexDifferentialClosedOn
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.LocallyExactCovectorClosedAt
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.ProjectionFibreFactorization
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.TranslatedPotentialsSameDifferential
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.StableProjectionFibreIff
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.StableProjectionCommutes
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.StableProjectionConstruction
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.StableProjectionDeckPreservesFibres
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NonzeroDeckFactorFixedPointFree
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.HolomorphicProjectionDeckTranslation
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalMultiplierBounds
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CovectorSectionGluing
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.ScalarDifferentialHolomorphicOn
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.TranslatedNativePotentialsSameCovector
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.InverseSheetsDifferByDeckLocally
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeScalarDifferentialPullback
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.TranslatedLocalPotentialsGlue
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CoveringProjectionHolomorphicForm
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeFormClosedOfLocalPotential
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeScalarDifferentialComp
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.DescendedCovectorNonzeroAndKernel
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.NativeScalarDifferentialEquivariance
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CovectorEquivarianceDescends
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.DescendedFormPullbackOfDeckSheets
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.CoveringProjectionOneFormProperties

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang
attribute [local instance] complex_isManifold_real
universe u

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Assuming homotopy-torus rigidity in real dimensions at least five, a holomorphic Anosov
diffeomorphism of a compact connected complex manifold of dimension at least three with stable
complex rank one admits a nowhere vanishing closed holomorphic one-form `θ` with unstable kernel
and `f*θ = μθ` for `0 < ‖μ‖ < 1`. (Zhang, Lemma 4.2, pp.14–15, (21)–(23), Lemma 2.7, p.9, Lemma
2.4, p.7, Thm 1.1; Ghys, Thm B, p.598; Demailly, I §3.B–C, (3.8)–(3.11), (3.14)–(3.19); Nisoli,
§1.3, pp.21–23, Remark 1.3.2, (1.9)–(1.11); McMullen, Thm 2.2 and Cor. 2.3, p.28) -/
theorem invariant_holomorphic_one_form
    (HS : HomotopyTorusRigidity.{u})
    {d : ℕ} (hd : 3 ≤ d) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution) :
    ∃ (θ : ∀ x : X, TangentSpace (complexModel d) x →L[ℂ] ℂ) (μ : ℂ),
      ContMDiff (complexModel d)
        ((complexModel d).prod 𝓘(ℂ, ComplexModel d →L[ℂ] ℂ)) ∞
        (fun x ↦ (⟨x, θ x⟩ : Bundle.TotalSpace (ComplexModel d →L[ℂ] ℂ)
          (fun y : X ↦ TangentSpace (complexModel d) y →L[ℂ] ℂ))) ∧
      (∀ x : X, θ x ≠ 0) ∧
      (∀ x : X, ∀ z ∈ (chartAt (ComplexModel d) x).target,
        extDeriv (fun w : ComplexModel d ↦
          ContinuousAlternatingMap.ofSubsingleton ℝ (ComplexModel d) ℂ (0 : Fin 1)
            (((θ ((chartAt (ComplexModel d) x).symm w)).comp
              (mfderiv 𝓘(ℂ, ComplexModel d) (complexModel d)
                (chartAt (ComplexModel d) x).symm w)).restrictScalars ℝ)) z = 0) ∧
      (∀ (x : X) (v : TangentSpace (complexModel d) x),
        θ x v = 0 ↔ complexTangentToReal d x v ∈
          a.splitting.unstable.toDistribution x) ∧
      0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧
      (∀ x : X, (θ (f x)).comp (mfderiv (complexModel d) (complexModel d) f x) =
        μ • θ x) := by
  classical
  have hd2 : 2 ≤ d := by omega
  have toral := HolomorphicAnosov.theorem_1_1 hd2 f a hstable HS
  obtain ⟨hΓdiscrete, hΓlattice, hΓspan, hRealDim, hΓcompact,
    A, htorus, hAΓ, hAhyperbolic, htorusConjugacy⟩ :=
    Theorem12LiftedAssembly.lifted_real_toral_model
      (fun x ↦ f x) toral
  let V := Theorem12LiftedCarrier.Carrier.{u} (2 * d)
  let Γ := (IntegerCoordinateLattice.integerLattice (2 * d)).map
    ((Theorem12LiftedCarrier.liftEquiv.{u} (2 * d)).toLinearMap.restrictScalars ℤ)
  let : DiscreteTopology Γ := hΓdiscrete
  let : IsZLattice ℝ Γ := hΓlattice
  let : CompactSpace (V ⧸ Γ.toAddSubgroup) := hΓcompact
  let fixedBasepoint : X := htorus.symm (QuotientAddGroup.mk 0)
  have fixedBasepoint_fixed : f fixedBasepoint = fixedBasepoint := by
    apply htorus.injective
    have heq := htorusConjugacy fixedBasepoint 0
      (htorus.apply_symm_apply (QuotientAddGroup.mk 0)).symm
    simpa only [map_zero, fixedBasepoint, Homeomorph.apply_symm_apply] using heq
  obtain ⟨coverMap, coverMap_covering, coverMap_surjective, coverCharts,
    coverManifold, coverMap_holomorphic, coverSheets, coverConjugacy,
    liftedDynamics, deckAction, coverConjugacy_eq, coverDynamics_eq,
    liftedConjugacy_eq, deckTranslation_eq, deckProjection_eq,
    liftedFixedPoint_eq, projectedFixedPoint_eq, coverFibre_eq, coverDeckTransitive⟩ :=
    covering_conjugacy_lifted_dynamics f a hRealDim Γ A hAhyperbolic hAΓ
      htorus htorusConjugacy
  let : ChartedSpace (ComplexModel d) V := coverCharts
  let : IsManifold (complexModel d) ∞ V := coverManifold
  have liftedBasepoint_projects : coverMap (coverConjugacy.symm 0) = fixedBasepoint := by
    apply htorus.injective
    rw [← coverConjugacy_eq, coverConjugacy.apply_symm_apply]
    exact (htorus.apply_symm_apply _).symm
  obtain ⟨U, hU_hol, hU_real⟩ :=
    rank_one_stable_holomorphic_unstable hd2 f a hstable
  obtain ⟨_, hU, nabla, hn_cont, hn_compat, hn_inv, hn_unique, hn_limit⟩ :=
    lemma_2_2_invariant_connection hd f a hstable U hU_real hU_hol
  have hlocal := transverse_parallel_coordinates hd X f a hstable U
    hU_real hU nabla hn_cont hn_compat hn_inv
  obtain ⟨originalHermitianMetric, originalHermitianSmooth⟩ :=
    OneFormBundle.original_smooth_tangent_metric_exists (d := d) (M := X)
  let : TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace (realModel d) X
  let : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨originalC, originalRate, originalC_pos, originalRate_bounds,
    originalStableEstimate, originalUnstableEstimate⟩ :=
    OneFormBundle.original_all_iterates_hermitian f a originalHermitianMetric
      originalHermitianSmooth
  have sourceNativeComplex := stableFoliations f originalHermitianMetric
    originalHermitianSmooth a.splitting originalC originalRate originalC_pos
    originalRate_bounds originalStableEstimate originalUnstableEstimate
  rcases sourceNativeComplex with ⟨s, t, hst, S, sourceU, hranks, hSr, hUr, hfamily⟩
  have hs1 : s = 1 := by
    let x : X := Classical.arbitrary X
    obtain ⟨K, hK, hKreal⟩ := hstable x
    have hSK : S.toDistribution x = K := by
      apply Submodule.restrictScalars_injective ℝ ℂ _
      apply Submodule.map_injective_of_injective (complexTangentToReal d x).injective
      exact (hSr x).trans hKreal.symm
    rw [← (hranks x).1, hSK]
    exact hK
  subst s
  rcases hfamily with ⟨ιs, ιu, Ls, Lu, ts, tu, hfamily⟩
  let : ∀ i, TopologicalSpace (Ls i) := ts
  let : ∀ i, TopologicalSpace (Lu i) := tu
  rcases hfamily with ⟨cs, cu, hfamily⟩
  let : ∀ i, ChartedSpace (Fin (2*1) → ℝ) (Ls i) := cs
  let : ∀ i, ChartedSpace (Fin (2*t) → ℝ) (Lu i) := cu
  rcases hfamily with ⟨ms, mu, Fs, Fu, hstableAsymptotic, hunstableAsymptotic,
    hstableEuclidean, hunstableEuclidean, hstableAction, hunstableAction,
    hboxes, hproducts, hstableJets, hunstableJets, hstableComplex, hunstableComplex⟩
  let : ∀ i, IsManifold 𝓘(ℝ, Fin (2*1) → ℝ) ∞ (Ls i) := ms
  let : ∀ i, IsManifold 𝓘(ℝ, Fin (2*t) → ℝ) ∞ (Lu i) := mu
  have nativeUnstablePointedData (x : X) :
      ∃ N : NativeAsymptoticLeafDatum (realModel d) f.toHomeomorph.symm
          a.splitting.unstable.toDistribution x,
        N.rank = 2 * t ∧
        (letI := N.topology
         ∃ (i : ιu) (a₀ : Lu i)
           (e : Lu i ≃ₜ StableAsymptoticLeaf f.toHomeomorph.symm x),
           (Fu.leaf i).inclusion a₀ = x ∧
           (∀ z, (e z).val = (Fu.leaf i).inclusion z) ∧ (e a₀).val = x) := by
    obtain ⟨i, a₀, ha₀⟩ := Fu.cover x
    have hrange : Set.range (Fu.leaf i).inclusion =
        {y | ForwardAsymptotic f.toHomeomorph.symm x y} := by
      simpa only [ha₀, Diffeomorph.coe_toHomeomorph_symm] using hunstableAsymptotic i a₀
    obtain ⟨N, hN, he⟩ := native_asymptotic_datum_of_leaf_g15
      a.splitting.unstable.toDistribution (Fu.leaf i) f.toHomeomorph.symm x hrange
    refine ⟨N, hN, ?_⟩
    let := N.topology
    let := N.charts
    obtain ⟨e, he⟩ := he
    exact ⟨i, a₀, e.toHomeomorph, ha₀, he, (he a₀).trans ha₀⟩
  choose nativeUnstableDatum nativeUnstableRank nativeUnstableComparison
    using nativeUnstablePointedData
  have hSrfun : complexStableRealDistribution S = a.splitting.stable.toDistribution :=
    funext hSr
  have nativeStableDatum : Nonempty (NativeComplexStableLeafDatum f.toHomeomorph S ιs Ls) := by
    generalize hP : a.splitting.stable.toDistribution = P at Fs hstableAsymptotic hstableComplex hboxes hstableJets
    have hPS : P = complexStableRealDistribution S := hP.symm.trans hSrfun.symm
    clear hP
    subst P
    rcases hboxes with ⟨βs, βu, Ts, Tu, tts, ttu, ⟨Bs⟩, ⟨Bu⟩⟩
    let : ∀ b, TopologicalSpace (Ts b) := tts
    let : ∀ b, TopologicalSpace (Tu b) := ttu
    have hupgrade : ∀ i, ∃ up : NativeLeafComplexUpgrade (d := d) (r := 2) 1
        (Fs.leaf i).inclusion,
        letI := up.charts
        ∀ z : Ls i, (mfderiv (complexModel 1) (complexModel d)
          (Fs.leaf i).inclusion z).range = S.toDistribution ((Fs.leaf i).inclusion z) := by
      intro i
      rcases hstableComplex i with ⟨c, hm, him, up, hc, htangent⟩
      subst c
      exact ⟨up, htangent⟩
    choose upgrade tangent using hupgrade
    refine ⟨{ partition := Fs
              complexUpgrade := upgrade
              asymptotic := hstableAsymptotic
              complex_tangent := ?_
              boxIndex := βs
              transversal := Ts
              transversalTopology := tts
              boxes := Bs
              local_first_jets := hstableJets }⟩
    intro i
    exact tangent i
  obtain ⟨nativeStable⟩ := nativeStableDatum
  obtain ⟨fixedLeafIndex, fixedLeafPoint, fixedLeafBasepoint⟩ :=
    nativeStable.partition.cover fixedBasepoint
  have coordinates := complete_stable_coordinates hd X f a hstable S hSr U hU_real
    hU nabla hn_cont hn_compat hn_inv ιs Ls nativeStable
  let : ∀ i, ChartedSpace (ComplexModel 1) (Ls i) :=
    fun i ↦ (nativeStable.complexUpgrade i).charts
  let : ∀ x : X, NormedAddCommGroup (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedAddCommGroup (ComplexModel d))
  let : ∀ x : X, NormedSpace ℂ (TangentSpace (complexModel d) x) :=
    fun _ ↦ inferInstanceAs (NormedSpace ℂ (ComplexModel d))
  obtain ⟨φ, K, D, e, hφzero, hφderiv, hφgerm, hφlocal, hφiterate,
    hφequivariant, heinverse, hecontinuous, hφcontinuous⟩ := coordinates
  have hnativeEuclidean (i : ιs) : Nonempty ((Fin 2 → ℝ) ≃ₜ Ls i) := by
    obtain ⟨e⟩ := hstableEuclidean i
    exact ⟨e.toHomeomorph⟩
  let : ∀ x : X, NormedSpace ℂ (S.toDistribution x) :=
    fun x ↦ Submodule.normedSpace (S.toDistribution x)
  let stableScalarCoordinate :
      S.toDistribution ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
        ≃L[ℂ] ℂ :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [(hranks _).1]
      simp)
  let fixedVectorCoordinate : Diffeomorph (complexModel 1)
      𝓘(ℂ, S.toDistribution
        ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint))
      (Ls fixedLeafIndex)
      (S.toDistribution ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint))
      ∞ := φ fixedLeafIndex fixedLeafPoint
  let fixedLeafCoordinate : Diffeomorph (complexModel 1) 𝓘(ℂ, ℂ)
      (Ls fixedLeafIndex) ℂ ∞ :=
    fixedVectorCoordinate.trans stableScalarCoordinate.toDiffeomorph
  have fixedLeafCoordinate_zero : fixedLeafCoordinate fixedLeafPoint = 0 := by
    change stableScalarCoordinate (φ fixedLeafIndex fixedLeafPoint fixedLeafPoint) = 0
    rw [hφzero, map_zero]
  let fixedLeafParametrization : ℂ → X :=
    (nativeStable.partition.leaf fixedLeafIndex).inclusion ∘ fixedLeafCoordinate.symm
  have fixedLeafParametrization_holomorphic :
      ContMDiff 𝓘(ℂ, ℂ) (complexModel d) ∞ fixedLeafParametrization :=
    (nativeStable.complexUpgrade fixedLeafIndex).inclusion_holomorphic.comp
      fixedLeafCoordinate.symm.contMDiff
  have fixedLeafParametrization_injective : Function.Injective fixedLeafParametrization :=
    (nativeStable.partition.leaf fixedLeafIndex).injective.comp
      fixedLeafCoordinate.symm.injective
  have fixedLeafParametrization_zero : fixedLeafParametrization 0 = fixedBasepoint := by
    change (nativeStable.partition.leaf fixedLeafIndex).inclusion
      (fixedLeafCoordinate.symm 0) = fixedBasepoint
    rw [← fixedLeafCoordinate_zero, fixedLeafCoordinate.symm_apply_apply]
    exact fixedLeafBasepoint
  have fixedLeafParametrization_range : Set.range fixedLeafParametrization =
      {y : X | ForwardAsymptotic f.toHomeomorph fixedBasepoint y} := by
    have hsurj : Function.Surjective (fixedLeafCoordinate.symm : ℂ → Ls fixedLeafIndex) :=
      fixedLeafCoordinate.symm.surjective
    change Set.range ((nativeStable.partition.leaf fixedLeafIndex).inclusion ∘
      (fixedLeafCoordinate.symm : ℂ → Ls fixedLeafIndex)) = _
    rw [hsurj.range_comp, nativeStable.asymptotic fixedLeafIndex fixedLeafPoint,
      fixedLeafBasepoint]
  have fixedLeaf_forward (z : ℂ) :
      ∃ w : ℂ, fixedLeafParametrization w = f (fixedLeafParametrization z) := by
    apply Set.mem_range.mp
    rw [fixedLeafParametrization_range]
    have hz : ForwardAsymptotic f.toHomeomorph fixedBasepoint
        (fixedLeafParametrization z) := by
      have hz := Set.mem_range_self (f := fixedLeafParametrization) z
      rw [fixedLeafParametrization_range] at hz
      exact hz
    change ForwardAsymptotic f.toHomeomorph fixedBasepoint (f (fixedLeafParametrization z))
    rw [← fixedBasepoint_fixed]
    exact (StableFoliationsSupport.forwardAsymptotic_apply_iff
      (f.toHomeomorph : X → X) fixedBasepoint (fixedLeafParametrization z)).mpr hz
  choose fixedLeafDynamics fixedLeafDynamics_eq using fixedLeaf_forward
  have fixedLeafDynamics_zero : fixedLeafDynamics 0 = 0 := by
    apply fixedLeafParametrization_injective
    rw [fixedLeafDynamics_eq, fixedLeafParametrization_zero, fixedBasepoint_fixed]
  have fixedLeafDynamics_derivative (z : ℂ) :
      (stableScalarCoordinate.symm (fixedLeafDynamics z)).val =
        mfderiv (complexModel d) (complexModel d) f
          ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
          (stableScalarCoordinate.symm z).val := by
    have heq := hφequivariant fixedLeafIndex fixedLeafIndex
      fixedLeafPoint (fixedLeafCoordinate.symm z)
      fixedLeafPoint (fixedLeafCoordinate.symm (fixedLeafDynamics z))
      (by change (nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint =
          f ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
          rw [fixedLeafBasepoint, fixedBasepoint_fixed]) (fixedLeafDynamics_eq z)
    change (fixedVectorCoordinate
      (fixedVectorCoordinate.symm (stableScalarCoordinate.symm (fixedLeafDynamics z)))).val =
      mfderiv (complexModel d) (complexModel d) f
        ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
        (fixedVectorCoordinate (fixedVectorCoordinate.symm
          (stableScalarCoordinate.symm z))).val at heq
    simpa only [Diffeomorph.apply_symm_apply] using heq
  let stableMultiplier : ℂ := fixedLeafDynamics 1
  have fixedLeafDynamics_scalar (z : ℂ) : fixedLeafDynamics z = stableMultiplier * z := by
    apply stableScalarCoordinate.symm.injective
    apply Subtype.ext
    have hz : stableScalarCoordinate.symm z = z • stableScalarCoordinate.symm 1 := by
      rw [← map_smul]
      simp
    rw [fixedLeafDynamics_derivative, hz]
    change mfderiv (complexModel d) (complexModel d) f
      ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
      (z • (stableScalarCoordinate.symm 1).val) = _
    rw [map_smul, ← fixedLeafDynamics_derivative 1]
    change (z • stableScalarCoordinate.symm stableMultiplier).val =
      (stableScalarCoordinate.symm (stableMultiplier * z)).val
    rw [← map_smul]
    congr 2
    simp [mul_comm]
  have fixedLeafParametrization_equivariant (z : ℂ) :
      fixedLeafParametrization (stableMultiplier * z) = f (fixedLeafParametrization z) := by
    rw [← fixedLeafDynamics_scalar]
    exact fixedLeafDynamics_eq z
  have stableMultiplier_ne_zero : stableMultiplier ≠ 0 := by
    intro hzero
    have heq := fixedLeafParametrization_equivariant 1
    rw [hzero, zero_mul, fixedLeafParametrization_zero] at heq
    have hone : fixedLeafParametrization 1 = fixedLeafParametrization 0 := by
      apply f.injective
      change f (fixedLeafParametrization 1) = f (fixedLeafParametrization 0)
      rw [fixedLeafParametrization_zero, fixedBasepoint_fixed]
      exact heq.symm
    exact one_ne_zero (fixedLeafParametrization_injective hone)
  let fixedTangentVector : TangentSpace (complexModel d)
      ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint) :=
    (stableScalarCoordinate.symm 1).val
  have fixedTangentVector_ne_zero : fixedTangentVector ≠ 0 := by
    intro hz
    have hsub : stableScalarCoordinate.symm 1 = 0 := Subtype.ext hz
    have heq := congrArg stableScalarCoordinate hsub
    simp at heq
  have fixedTangentVector_eigen :
      mfderiv (complexModel d) (complexModel d) f
        ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
        fixedTangentVector = stableMultiplier • fixedTangentVector := by
    rw [← fixedLeafDynamics_derivative 1, fixedLeafDynamics_scalar, mul_one]
    change (stableScalarCoordinate.symm stableMultiplier).val =
      (stableMultiplier • stableScalarCoordinate.symm 1).val
    rw [← map_smul]
    simp
  have fixedLeafPoint_fixed :
      f ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint) =
        (nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint := by
    rw [fixedLeafBasepoint, fixedBasepoint_fixed]
  have fixedTangentVector_iterate (n : ℕ) :
      mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n])
        ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
        fixedTangentVector = stableMultiplier ^ n • fixedTangentVector := by
    induction n with
    | zero =>
      simp only [Function.iterate_zero, mfderiv_id, pow_zero, one_smul]
      rfl
    | succ n ih =>
      rw [Function.iterate_succ, mfderiv_comp _
        ((f.contMDiff.iterate n).mdifferentiableAt (by simp))
        (f.contMDiff.mdifferentiableAt (by simp))]
      change (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n])
        (f ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)))
        ((mfderiv (complexModel d) (complexModel d) f
          ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint))
          fixedTangentVector) = _
      erw [fixedLeafPoint_fixed]
      erw [fixedTangentVector_eigen]
      rw [map_smul, ih]
      rw [smul_smul, pow_succ']
  have fixedTangentVector_hermitian_bound (n : ℕ) :
      Real.sqrt ((originalHermitianMetric
        ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)).inner
          (stableMultiplier ^ n • fixedTangentVector)
          (stableMultiplier ^ n • fixedTangentVector)).re ≤
        originalC * originalRate ^ n * Real.sqrt ((originalHermitianMetric
          ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)).inner
            fixedTangentVector fixedTangentVector).re := by
    let x := (nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint
    have hv : complexTangentToReal d x fixedTangentVector ∈
        a.splitting.stable.toDistribution x := by
      rw [← hSr x]
      exact Submodule.mem_map_of_mem (stableScalarCoordinate.symm 1).property
    have hb := originalStableEstimate n x (complexTangentToReal d x fixedTangentVector) hv
    have hd := StableFoliationsSupport.derivative_scalar_restriction ((f : X → X)^[n]) x
      ((f.contMDiff.iterate n).mdifferentiableAt (by simp))
      ((f.toReal.contMDiff.iterate n).mdifferentiableAt (by simp))
    rw [hd] at hb
    have hfn : (f : X → X)^[n] x = x := Function.iterate_fixed fixedLeafPoint_fixed n
    erw [hfn] at hb
    change Real.sqrt ((originalHermitianMetric x).inner
      (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x fixedTangentVector)
      (mfderiv (complexModel d) (complexModel d) ((f : X → X)^[n]) x fixedTangentVector)).re ≤
      originalC * originalRate ^ n * Real.sqrt
        ((originalHermitianMetric x).inner fixedTangentVector fixedTangentVector).re at hb
    rw [fixedTangentVector_iterate] at hb
    exact hb
  let fixedHermitianCore := originalHermitianMetric
    ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)
  let fixedHermitianLength : ℝ :=
    Real.sqrt (fixedHermitianCore.inner fixedTangentVector fixedTangentVector).re
  have fixedHermitianLength_pos : 0 < fixedHermitianLength := by
    let : InnerProductSpace.Core ℂ _ := fixedHermitianCore
    let : Norm (TangentSpace (complexModel d)
        ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)) :=
      InnerProductSpace.Core.toNorm (𝕜 := ℂ)
    have hzero := fixedHermitianCore.toNormedSpaceCore.norm_eq_zero_iff fixedTangentVector
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm (hzero.not.mpr fixedTangentVector_ne_zero))
  have stableMultiplier_power_bound (n : ℕ) :
      ‖stableMultiplier‖ ^ n ≤ originalC * originalRate ^ n := by
    have hb := fixedTangentVector_hermitian_bound n
    have hhom : Real.sqrt (fixedHermitianCore.inner
        (stableMultiplier ^ n • fixedTangentVector)
        (stableMultiplier ^ n • fixedTangentVector)).re =
        ‖stableMultiplier ^ n‖ * fixedHermitianLength := by
      let : InnerProductSpace.Core ℂ _ := fixedHermitianCore
      let : Norm (TangentSpace (complexModel d)
          ((nativeStable.partition.leaf fixedLeafIndex).inclusion fixedLeafPoint)) :=
        InnerProductSpace.Core.toNorm (𝕜 := ℂ)
      exact fixedHermitianCore.toNormedSpaceCore.norm_smul _ _
    rw [hhom, norm_pow] at hb
    exact (mul_le_mul_iff_left₀ fixedHermitianLength_pos).mp hb
  have stableMultiplier_norm_lt_one : ‖stableMultiplier‖ < 1 :=
    lt_one_of_geometric_power_bound ‖stableMultiplier‖ originalC originalRate
      originalRate_bounds.1.le originalRate_bounds.2 stableMultiplier_power_bound
  obtain ⟨liftedStableParametrization, liftedStableParametrization_holomorphic,
    liftedStableParametrization_injective, liftedStableParametrization_zero,
    liftedStableParametrization_projects, liftedStableParametrization_range⟩ :=
    native_stable_leaf_coordinate_lift f.toHomeomorph S ιs Ls nativeStable
      coverMap coverMap_covering coverSheets fixedLeafIndex fixedLeafPoint
      (coverConjugacy.symm 0)
      (liftedBasepoint_projects.trans fixedLeafBasepoint.symm)
      (hnativeEuclidean fixedLeafIndex) ℂ fixedLeafCoordinate fixedLeafCoordinate_zero
  have liftedStableParametrization_projection (z : ℂ) :
      coverMap (liftedStableParametrization z) = fixedLeafParametrization z :=
    liftedStableParametrization_projects z
  have liftedStableParametrization_equivariant (z : ℂ) :
      liftedDynamics (liftedStableParametrization z) =
        liftedStableParametrization (stableMultiplier * z) := by
    have hlift : (fun w : ℂ ↦ liftedDynamics (liftedStableParametrization w)) =
        (fun w : ℂ ↦ liftedStableParametrization (stableMultiplier * w)) := by
      refine coverMap_covering.eq_of_comp_eq
        (liftedDynamics.continuous.comp liftedStableParametrization_holomorphic.continuous)
        (liftedStableParametrization_holomorphic.continuous.comp
          (continuous_const.mul continuous_id)) ?_ 0 ?_
      · funext w
        simp only [Function.comp_apply, coverDynamics_eq,
          liftedStableParametrization_projection]
        exact (fixedLeafParametrization_equivariant w).symm
      · simp only [mul_zero, liftedStableParametrization_zero,
          liftedFixedPoint_eq]
    exact congrFun hlift z
  have liftedStableParametrization_iterate (n : ℕ) (z : ℂ) :
      (liftedDynamics^[n]) (liftedStableParametrization z) =
        liftedStableParametrization (stableMultiplier ^ n * z) := by
    induction n with
    | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, liftedStableParametrization_equivariant]
      congr 1
      ring
  have liftedStableParametrization_contracts (z : ℂ) :
      Filter.Tendsto (fun n : ℕ ↦ (liftedDynamics^[n]) (liftedStableParametrization z))
        Filter.atTop (𝓝 (coverConjugacy.symm 0)) := by
    have hscalar : Filter.Tendsto (fun n : ℕ ↦ stableMultiplier ^ n * z)
        Filter.atTop (𝓝 (0 : ℂ)) := by
      simpa only [zero_mul] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one stableMultiplier_norm_lt_one).mul_const z
    simpa only [Function.comp_def, liftedStableParametrization_iterate,
      liftedStableParametrization_zero] using
      liftedStableParametrization_holomorphic.continuous.continuousAt.tendsto.comp hscalar
  let : SimplyConnectedSpace (Ls fixedLeafIndex) :=
    (hnativeEuclidean fixedLeafIndex).some.symm.toHomotopyEquiv.simplyConnectedSpace
  have liftedStableParametrization_affine :
      coverConjugacy '' Set.range liftedStableParametrization =
        (fullDecaySubmodule A : Set V) := by
    have hleaf := intrinsic_affine Γ A hAΓ f.toHomeomorph htorus htorusConjugacy
      coverMap coverMap_covering coverConjugacy coverConjugacy_eq
      (coverConjugacy.symm 0) (nativeStable.partition.leaf fixedLeafIndex).inclusion
      (nativeStable.complexUpgrade fixedLeafIndex).inclusion_holomorphic.continuous
      fixedLeafPoint (fixedLeafBasepoint.trans liftedBasepoint_projects.symm)
      (fun w ↦ ?_) (fun x hx ↦ ?_)
    · rw [liftedStableParametrization_range]
      simpa only [Homeomorph.apply_symm_apply, zero_add, Set.image_id'] using hleaf.1
    · rw [liftedBasepoint_projects]
      have hw : (nativeStable.partition.leaf fixedLeafIndex).inclusion w ∈
          Set.range fixedLeafParametrization :=
        ⟨fixedLeafCoordinate w, by simp only [fixedLeafParametrization, Function.comp_apply,
          Diffeomorph.symm_apply_apply]⟩
      rwa [fixedLeafParametrization_range] at hw
    · rw [liftedBasepoint_projects] at hx
      have hx' : x ∈ Set.range fixedLeafParametrization := by
        rwa [fixedLeafParametrization_range]
      obtain ⟨z, rfl⟩ := hx'
      exact ⟨fixedLeafCoordinate.symm z, rfl⟩
  let stablePlaneParametrization : ℂ → fullDecaySubmodule A := fun z ↦
    ⟨coverConjugacy (liftedStableParametrization z), by
      change coverConjugacy (liftedStableParametrization z) ∈ (fullDecaySubmodule A : Set V)
      rw [← liftedStableParametrization_affine]
      exact Set.mem_image_of_mem coverConjugacy (Set.mem_range_self z)⟩
  have stablePlaneParametrization_bijective : Function.Bijective stablePlaneParametrization := by
    constructor
    · intro z w heq
      exact liftedStableParametrization_injective
        (coverConjugacy.injective (congrArg Subtype.val heq))
    · intro v
      have hv : (v : V) ∈ coverConjugacy '' Set.range liftedStableParametrization :=
        liftedStableParametrization_affine.symm ▸ v.property
      obtain ⟨y, ⟨z, rfl⟩, hz⟩ := hv
      exact ⟨z, Subtype.ext hz⟩
  let stablePlaneCoordinate : fullDecaySubmodule A ≃ ℂ :=
    (Equiv.ofBijective stablePlaneParametrization stablePlaneParametrization_bijective).symm
  have stableUnstablePlanes_complementary :
      IsCompl (fullDecaySubmodule A) (fullDecaySubmodule A.symm) := by
    obtain ⟨Vs, Vu, hVs, hVu, hcompl⟩ := covering_conjugacy_linear_decay_g15 A hAhyperbolic
    have hVs' : Vs = fullDecaySubmodule A := SetLike.coe_injective hVs
    have hVu' : Vu = fullDecaySubmodule A.symm := SetLike.coe_injective hVu
    simpa only [hVs', hVu'] using hcompl
  have stablePlane_invariant : ∀ v ∈ fullDecaySubmodule A, A v ∈ fullDecaySubmodule A :=
    fullDecaySubmodule_mapsTo_of_commute A A.toContinuousLinearMap (Function.Commute.refl _)
  have unstablePlane_invariant : ∀ v ∈ fullDecaySubmodule A.symm,
      A v ∈ fullDecaySubmodule A.symm :=
    fullDecaySubmodule_mapsTo_of_commute A.symm A.toContinuousLinearMap
      (by intro v; simp only [ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply])
  have stablePlaneCoordinate_equivariant (v : fullDecaySubmodule A) :
      stablePlaneCoordinate ⟨A v, stablePlane_invariant _ v.property⟩ =
        stableMultiplier * stablePlaneCoordinate v := by
    apply stablePlaneCoordinate.symm.injective
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    change A v = coverConjugacy
      (liftedStableParametrization (stableMultiplier * stablePlaneCoordinate v))
    rw [← liftedStableParametrization_equivariant, liftedConjugacy_eq]
    exact congrArg A (congrArg Subtype.val (stablePlaneCoordinate.symm_apply_apply v)).symm
  obtain ⟨globalStableProjection, globalStableSection, globalStableProjection_formula,
    globalStableSection_formula, globalStableProjection_section, globalStableProjection_surjective,
    globalStableProjection_fibres, globalStableProjection_equivariant⟩ :=
    stable_projection_construction (fullDecaySubmodule A) (fullDecaySubmodule A.symm)
      stableUnstablePlanes_complementary coverConjugacy.toEquiv stablePlaneCoordinate
      A.toLinearEquiv.toLinearMap liftedDynamics stableMultiplier
      stablePlane_invariant unstablePlane_invariant liftedConjugacy_eq
      stablePlaneCoordinate_equivariant
  have globalStableSection_eq (z : ℂ) :
      globalStableSection z = liftedStableParametrization z := by
    rw [globalStableSection_formula]
    change coverConjugacy.symm (coverConjugacy (liftedStableParametrization z)) = _
    exact coverConjugacy.symm_apply_apply _
  have globalStableProjection_liftedCoordinate (z : ℂ) :
      globalStableProjection (liftedStableParametrization z) = z := by
    rw [← globalStableSection_eq]
    exact globalStableProjection_section z
  have fixedLeafParametrization_mfderiv_injective (z : ℂ) :
      Function.Injective (mfderiv 𝓘(ℂ, ℂ) (complexModel d) fixedLeafParametrization z) := by
    have hbij : Function.Bijective (mfderiv 𝓘(ℂ, ℂ) (complexModel 1)
        fixedLeafCoordinate.symm z) := by
      rw [← fixedLeafCoordinate.symm.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact ContinuousLinearEquiv.bijective _
    change Function.Injective (mfderiv 𝓘(ℂ, ℂ) (complexModel d)
      ((nativeStable.partition.leaf fixedLeafIndex).inclusion ∘ fixedLeafCoordinate.symm) z)
    rw [mfderiv_comp z
      ((nativeStable.complexUpgrade fixedLeafIndex).inclusion_holomorphic.mdifferentiableAt
        (by simp)) (fixedLeafCoordinate.symm.contMDiff.mdifferentiableAt (by simp))]
    exact ((nativeStable.complexUpgrade fixedLeafIndex).inclusion_immersion
      (fixedLeafCoordinate.symm z)).mfderiv_injective (by simp) |>.comp hbij.1
  have liftedStableParametrization_mfderiv_injective (z : ℂ) :
      Function.Injective (mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization z) := by
    have hchain := mfderiv_comp z
      (coverMap_holomorphic.mdifferentiableAt (by simp))
      (liftedStableParametrization_holomorphic.mdifferentiableAt (by simp))
    have hproj : coverMap ∘ liftedStableParametrization = fixedLeafParametrization :=
      funext liftedStableParametrization_projection
    rw [hproj] at hchain
    have hi := fixedLeafParametrization_mfderiv_injective z
    rw [hchain] at hi
    exact Function.Injective.of_comp hi
  have fixedLeafParametrization_mfderiv_range (z : ℂ) :
      (mfderiv 𝓘(ℂ, ℂ) (complexModel d) fixedLeafParametrization z).range =
        S.toDistribution (fixedLeafParametrization z) := by
    have hbij : Function.Bijective (mfderiv 𝓘(ℂ, ℂ) (complexModel 1)
        fixedLeafCoordinate.symm z) := by
      rw [← fixedLeafCoordinate.symm.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact ContinuousLinearEquiv.bijective _
    change (mfderiv 𝓘(ℂ, ℂ) (complexModel d)
      ((nativeStable.partition.leaf fixedLeafIndex).inclusion ∘ fixedLeafCoordinate.symm) z).range = _
    rw [mfderiv_comp z
      ((nativeStable.complexUpgrade fixedLeafIndex).inclusion_holomorphic.mdifferentiableAt
        (by simp)) (fixedLeafCoordinate.symm.contMDiff.mdifferentiableAt (by simp))]
    change LinearMap.range (_ ∘ₗ _) = _
    rw [LinearMap.range_comp]
    have hrange : (mfderiv 𝓘(ℂ, ℂ) (complexModel 1) fixedLeafCoordinate.symm z).range = ⊤ :=
      LinearMap.range_eq_top.mpr hbij.2
    rw [hrange, Submodule.map_top]
    exact nativeStable.complex_tangent fixedLeafIndex (fixedLeafCoordinate.symm z)
  have liftedStableParametrization_tangent_projects (z : ℂ) :
      ((mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization z).range).map
        (mfderiv (complexModel d) (complexModel d) coverMap
          (liftedStableParametrization z)).toLinearMap =
        S.toDistribution (coverMap (liftedStableParametrization z)) := by
    have hchain := mfderiv_comp z
      (coverMap_holomorphic.mdifferentiableAt (by simp))
      (liftedStableParametrization_holomorphic.mdifferentiableAt (by simp))
    have hproj : coverMap ∘ liftedStableParametrization = fixedLeafParametrization :=
      funext liftedStableParametrization_projection
    rw [hproj] at hchain
    have hrange := congrArg (fun D : ℂ →L[ℂ] ComplexModel d ↦ D.range) hchain
    change _ = LinearMap.range (_ ∘ₗ _) at hrange
    rw [LinearMap.range_comp] at hrange
    rw [← hrange, fixedLeafParametrization_mfderiv_range,
      liftedStableParametrization_projection]
  have original_complex_stable_unstable_disjoint (x : X) :
      Disjoint (S.toDistribution x) (U x) := by
    apply disjoint_iff_inf_le.mpr
    intro v hv
    have hs : complexTangentToReal d x v ∈ a.splitting.stable.toDistribution x := by
      rw [← hSr x]
      exact ⟨v, hv.1, rfl⟩
    have hu : complexTangentToReal d x v ∈ a.splitting.unstable.toDistribution x := by
      rw [← hU_real x]
      exact ⟨v, hv.2, rfl⟩
    have hzero : complexTangentToReal d x v = 0 :=
      (disjoint_iff_inf_le.mp (a.splitting.isCompl x).disjoint) ⟨hs, hu⟩
    exact (complexTangentToReal d x).injective (by simpa only [map_zero] using hzero)
  have liftedStableParametrization_tangent_disjoint (z : ℂ) :
      Disjoint (mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization z).range
        ((U (coverMap (liftedStableParametrization z))).comap
          (mfderiv (complexModel d) (complexModel d) coverMap
            (liftedStableParametrization z)).toLinearMap) := by
    apply disjoint_iff_inf_le.mpr
    rintro w ⟨⟨v, rfl⟩, hu⟩
    let Dp := mfderiv (complexModel d) (complexModel d) coverMap (liftedStableParametrization z)
    let Di := mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization z
    have hs : Dp (Di v) ∈ S.toDistribution (coverMap (liftedStableParametrization z)) := by
      rw [← liftedStableParametrization_tangent_projects z]
      exact ⟨Di v, ⟨v, rfl⟩, rfl⟩
    have hzero : Dp (Di v) = 0 :=
      (disjoint_iff_inf_le.mp (original_complex_stable_unstable_disjoint _)) ⟨hs, hu⟩
    have hchain := mfderiv_comp z
      (coverMap_holomorphic.mdifferentiableAt (by simp))
      (liftedStableParametrization_holomorphic.mdifferentiableAt (by simp))
    have hproj : coverMap ∘ liftedStableParametrization = fixedLeafParametrization :=
      funext liftedStableParametrization_projection
    rw [hproj] at hchain
    have hdown : mfderiv 𝓘(ℂ, ℂ) (complexModel d) fixedLeafParametrization z v = 0 := by
      rw [hchain]
      exact hzero
    have hv : v = 0 := (fixedLeafParametrization_mfderiv_injective z)
      (by simpa only [map_zero] using hdown)
    simpa only [hv, map_zero] using (show (0 : ComplexModel d) ∈ (⊥ : Submodule ℂ _) from
      Submodule.zero_mem _)
  have globalStableProjection_holomorphic_of_native_foliation
      (Fu : RegularHolomorphicFoliation.{u,u} d (d - 1) 1 V)
      (hfibres : ∀ y w, Fu.partition y w ↔ globalStableProjection y = globalStableProjection w)
      (htangent : ∀ y, Fu.tangent y = (U (coverMap y)).comap
        (mfderiv (complexModel d) (complexModel d) coverMap y).toLinearMap) :
      ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ globalStableProjection := by
    let e : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
    have hehol : ContMDiff (complexModel 1) 𝓘(ℂ, ℂ) ∞ e := e.contDiff.contMDiff
    let qModel : V → ComplexModel 1 := e.symm ∘ globalStableProjection
    let τ : ComplexModel 1 → V := liftedStableParametrization ∘ e
    have hτ : ContMDiff (complexModel 1) (complexModel d) ∞ τ :=
      liftedStableParametrization_holomorphic.comp hehol
    have hτder (z : ComplexModel 1) :
        mfderiv (complexModel 1) (complexModel d) τ z =
          (mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization (e z)).comp
            e.toContinuousLinearMap := by
      rw [mfderiv_comp z
        (liftedStableParametrization_holomorphic.mdifferentiableAt (by simp))
        (hehol.mdifferentiableAt (by simp))]
      simp only [mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
    have hqModel : ContMDiff (complexModel d) (complexModel 1) ∞ qModel := by
      apply foliation_projection_of_transverse_section Fu qModel τ
      · intro y w
        exact (hfibres y w).trans e.symm.injective.eq_iff.symm
      · intro z
        change e.symm (globalStableProjection (liftedStableParametrization (e z))) = z
        rw [globalStableProjection_liftedCoordinate, e.symm_apply_apply]
      · exact hτ
      · intro z
        rw [hτder]
        exact (liftedStableParametrization_mfderiv_injective (e z)).comp e.injective
      · intro z
        rw [hτder, htangent]
        have hrange :
            ((mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization (e z)).comp
              e.toContinuousLinearMap).range =
            (mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization (e z)).range := by
          change LinearMap.range (_ ∘ₗ _) = _
          exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.surjective)
        rw [hrange]
        exact liftedStableParametrization_tangent_disjoint (e z)
    have hfinal := hehol.comp hqModel
    simpa only [qModel, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hfinal
  have localUnstableSubmersionNormalForm (x : X) :
      ∃ (W : TopologicalSpace.Opens X) (t : X → ℂ), x ∈ W ∧
        ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t W ∧
        (∀ y ∈ W, (transverseScalarDifferential t y).ker = U y) ∧
        ∃ h : Manifold.IsSubmersionAtOfComplement (ComplexModel (d - 1))
          (complexModel d) 𝓘(ℂ, ℂ) ∞ t x,
          ∀ y ∈ h.domChart.source,
            h.codChart (t y) = (h.equiv (h.domChart y)).1 := by
    obtain ⟨W, hx, σ, t, hσ, hσzero, hparallel, ht, hsub, hkernel⟩ := hlocal x
    let h := complex_submersion_fixed_complement (hsub x hx)
    refine ⟨W, t, hx, ht, fun y hy ↦ (hkernel y hy).2, h, ?_⟩
    intro y hy
    have hh := h.writtenInCharts
      ((h.domChart.extend (complexModel d)).map_source' (by simpa using hy))
    simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
      Function.id_def, h.domChart.left_inv hy] using hh
  have rawData : ∀ x : X, ∃ (W : TopologicalSpace.Opens X) (t : X → ℂ), x ∈ W ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t W ∧
      (∀ y ∈ W, (transverseScalarDifferential t y).ker = U y) ∧
      ∃ h : Manifold.IsSubmersionAtOfComplement (ComplexModel (d - 1))
        (complexModel d) 𝓘(ℂ, ℂ) ∞ t x,
        ∀ y ∈ h.domChart.source,
          h.codChart (t y) = (h.equiv (h.domChart y)).1 := localUnstableSubmersionNormalForm
  choose rawDomain rawScalar rawMem rawHolomorphic rawKernel rawSubmersion rawNormalForm
    using rawData
  let scalarModel : ComplexModel 1 ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  let rawCoordinate (x : X) : ComplexModel d ≃L[ℂ]
      ComplexModel (d - 1) × ComplexModel 1 :=
    ((rawSubmersion x).equiv.trans
      (ContinuousLinearEquiv.prodComm ℂ ℂ (ComplexModel (d - 1)))).trans
        ((ContinuousLinearEquiv.refl ℂ (ComplexModel (d - 1))).prodCongr scalarModel.symm)
  let rawUnstableBox (x : X) :
      OpenPartialHomeomorph X (ComplexModel (d - 1) × ComplexModel 1) :=
    (((rawSubmersion x).domChart).restrOpen (rawDomain x) (rawDomain x).isOpen).trans
      (rawCoordinate x).toHomeomorph.toOpenPartialHomeomorph
  have rawUnstableBox_source (x : X) : (rawUnstableBox x).source =
      (rawSubmersion x).domChart.source ∩ (rawDomain x : Set X) := by
    simp [rawUnstableBox]
  have rawUnstableBox_mem (x : X) : x ∈ (rawUnstableBox x).source := by
    rw [rawUnstableBox_source]
    exact ⟨(rawSubmersion x).mem_domChart_source, rawMem x⟩
  have rawUnstableBox_holomorphic (x : X) :
      ContMDiffOn (complexModel d) ((complexModel (d - 1)).prod (complexModel 1)) ∞
        (rawUnstableBox x) (rawUnstableBox x).source := by
    have hchart := contMDiffOn_of_mem_maximalAtlas (rawSubmersion x).domChart_mem_maximalAtlas
    have hdom : (rawUnstableBox x).source ⊆ (rawSubmersion x).domChart.source := by
      intro y hy
      rw [rawUnstableBox_source] at hy
      exact hy.1
    have hfst := ((ContinuousLinearMap.fst ℂ (ComplexModel (d - 1))
      (ComplexModel 1)).comp (rawCoordinate x).toContinuousLinearMap).contMDiff.comp_contMDiffOn
        (hchart.mono hdom)
    have hsnd := ((ContinuousLinearMap.snd ℂ (ComplexModel (d - 1))
      (ComplexModel 1)).comp (rawCoordinate x).toContinuousLinearMap).contMDiff.comp_contMDiffOn
        (hchart.mono hdom)
    exact hfst.prodMk hsnd
  have rawUnstableBox_inverse_holomorphic (x : X) :
      ContMDiffOn ((complexModel (d - 1)).prod (complexModel 1)) (complexModel d) ∞
        (rawUnstableBox x).symm (rawUnstableBox x).target := by
    have hid : ContMDiff ((complexModel (d - 1)).prod (complexModel 1))
        𝓘(ℂ, ComplexModel (d - 1) × ComplexModel 1) ∞
        (fun z : ComplexModel (d - 1) × ComplexModel 1 ↦ (z.1, z.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    have hlin := (rawCoordinate x).symm.toContinuousLinearMap.contMDiff.comp hid
    have hchart := contMDiffOn_symm_of_mem_maximalAtlas
      (rawSubmersion x).domChart_mem_maximalAtlas
    have hmaps : MapsTo (rawCoordinate x).symm (rawUnstableBox x).target
        (rawSubmersion x).domChart.target := by
      intro z hz
      have hh := (rawUnstableBox x).map_target hz
      rw [rawUnstableBox_source] at hh
      have hh' := (rawSubmersion x).domChart.map_source hh.1
      have heq := (rawUnstableBox x).right_inv hz
      change rawCoordinate x ((rawSubmersion x).domChart
        ((rawUnstableBox x).symm z)) = z at heq
      rw [← heq, (rawCoordinate x).symm_apply_apply]
      exact hh'
    exact hchart.comp hlin.contMDiffOn hmaps
  have rawUnstableBox_transverse (x y : X) (hy : y ∈ (rawUnstableBox x).source) :
      scalarModel ((rawUnstableBox x y).2) = (rawSubmersion x).codChart (rawScalar x y) := by
    have hy' : y ∈ (rawSubmersion x).domChart.source := by
      rw [rawUnstableBox_source] at hy
      exact hy.1
    change scalarModel (scalarModel.symm (((rawSubmersion x).equiv
      ((rawSubmersion x).domChart y)).1)) = _
    rw [scalarModel.apply_symm_apply]
    exact (rawNormalForm x y hy').symm
  have rawUnstableBox_product_neighborhood (x : X) :
      ∃ ρ : ℝ, 0 < ρ ∧
        Metric.ball (rawUnstableBox x x).1 ρ ×ˢ Metric.ball (rawUnstableBox x x).2 ρ ⊆
          (rawUnstableBox x).target := by
    obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp (rawUnstableBox x).open_target
      (rawUnstableBox x x) ((rawUnstableBox x).map_source (rawUnstableBox_mem x))
    refine ⟨ρ, hρ, ?_⟩
    simpa only [ball_prod_same, Prod.mk.eta] using hsub
  choose rawRadius rawRadius_pos rawProduct_subset using rawUnstableBox_product_neighborhood
  let rawProduct (x : X) :=
    Metric.ball (rawUnstableBox x x).1 (rawRadius x) ×ˢ
      Metric.ball (rawUnstableBox x x).2 (rawRadius x)
  have rawProduct_open (x : X) : IsOpen (rawProduct x) :=
    Metric.isOpen_ball.prod Metric.isOpen_ball
  let productUnstableBox (x : X) :=
    (((rawUnstableBox x).symm).restrOpen (rawProduct x) (rawProduct_open x)).symm
  have productUnstableBox_target (x : X) :
      (productUnstableBox x).target = rawProduct x := by
    change (rawUnstableBox x).target ∩ rawProduct x = rawProduct x
    exact Set.inter_eq_right.mpr (rawProduct_subset x)
  have productUnstableBox_mem (x : X) : x ∈ (productUnstableBox x).source := by
    change x ∈ (rawUnstableBox x).source ∩ (rawUnstableBox x) ⁻¹' rawProduct x
    exact ⟨rawUnstableBox_mem x, ⟨Metric.mem_ball_self (rawRadius_pos x),
      Metric.mem_ball_self (rawRadius_pos x)⟩⟩
  have productUnstableBox_source_subset (x : X) :
      (productUnstableBox x).source ⊆ (rawUnstableBox x).source := by
    intro y hy
    exact hy.1
  have productUnstableBox_holomorphic (x : X) :
      ContMDiffOn (complexModel d) ((complexModel (d - 1)).prod (complexModel 1)) ∞
        (productUnstableBox x) (productUnstableBox x).source :=
    (rawUnstableBox_holomorphic x).mono (productUnstableBox_source_subset x)
  have productUnstableBox_inverse_holomorphic (x : X) :
      ContMDiffOn ((complexModel (d - 1)).prod (complexModel 1)) (complexModel d) ∞
        (productUnstableBox x).symm (productUnstableBox x).target := by
    exact (rawUnstableBox_inverse_holomorphic x).mono (by
      intro y hy
      exact hy.1)
  let unitNormalization (x : X) :
      (ComplexModel (d - 1) × ComplexModel 1) ≃ₜ
        (ComplexModel (d - 1) × ComplexModel 1) :=
    ((Homeomorph.smulOfNeZero (rawRadius x : ℂ)
      (Complex.ofReal_ne_zero.mpr (rawRadius_pos x).ne')).trans
        (Homeomorph.addRight (rawUnstableBox x x))).symm
  let unitUnstableBox (x : X) :=
    (productUnstableBox x).trans (unitNormalization x).toOpenPartialHomeomorph
  have unitNormalization_inv_mem (x : X) (z : ComplexModel (d - 1) × ComplexModel 1) :
      (unitNormalization x).symm z ∈ rawProduct x ↔
        z ∈ (complexFoliationDisk (d - 1) : Set _) ×ˢ (complexFoliationDisk 1 : Set _) := by
    change ((rawRadius x : ℂ) • z + rawUnstableBox x x) ∈ rawProduct x ↔ _
    change (dist ((rawRadius x : ℂ) • z.1 + (rawUnstableBox x x).1)
      (rawUnstableBox x x).1 < rawRadius x ∧
      dist ((rawRadius x : ℂ) • z.2 + (rawUnstableBox x x).2)
      (rawUnstableBox x x).2 < rawRadius x) ↔
        dist z.1 0 < 1 ∧ dist z.2 0 < 1
    simp only [dist_eq_norm, add_sub_cancel_right, sub_zero, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rawRadius_pos x)]
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> nlinarith [rawRadius_pos x]
    · rintro ⟨h₁, h₂⟩
      constructor <;> nlinarith [rawRadius_pos x]
  have unitUnstableBox_target (x : X) : (unitUnstableBox x).target =
      (complexFoliationDisk (d - 1) : Set _) ×ˢ (complexFoliationDisk 1 : Set _) := by
    ext z
    change z ∈ Set.univ ∩ (unitNormalization x).symm ⁻¹'
      (productUnstableBox x).target ↔ _
    rw [productUnstableBox_target]
    exact (and_iff_right (Set.mem_univ z)).trans (unitNormalization_inv_mem x z)
  have unitUnstableBox_mem (x : X) : x ∈ (unitUnstableBox x).source :=
    ⟨productUnstableBox_mem x, Set.mem_univ _⟩
  have unitUnstableBox_source (x : X) :
      (unitUnstableBox x).source = (productUnstableBox x).source := by
    simp [unitUnstableBox]
  have unitUnstableBox_holomorphic (x : X) :
      ContMDiffOn (complexModel d) ((complexModel (d - 1)).prod (complexModel 1)) ∞
        (unitUnstableBox x) (unitUnstableBox x).source := by
    rw [unitUnstableBox_source]
    have h₁ : ContDiff ℂ ∞ (fun z : ComplexModel (d - 1) ↦
        (rawRadius x : ℂ)⁻¹ • (z - (rawUnstableBox x x).1)) := by fun_prop
    have h₂ : ContDiff ℂ ∞ (fun z : ComplexModel 1 ↦
        (rawRadius x : ℂ)⁻¹ • (z - (rawUnstableBox x x).2)) := by fun_prop
    exact (h₁.contMDiff.comp_contMDiffOn (contMDiff_fst.comp_contMDiffOn (productUnstableBox_holomorphic x))).prodMk
      (h₂.contMDiff.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn (productUnstableBox_holomorphic x)))
  have unitUnstableBox_inverse_holomorphic (x : X) :
      ContMDiffOn ((complexModel (d - 1)).prod (complexModel 1)) (complexModel d) ∞
        (unitUnstableBox x).symm (unitUnstableBox x).target := by
    have h₁ : ContDiff ℂ ∞ (fun z : ComplexModel (d - 1) ↦
        (rawRadius x : ℂ) • z + (rawUnstableBox x x).1) := by fun_prop
    have h₂ : ContDiff ℂ ∞ (fun z : ComplexModel 1 ↦
        (rawRadius x : ℂ) • z + (rawUnstableBox x x).2) := by fun_prop
    have hi : ContMDiff ((complexModel (d - 1)).prod (complexModel 1))
        ((complexModel (d - 1)).prod (complexModel 1)) ∞ (unitNormalization x).symm :=
      (h₁.contMDiff.comp contMDiff_fst).prodMk (h₂.contMDiff.comp contMDiff_snd)
    apply (productUnstableBox_inverse_holomorphic x).comp hi.contMDiffOn
    intro z hz
    exact hz.2
  let unitTransverseNormalization (x : X) : ComplexModel 1 ≃ₜ ComplexModel 1 :=
    ((Homeomorph.smulOfNeZero (rawRadius x : ℂ)
      (Complex.ofReal_ne_zero.mpr (rawRadius_pos x).ne')).trans
        (Homeomorph.addRight (rawUnstableBox x x).2)).symm
  let unitTransverseChart (x : X) : OpenPartialHomeomorph ℂ (ComplexModel 1) :=
    (((rawSubmersion x).codChart.trans scalarModel.symm.toHomeomorph.toOpenPartialHomeomorph).trans
      (unitTransverseNormalization x).toOpenPartialHomeomorph)
  have unitTransverseChart_mdiff (x : X) :
      (unitTransverseChart x).MDifferentiable 𝓘(ℂ, ℂ) (complexModel 1) := by
    have hc := contMDiffOn_of_mem_maximalAtlas (rawSubmersion x).codChart_mem_maximalAtlas
    have hci := contMDiffOn_symm_of_mem_maximalAtlas (rawSubmersion x).codChart_mem_maximalAtlas
    have hn : ContDiff ℂ ∞ (unitTransverseNormalization x) := by
      change ContDiff ℂ ∞ (fun z : ComplexModel 1 ↦
        (rawRadius x : ℂ)⁻¹ • (z - (rawUnstableBox x x).2))
      fun_prop
    have hni : ContDiff ℂ ∞ (unitTransverseNormalization x).symm := by
      change ContDiff ℂ ∞ (fun z : ComplexModel 1 ↦
        (rawRadius x : ℂ) • z + (rawUnstableBox x x).2)
      fun_prop
    constructor
    · have hh := hn.contMDiff.comp_contMDiffOn
        (scalarModel.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hc)
      exact (hh.mono (by intro z hz; exact hz.1.1)).mdifferentiableOn (by simp)
    · have hm : MapsTo (scalarModel ∘ (unitTransverseNormalization x).symm)
          (unitTransverseChart x).target (rawSubmersion x).codChart.target := by
        intro z hz
        exact hz.2.2
      have hh := hci.comp
        (scalarModel.toContinuousLinearMap.contMDiff.comp hni.contMDiff).contMDiffOn hm
      exact hh.mdifferentiableOn (by simp)
  have unitTransverseChart_at (x y : X) (hy : y ∈ (unitUnstableBox x).source) :
      rawScalar x y ∈ (unitTransverseChart x).source ∧
        unitTransverseChart x (rawScalar x y) = (unitUnstableBox x y).2 := by
    have hp : y ∈ (productUnstableBox x).source := (unitUnstableBox_source x) ▸ hy
    have hr := productUnstableBox_source_subset x hp
    have hd : y ∈ (rawSubmersion x).domChart.source :=
      ((rawUnstableBox_source x) ▸ hr).1
    refine ⟨⟨⟨(rawSubmersion x).source_subset_preimage_source hd, Set.mem_univ _⟩,
      Set.mem_univ _⟩, ?_⟩
    change (rawRadius x : ℂ)⁻¹ •
      (scalarModel.symm ((rawSubmersion x).codChart (rawScalar x y)) - (rawUnstableBox x x).2) =
      (rawRadius x : ℂ)⁻¹ • ((rawUnstableBox x y).2 - (rawUnstableBox x x).2)
    rw [← rawUnstableBox_transverse x y hr, scalarModel.symm_apply_apply]
  have unitUnstableBox_transverse_derivative (x y : X)
      (hy : y ∈ (unitUnstableBox x).source) (v : TangentSpace (complexModel d) y) :
      (mfderiv (complexModel d) ((complexModel (d - 1)).prod (complexModel 1))
        (unitUnstableBox x) y v).2 = 0 ↔ transverseScalarDifferential (rawScalar x) y v = 0 := by
    have hr : y ∈ (rawUnstableBox x).source := productUnstableBox_source_subset x
      ((unitUnstableBox_source x) ▸ hy)
    have hW : y ∈ rawDomain x := ((rawUnstableBox_source x) ▸ hr).2
    have hq := ((rawHolomorphic x).contMDiffAt ((rawDomain x).isOpen.mem_nhds hW)).mdifferentiableAt (by simp)
    have hb := ((unitUnstableBox_holomorphic x).contMDiffAt
      ((unitUnstableBox x).open_source.mem_nhds hy)).mdifferentiableAt (by simp)
    have ht := (unitTransverseChart_mdiff x).mdifferentiableAt (unitTransverseChart_at x y hy).1
    have hevent : (unitTransverseChart x) ∘ rawScalar x =ᶠ[𝓝 y]
        Prod.snd ∘ (unitUnstableBox x) := by
      filter_upwards [(unitUnstableBox x).open_source.mem_nhds hy] with z hz
      exact (unitTransverseChart_at x z hz).2
    have he := hevent.mfderiv_eq (I := complexModel d) (I' := complexModel 1)
    rw [mfderiv_comp y ht hq, mfderiv_comp y mdifferentiableAt_snd hb, mfderiv_snd] at he
    have hev := congrArg (fun L ↦ L v) he
    change (mfderiv 𝓘(ℂ, ℂ) (complexModel 1) (unitTransverseChart x) (rawScalar x y))
      (transverseScalarDifferential (rawScalar x) y v) =
      (mfderiv (complexModel d) ((complexModel (d - 1)).prod (complexModel 1))
        (unitUnstableBox x) y v).2 at hev
    constructor
    · intro hv
      apply (unitTransverseChart_mdiff x).mfderiv_injective (unitTransverseChart_at x y hy).1
      rw [map_zero, hev, hv]
    · intro hv
      rw [← hev, hv, map_zero]
  have unitUnstableBox_flattening (x y : X) (hy : y ∈ (unitUnstableBox x).source) :
      (U y).map (mfderiv (complexModel d) ((complexModel (d - 1)).prod (complexModel 1))
        (unitUnstableBox x) y).toLinearMap =
      (ContinuousLinearMap.inl ℂ (ComplexModel (d - 1)) (ComplexModel 1)).toLinearMap.range := by
    have hr : y ∈ (rawUnstableBox x).source := productUnstableBox_source_subset x
      ((unitUnstableBox_source x) ▸ hy)
    have hW : y ∈ rawDomain x := ((rawUnstableBox_source x) ▸ hr).2
    have hb : (unitUnstableBox x).MDifferentiable (complexModel d)
        ((complexModel (d - 1)).prod (complexModel 1)) :=
      ⟨(unitUnstableBox_holomorphic x).mdifferentiableOn (by simp),
        (unitUnstableBox_inverse_holomorphic x).mdifferentiableOn (by simp)⟩
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hq : transverseScalarDifferential (rawScalar x) y v = 0 := by
        rw [← rawKernel x y hW] at hv
        exact hv
      have hv₂ := (unitUnstableBox_transverse_derivative x y hy v).mpr hq
      refine ⟨(mfderiv (complexModel d) ((complexModel (d - 1)).prod (complexModel 1))
        (unitUnstableBox x) y v).1, ?_⟩
      exact Prod.ext rfl hv₂.symm
    · rintro ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hb.mfderiv_surjective hy (u, 0)
      refine ⟨v, ?_, hv⟩
      rw [← rawKernel x y hW]
      apply (unitUnstableBox_transverse_derivative x y hy v).mp
      exact congrArg Prod.snd hv
  obtain ⟨nativeUnstableFoliation, nativeUnstableBoxes, nativeUnstablePartition,
      nativeUnstableMarkedHomeomorph⟩ :=
    NativeLeafRebase.original_tangent_regular_foliation_native_homeomorph
      f.toHomeomorph.symm a.splitting.unstable.toDistribution nativeUnstableDatum
      unitUnstableBox (show d = (d - 1) + 1 by omega) U hU_hol hU_real
      unitUnstableBox_target (fun x ↦ ⟨x, unitUnstableBox_mem x⟩)
      unitUnstableBox_holomorphic unitUnstableBox_inverse_holomorphic
      unitUnstableBox_flattening
  have nativeUnstableFoliation_flattening
      (F : RegularHolomorphicFoliation.{u,u} d (d - 1) 1 X)
      (hboxes : ∃ e : X ≃ F.boxIndex, ∀ x, F.box (e x) = unitUnstableBox x) :
      ∀ i y, y ∈ (F.box i).source → (U y).map
        (mfderiv (complexModel d) ((complexModel (d - 1)).prod (complexModel 1))
          (F.box i) y).toLinearMap =
        (ContinuousLinearMap.inl ℂ (ComplexModel (d - 1)) (ComplexModel 1)).toLinearMap.range := by
    obtain ⟨e, he⟩ := hboxes
    intro i y hy
    obtain ⟨x, rfl⟩ := e.surjective i
    rw [he x] at hy ⊢
    exact unitUnstableBox_flattening x y hy
  have sourceUnstable_eq (x : X) : sourceU.toDistribution x = U x := by
    apply Submodule.restrictScalars_injective ℝ ℂ _
    apply Submodule.map_injective_of_injective (complexTangentToReal d x).injective
    exact (hUr x).trans (hU_real x).symm
  have nativeUnstableUpgrades : ∀ i, ∃ up : NativeLeafComplexUpgrade (d := d)
      (r := 2*t) t (Fu.leaf i).inclusion,
      letI := up.charts
      ∀ z : Lu i, (mfderiv (complexModel t) (complexModel d)
        (Fu.leaf i).inclusion z).range = U ((Fu.leaf i).inclusion z) := by
    intro i
    obtain ⟨c, hm, him, up, hc, htangent⟩ := hunstableComplex i
    subst c
    exact ⟨up, fun z ↦ (htangent z).trans (sourceUnstable_eq _)⟩
  choose unstableUpgrade unstableTangent using nativeUnstableUpgrades
  let : ∀ i, ChartedSpace (ComplexModel t) (Lu i) := fun i ↦ (unstableUpgrade i).charts
  let : ∀ i, IsManifold (complexModel t) ∞ (Lu i) :=
    fun i ↦ (unstableUpgrade i).complex_manifold
  have liftedUnstableRange_fibre (y : V) (i : ιu) (a₀ : Lu i)
      (ha₀ : (Fu.leaf i).inclusion a₀ = coverMap y) :
      liftedIntrinsicLeafRange coverMap (Fu.leaf i).inclusion a₀ y =
        {z | globalStableProjection z = globalStableProjection y} := by
    let : PathConnectedSpace (Lu i) :=
      (hunstableEuclidean i).some.toHomeomorph.pathConnectedSpace
    have hInvΓ := covering_conjugacy_inverse_lattice_g15 Γ A hAΓ
    have hInvConjugacy := covering_conjugacy_inverse_conjugacy_g15 Γ f A
      htorus htorusConjugacy
    have hleaf := intrinsic_affine Γ A.symm hInvΓ f.toHomeomorph.symm
      htorus hInvConjugacy coverMap coverMap_covering coverConjugacy coverConjugacy_eq
      y (Fu.leaf i).inclusion (unstableUpgrade i).inclusion_holomorphic.continuous a₀ ha₀
      (fun b ↦ ?_) (fun w hw ↦ ?_)
    · ext z
      constructor
      · intro hz
        have hm := Set.mem_image_of_mem coverConjugacy hz
        rw [hleaf.1] at hm
        obtain ⟨v, hv, heq⟩ := hm
        apply (globalStableProjection_fibres z y).mpr
        change coverConjugacy z - coverConjugacy y ∈ fullDecaySubmodule A.symm
        have heq' : coverConjugacy z - coverConjugacy y = v := by
          rw [← heq]
          exact add_sub_cancel_left _ _
        rw [heq']
        exact hv
      · intro hz
        have hv := (globalStableProjection_fibres z y).mp hz
        have hm : coverConjugacy z ∈
            (fun v ↦ coverConjugacy y + v) '' (fullDecaySubmodule A.symm : Set V) :=
          ⟨coverConjugacy z - coverConjugacy y, hv, by abel⟩
        rw [← hleaf.1] at hm
        obtain ⟨w, hw, heq⟩ := hm
        exact (coverConjugacy.injective heq) ▸ hw
    · have hb : (Fu.leaf i).inclusion b ∈ Set.range (Fu.leaf i).inclusion := ⟨b, rfl⟩
      rw [hunstableAsymptotic i a₀, ha₀] at hb
      exact hb
    · have hw' : w ∈ Set.range (Fu.leaf i).inclusion := by
        rw [hunstableAsymptotic i a₀, ha₀]
        exact hw
      exact hw'
  have coverMap_mfderiv_injective (y : V) :
      Function.Injective (mfderiv (complexModel d) (complexModel d) coverMap y) := by
    obtain ⟨e, hy, heq, he, hei⟩ := coverSheets y
    have hdiff : e.MDifferentiable (complexModel d) (complexModel d) :=
      ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
    have hevent : (e : V → X) =ᶠ[𝓝 y] coverMap := by
      filter_upwards [e.open_source.mem_nhds hy] with z hz
      exact heq hz
    have hinj := hdiff.mfderiv_injective hy
    rw [hevent.mfderiv_eq (I := complexModel d) (I' := complexModel d)] at hinj
    intro v w hv
    apply hinj
    exact congrArg (tangentSpaceCast (complexModel d) (coverMap y) (e y)) hv
  have coverMap_localDiffeomorph :
      IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ coverMap := by
    intro y
    obtain ⟨e, hy, heq, he, hei⟩ := coverSheets y
    exact ⟨{ toPartialEquiv := e.toPartialEquiv
             open_source := e.open_source
             open_target := e.open_target
             contMDiffOn_toFun := he
             contMDiffOn_invFun := hei }, hy, fun z hz ↦ (heq hz).symm⟩
  have lifted_native_ranges_of_marked_foliation
      (F : RegularHolomorphicFoliation.{u,u} d (d - 1) 1 X)
      (hNative : ∀ x : X, letI := F.leafTopology (Quotient.mk F.partition x)
        letI := (nativeUnstableDatum x).topology
        ∃ H : F.Leaf x ≃ₜ StableAsymptoticLeaf f.toHomeomorph.symm x,
          (∀ z, (H z).val = z.val) ∧
          (∀ z, (H.symm z).val = z.val))
      (G : RegularHolomorphicFoliation.{u,u} d (d - 1) 1 V)
      (hranges : ∀ y, Set.range (Subtype.val : G.Leaf y → V) =
        liftedIntrinsicLeafRange coverMap (Subtype.val : F.Leaf (coverMap y) → X)
          ⟨coverMap y, rfl⟩ y) :
      ∀ y, ∃ (i : ιu) (a₀ : Lu i),
        (Fu.leaf i).inclusion a₀ = coverMap y ∧
        Set.range (Subtype.val : G.Leaf y → V) =
          liftedIntrinsicLeafRange coverMap (Fu.leaf i).inclusion a₀ y := by
    intro y
    let x := coverMap y
    let := (nativeUnstableDatum x).topology
    obtain ⟨H, hH, hHi⟩ := hNative x
    obtain ⟨i, a₀, e, ha₀, he, he₀⟩ := nativeUnstableComparison x
    let T : F.Leaf x ≃ₜ Lu i := H.trans e.symm
    have hT : ∀ z : F.Leaf x, (Fu.leaf i).inclusion (T z) = z.val := by
      intro z
      change (Fu.leaf i).inclusion (e.symm (H z)) = z.val
      rw [← he, e.apply_symm_apply]
      exact hH z
    have hTa : T ⟨x, rfl⟩ = a₀ := by
      apply e.injective
      change e (e.symm (H ⟨x, rfl⟩)) = e a₀
      rw [e.apply_symm_apply]
      apply Subtype.ext
      exact (hH _).trans he₀.symm
    have hrange := Theorem12LiftedFoliationAssembly.lifted_range_homeomorph
      coverMap (Subtype.val : F.Leaf x → X) (Fu.leaf i).inclusion T hT ⟨x, rfl⟩ y
    rw [hTa] at hrange
    exact ⟨i, a₀, ha₀, (hranges y).trans hrange⟩
  have globalStableProjection_mfderiv_surjective_of_native_foliation
      (F : RegularHolomorphicFoliation.{u,u} d (d - 1) 1 V)
      (hfibres : ∀ y w, F.partition y w ↔ globalStableProjection y = globalStableProjection w)
      (hq : ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ globalStableProjection) :
      ∀ y, Function.Surjective (transverseScalarDifferential (d := d) globalStableProjection y) := by
    apply foliation_leaf_constant_mfderiv_surjective F globalStableProjection hq
    · intro y w hyw
      exact (hfibres y w).mp hyw
    · intro y
      refine ⟨liftedStableParametrization (globalStableProjection y),
        (hfibres _ _).mpr (globalStableProjection_liftedCoordinate _), ?_⟩
      have hcomp : globalStableProjection ∘ liftedStableParametrization = id :=
        funext globalStableProjection_liftedCoordinate
      have hd := mfderiv_comp (globalStableProjection y)
        (hq.mdifferentiableAt (by simp))
        (liftedStableParametrization_holomorphic.mdifferentiableAt (by simp))
      rw [hcomp, mfderiv_id] at hd
      intro z
      refine ⟨mfderiv 𝓘(ℂ, ℂ) (complexModel d) liftedStableParametrization
        (globalStableProjection y) z, ?_⟩
      exact (congrArg (fun L ↦ L z) hd).symm
  have globalStableProjection_kernel_of_native_foliation
      (F : RegularHolomorphicFoliation.{u,u} d (d - 1) 1 V)
      (hfibres : ∀ y w, F.partition y w ↔ globalStableProjection y = globalStableProjection w)
      (htangent : ∀ y, F.tangent y = (U (coverMap y)).comap
        (mfderiv (complexModel d) (complexModel d) coverMap y).toLinearMap)
      (hq : ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ globalStableProjection) :
      ∀ y v, transverseScalarDifferential (d := d) globalStableProjection y v = 0 ↔
        complexTangentToReal d (coverMap y)
          (mfderiv (complexModel d) (complexModel d) coverMap y v) ∈
            a.splitting.unstable.toDistribution (coverMap y) := by
    intro y v
    have hker := foliation_leaf_constant_mfderiv_kernel F globalStableProjection
      (fun a b h ↦ (hfibres a b).mp h) (by simp) y
      (hq.mdifferentiableAt (by simp))
      (globalStableProjection_mfderiv_surjective_of_native_foliation F hfibres hq y)
    change v ∈ (mfderiv (complexModel d) 𝓘(ℂ, ℂ) globalStableProjection y).ker ↔ _
    rw [hker, htangent]
    rw [← hU_real (coverMap y), Submodule.mem_map_equiv]
    change mfderiv (complexModel d) (complexModel d) coverMap y v ∈ U (coverMap y) ↔
      (complexTangentToReal d (coverMap y)).symm
        (complexTangentToReal d (coverMap y)
          (mfderiv (complexModel d) (complexModel d) coverMap y v)) ∈ U (coverMap y)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  have globalStableProjection_deck_translation
      (hq : ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ globalStableProjection) :
      ∀ γ : Γ, ∃ c : ℂ, ∀ y, globalStableProjection (deckAction γ y) =
        globalStableProjection y + c := by
    intro γ
    by_cases hγ : (γ : V) = 0
    · refine ⟨0, ?_⟩
      intro y
      have heq : deckAction γ y = y := by
        apply coverConjugacy.injective
        rw [deckTranslation_eq, hγ, add_zero]
      simp only [heq, add_zero]
    · have hInvΓ := covering_conjugacy_inverse_lattice_g15 Γ A hAΓ
      have hTZ : Set.MapsTo A.symm (Γ : Set V) (Γ : Set V) := by
        intro v hv
        rw [← hInvΓ]
        exact ⟨v, hv, rfl⟩
      exact holomorphic_projection_deck_translation (fullDecaySubmodule A.symm)
        (Γ : Set V) A.symm A.symm.injective
        (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
        hTZ Γ.zero_mem (map_zero A.symm)
        coverConjugacy globalStableProjection liftedStableParametrization hq
        liftedStableParametrization_holomorphic globalStableProjection_liftedCoordinate
        globalStableProjection_fibres (deckAction γ) (γ : V) γ.property hγ
        (fun h ↦ h) (deckTranslation_eq γ) (by
          intro y
          have heq := deckTranslation_eq γ ((deckAction γ).symm y)
          rw [(deckAction γ).apply_symm_apply] at heq
          exact eq_sub_iff_add_eq.mpr heq.symm)
  have coverInverseSheet_data (x : X) :
      ∃ e : OpenPartialHomeomorph V X, x ∈ e.target ∧
        EqOn e coverMap e.source ∧
        ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target := by
    obtain ⟨y, rfl⟩ := coverMap_surjective x
    obtain ⟨e, hy, heq, he, hei⟩ := coverSheets y
    exact ⟨e, (heq hy) ▸ e.map_source hy, heq, hei⟩
  choose inverseCoverSheet inverseCoverSheet_mem inverseCoverSheet_eq
    inverseCoverSheet_holomorphic using coverInverseSheet_data
  have coverMap_locally_injective (y : V) :
      ∃ W : Set V, W ∈ 𝓝 y ∧ Set.InjOn coverMap W := by
    obtain ⟨e, hy, heq, he, hei⟩ := coverSheets y
    refine ⟨e.source, e.open_source.mem_nhds hy, ?_⟩
    intro z hz w hw hzw
    exact e.injOn hz hw ((heq hz).trans (hzw.trans (heq hw).symm))
  let coverDerivative (y : V) : TangentSpace (complexModel d) y ≃L[ℂ]
      TangentSpace (complexModel d) (coverMap y) :=
    coverMap_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) y
  have coverDerivative_eq (y : V) : (coverDerivative y).toContinuousLinearMap =
      mfderiv (complexModel d) (complexModel d) coverMap y :=
    coverMap_localDiffeomorph.mfderivToContinuousLinearEquiv_coe (by simp) y
  suffices hProjection :
      ContMDiff (complexModel d) 𝓘(ℂ, ℂ) ∞ globalStableProjection ∧
      (∀ y, Function.Surjective (transverseScalarDifferential (d := d) globalStableProjection y)) ∧
      (∀ y v, transverseScalarDifferential (d := d) globalStableProjection y v = 0 ↔
        complexTangentToReal d (coverMap y)
          (mfderiv (complexModel d) (complexModel d) coverMap y v) ∈
            a.splitting.unstable.toDistribution (coverMap y)) by
    obtain ⟨hq, hqsurj, hqkernel⟩ := hProjection
    obtain ⟨θ, hθ⟩ := covering_projection_one_form_properties
      coverMap globalStableProjection (fun γ y ↦ deckAction γ y)
      f liftedDynamics stableMultiplier a.splitting.unstable.toDistribution
      coverMap_holomorphic hq f.contMDiff_toFun liftedDynamics.contMDiff_toFun
      coverMap_surjective coverDerivative coverDerivative_eq hqsurj
      (fun y v ↦ by
        have heq := congrArg (fun L ↦ L v) (coverDerivative_eq y)
        change coverDerivative y v = _ at heq
        rw [heq]
        exact hqkernel y v)
      (fun γ ↦ (deckAction γ).contMDiff_toFun.continuous)
      deckProjection_eq (globalStableProjection_deck_translation hq)
      coverMap_locally_injective
      (fun x ↦ (inverseCoverSheet x).target) (fun x ↦ (inverseCoverSheet x).open_target)
      inverseCoverSheet_mem (fun x ↦ (inverseCoverSheet x).symm)
      inverseCoverSheet_holomorphic
      (fun x z hz ↦ by
        rw [← inverseCoverSheet_eq x ((inverseCoverSheet x).map_target hz)]
        exact (inverseCoverSheet x).right_inv hz)
      (fun y z hyz ↦ (coverDeckTransitive y z hyz).exists)
      (funext coverDynamics_eq) (funext globalStableProjection_equivariant)
      (norm_pos_iff.mpr stableMultiplier_ne_zero) stableMultiplier_norm_lt_one
    exact ⟨θ, stableMultiplier, hθ⟩
  suffices hLift : ∃ G : RegularHolomorphicFoliation.{u,u} d (d - 1) 1 V,
      (∀ y, (G.tangent y).map
        (mfderiv (complexModel d) (complexModel d) coverMap y).toLinearMap = U (coverMap y)) ∧
      ∀ y, Set.range (Subtype.val : G.Leaf y → V) =
        liftedIntrinsicLeafRange coverMap
          (Subtype.val : nativeUnstableFoliation.Leaf (coverMap y) → X)
          ⟨coverMap y, rfl⟩ y by
    obtain ⟨G, hGtangent, hGranges⟩ := hLift
    have hOriginalRanges := lifted_native_ranges_of_marked_foliation nativeUnstableFoliation
      (fun x ↦ by
        obtain ⟨H, hH, hHi, hbase⟩ := nativeUnstableMarkedHomeomorph x
        exact ⟨H, hH, hHi⟩) G hGranges
    have hGfibres : ∀ y w, G.partition y w ↔
        globalStableProjection y = globalStableProjection w := by
      intro y w
      obtain ⟨i, a₀, ha₀, hr⟩ := hOriginalRanges y
      rw [liftedUnstableRange_fibre y i a₀ ha₀] at hr
      have hmem : G.partition y w ↔ w ∈ Set.range (Subtype.val : G.Leaf y → V) := by
        constructor
        · intro h
          exact ⟨⟨w, Quotient.sound (G.partition.symm h)⟩, rfl⟩
        · rintro ⟨z, rfl⟩
          exact G.partition.symm (Quotient.exact z.property)
      rw [hmem, hr]
      exact eq_comm
    have hGcomap : ∀ y, G.tangent y = (U (coverMap y)).comap
        (mfderiv (complexModel d) (complexModel d) coverMap y).toLinearMap := by
      intro y
      rw [← hGtangent y]
      exact (Submodule.comap_map_eq_of_injective
        (coverMap_mfderiv_injective y) (G.tangent y)).symm
    have hq := globalStableProjection_holomorphic_of_native_foliation G hGfibres hGcomap
    exact ⟨hq, globalStableProjection_mfderiv_surjective_of_native_foliation G hGfibres hq,
      globalStableProjection_kernel_of_native_foliation G hGfibres hGcomap hq⟩
  exact Theorem12LiftedFoliationAssembly.lifted_regular_foliation
    nativeUnstableFoliation coverMap coverMap_covering coverMap_localDiffeomorph
    coverSheets U (by
      intro i y hy
      exact nativeUnstableFoliation_flattening nativeUnstableFoliation
        nativeUnstableBoxes i y hy)


end HolomorphicAnosov.Paper.Zhang
