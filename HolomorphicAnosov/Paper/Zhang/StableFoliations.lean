import HolomorphicAnosov.Dynamics.Anosov.FiniteC1NativePlaqueExport
import HolomorphicAnosov.Geometry.ComplexSubbundleChart
import HolomorphicAnosov.Paper.Zhang.StableFoliationsGlobalCompletion
import HolomorphicAnosov.Dynamics.Anosov.NativeProductBoxDimension
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorMetric
import HolomorphicAnosov.Dynamics.Anosov.DistanceLeafRange
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsComplexSubmoduleOfJInvariant
import HolomorphicAnosov.Paper.Zhang.StableFoliationsComplexRankSplitFromRealification
import HolomorphicAnosov.Paper.Zhang.StableFoliationsNativeLeafRankFromComplexRank
import HolomorphicAnosov.Geometry.ComplexLinearFrameFromRealSubbundle
import HolomorphicAnosov.Geometry.RealificationSubbundleChart
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalStableJInvariant
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseSplitting
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingPos
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingContinuousBilinear
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealPairingSymm
import HolomorphicAnosov.Paper.Zhang.StableFoliationsPositiveFormUnitSublevelBounded
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinear
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinearApply
import HolomorphicAnosov.Paper.Zhang.StableFoliationsDerivativeScalarRestriction
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealInverseChartFrame
import HolomorphicAnosov.Paper.Zhang.StableFoliationsPairingInverseChartSmooth
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealMetric
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinearSmooth
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetric
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetricInner
import HolomorphicAnosov.Paper.Zhang.StableFoliationsTensorBoundsOfExactPairing
import HolomorphicAnosov.Paper.Zhang.StableFoliationsNativeLaminationsOfExactPairing
import HolomorphicAnosov.Paper.Zhang.StableFoliationsNativeLaminationsOfOriginalHermitian
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticIterateIff
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticIterateIffOfCompact
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticApplyIff
import HolomorphicAnosov.Paper.Zhang.StableFoliationsImageForwardAsymptoticEq
import HolomorphicAnosov.Paper.Zhang.StableFoliationsImageInverseAsymptoticEq
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalIterateDerivativeCommutesJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalIteratePairingJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalIterateBoundJ
import HolomorphicAnosov.Paper.Zhang.StableFoliationsMemStableOfExponentialDecay
import HolomorphicAnosov.Paper.Zhang.StableFoliationsStableInvariantOfEqualGrowth
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphConstruction
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.UniformExponentialLift
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Dynamics.PeriodicAsymptoticRigidity
import HolomorphicAnosov.Dynamics.PeriodicLabelUnique
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
This file constructs stable and unstable foliations with holomorphically immersed
leaves, real Euclidean parametrizations, and local product boxes from uniform Anosov estimates.
(Ghys, Lemma 2.1, pp.588–589; Zhang, p.3 and Lemma 2.5, p.8)
-/

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u
namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

open Bundle

/-- Uniform stable and unstable contraction bounds in a smooth Hermitian metric
yield complementary continuous complex tangent subbundles and invariant holomorphically
immersed stable and unstable foliations with Euclidean real parametrizations and asymptotic
leaf ranges. The foliations admit local product boxes and plaque families with jointly
continuous values and first leaf derivatives. (Ghys, Lemma 2.1 and pp.588–589;
HPS, Thm 5.5, pp.61–63 and pp.111–116, 127–129; Zhang, p.3 and Lemma 2.5, p.8;
Demailly, I, Lemma 7.15, p.60) -/
theorem stableFoliations
    {d : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M)
    (h : HermitianTangentMetricCore d M)
    (hh : IsSmoothHermitianTangentMetric h)
    (P : InvariantRealTangentSplitting f.toReal)
    (C rate : ℝ) (hC : 0 < C) (hrate : 0 < rate ∧ rate < 1)
    (hs : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.stable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)
        (mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v))
    (hu : ∀ n : ℕ, ∀ x : M, ∀ v : TangentSpace (realModel d) x,
      v ∈ P.unstable.toDistribution x →
      Real.sqrt (hermitianTangentRealPairing h ((f.symm : M → M)^[n] x)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)
        (mfderiv (realModel d) (realModel d)
          (realIterate (realModel d) f.toReal.symm n) x v)) ≤
        C * rate ^ n * Real.sqrt (hermitianTangentRealPairing h x v v)) :
    ∃ s t : ℕ, s + t = d ∧
    ∃ S U : ContinuousComplexTangentSubbundle (complexModel d) M,
      (∀ x, Module.finrank ℂ (S.toDistribution x) = s ∧
        Module.finrank ℂ (U.toDistribution x) = t) ∧
      (∀ x, ((S.toDistribution x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.stable.toDistribution x) ∧
      (∀ x, ((U.toDistribution x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.unstable.toDistribution x) ∧
    ∃ (ιs ιu : Type u) (Ls : ιs → Type u) (Lu : ιu → Type u),
    ∃ (ts : ∀ i, TopologicalSpace (Ls i)) (tu : ∀ i, TopologicalSpace (Lu i)),
    letI := ts; letI := tu
    ∃ (cs : ∀ i, ChartedSpace (Fin (2*s) → ℝ) (Ls i))
      (cu : ∀ i, ChartedSpace (Fin (2*t) → ℝ) (Lu i)),
    letI := cs; letI := cu
    ∃ (ms : ∀ i, IsManifold 𝓘(ℝ, Fin (2*s) → ℝ) ∞ (Ls i))
      (mu : ∀ i, IsManifold 𝓘(ℝ, Fin (2*t) → ℝ) ∞ (Lu i)),
    letI := ms; letI := mu
    ∃ (Fs : HPS.LeafPartition P.stable.toDistribution ιs Ls (fun _ ↦ 2*s))
      (Fu : HPS.LeafPartition P.unstable.toDistribution ιu Lu (fun _ ↦ 2*t)),
      (∀ i a, Set.range (Fs.leaf i).inclusion =
        {y | ForwardAsymptotic f ((Fs.leaf i).inclusion a) y}) ∧
      (∀ i a, Set.range (Fu.leaf i).inclusion =
        {y | ForwardAsymptotic f.symm ((Fu.leaf i).inclusion a) y}) ∧
      (∀ i, Nonempty (Diffeomorph 𝓘(ℝ, Fin (2*s) → ℝ)
        𝓘(ℝ, Fin (2*s) → ℝ) (Fin (2*s) → ℝ) (Ls i) ∞)) ∧
      (∀ i, Nonempty (Diffeomorph 𝓘(ℝ, Fin (2*t) → ℝ)
        𝓘(ℝ, Fin (2*t) → ℝ) (Fin (2*t) → ℝ) (Lu i) ∞)) ∧
      Nonempty (HPS.LeafDynamicalInvariance Fs f.toReal) ∧
      Nonempty (HPS.LeafDynamicalInvariance Fu f.toReal) ∧
      (∃ (βs βu : Type u) (Ts : βs → Type u) (Tu : βu → Type u)
        (tts : ∀ b, TopologicalSpace (Ts b)) (ttu : ∀ b, TopologicalSpace (Tu b)),
        letI := tts; letI := ttu
        Nonempty (HPS.LaminationBoxes Fs βs (fun _ ↦ 2*s) Ts) ∧
        Nonempty (HPS.LaminationBoxes Fu βu (fun _ ↦ 2*t) Tu)) ∧
      (∀ p : M, ∃ (Ds : TopologicalSpace.Opens (Fin (2*s) → ℝ))
        (Du : TopologicalSpace.Opens (Fin (2*t) → ℝ))
        (O : TopologicalSpace.Opens M) (e : (Ds × Du) ≃ₜ O),
        p ∈ O ∧ IsConnected (Ds : Set (Fin (2*s) → ℝ)) ∧
        IsConnected (Du : Set (Fin (2*t) → ℝ)) ∧
        (∀ w : Du, ∃ (i : ιs) (V : TopologicalSpace.Opens (Ls i))
          (c : Ds ≃ₜ V),
          ∀ z : Ds, (e (z, w)).val = (Fs.leaf i).inclusion (c z)) ∧
        (∀ z : Ds, ∃ (i : ιu) (V : TopologicalSpace.Opens (Lu i))
          (c : Du ≃ₜ V),
          ∀ w : Du, (e (z, w)).val = (Fu.leaf i).inclusion (c w)) ∧
        (∀ y z : O, ∃! w : O,
          (e.symm w).2 = (e.symm y).2 ∧ (e.symm w).1 = (e.symm z).1) ∧
        Continuous (fun yz : O × O ↦
          e ((e.symm yz.2).1, (e.symm yz.1).2))) ∧
      (∀ p : M, ∃ (V : Set M) (a : OpenPartialHomeomorph M (ComplexModel d))
        (r : ℝ) (q : M → (Fin (2*s) → ℝ) → M),
        IsOpen V ∧ p ∈ V ∧ V ⊆ a.source ∧
        a ∈ IsManifold.maximalAtlas (complexModel d) ∞ M ∧ 0 < r ∧
        (∀ x ∈ V, q x 0 = x) ∧
        (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*s) → ℝ) r, q x v ∈ a.source) ∧
        (∀ x ∈ V, ContMDiffOn 𝓘(ℝ, Fin (2*s) → ℝ) (realModel d) ∞
          (q x) (Metric.ball 0 r)) ∧
        (∀ x ∈ V, IsEmbedding (fun v : ↥(Metric.ball (0 : Fin (2*s) → ℝ) r) ↦ q x v)) ∧
        (∀ x ∈ V, ∃ (i : ιs) (c : OpenPartialHomeomorph (Ls i) (Fin (2*s) → ℝ)),
          c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (2*s) → ℝ) ∞ (Ls i) ∧
          Metric.ball (0 : Fin (2*s) → ℝ) r ⊆ c.target ∧
          ∀ v ∈ Metric.ball (0 : Fin (2*s) → ℝ) r,
            q x v = (Fs.leaf i).inclusion (c.symm v)) ∧
        (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*s) → ℝ) r,
          HasFDerivAt (fun w ↦ a (q x w))
            (fderiv ℝ (fun w ↦ a (q x w)) v) v) ∧
        ContinuousOn (fun xv : M × (Fin (2*s) → ℝ) ↦ a (q xv.1 xv.2))
          (V ×ˢ Metric.ball 0 r) ∧
        ContinuousOn (fun xv : M × (Fin (2*s) → ℝ) ↦
          fderiv ℝ (fun v ↦ a (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 r)) ∧
      (∀ p : M, ∃ (V : Set M) (a : OpenPartialHomeomorph M (ComplexModel d))
        (r : ℝ) (q : M → (Fin (2*t) → ℝ) → M),
        IsOpen V ∧ p ∈ V ∧ V ⊆ a.source ∧
        a ∈ IsManifold.maximalAtlas (complexModel d) ∞ M ∧ 0 < r ∧
        (∀ x ∈ V, q x 0 = x) ∧
        (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*t) → ℝ) r, q x v ∈ a.source) ∧
        (∀ x ∈ V, ContMDiffOn 𝓘(ℝ, Fin (2*t) → ℝ) (realModel d) ∞
          (q x) (Metric.ball 0 r)) ∧
        (∀ x ∈ V, IsEmbedding (fun v : ↥(Metric.ball (0 : Fin (2*t) → ℝ) r) ↦ q x v)) ∧
        (∀ x ∈ V, ∃ (i : ιu) (c : OpenPartialHomeomorph (Lu i) (Fin (2*t) → ℝ)),
          c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin (2*t) → ℝ) ∞ (Lu i) ∧
          Metric.ball (0 : Fin (2*t) → ℝ) r ⊆ c.target ∧
          ∀ v ∈ Metric.ball (0 : Fin (2*t) → ℝ) r,
            q x v = (Fu.leaf i).inclusion (c.symm v)) ∧
        (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin (2*t) → ℝ) r,
          HasFDerivAt (fun w ↦ a (q x w))
            (fderiv ℝ (fun w ↦ a (q x w)) v) v) ∧
        ContinuousOn (fun xv : M × (Fin (2*t) → ℝ) ↦ a (q xv.1 xv.2))
          (V ×ˢ Metric.ball 0 r) ∧
        ContinuousOn (fun xv : M × (Fin (2*t) → ℝ) ↦
          fderiv ℝ (fun v ↦ a (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 r)) ∧
      (∀ i, ∃ c : ChartedSpace (ComplexModel s) (Ls i),
        letI := c
        IsManifold (complexModel s) ∞ (Ls i) ∧
        Manifold.IsImmersion (complexModel s) (complexModel d) ∞ (Fs.leaf i).inclusion ∧
        ∃ upgrade : NativeLeafComplexUpgrade (d := d) (r := 2*s) s
            (Fs.leaf i).inclusion,
          upgrade.charts = c ∧
          ∀ z : Ls i, (mfderiv (complexModel s) (complexModel d)
            (Fs.leaf i).inclusion z).range = S.toDistribution ((Fs.leaf i).inclusion z)) ∧
      (∀ i, ∃ c : ChartedSpace (ComplexModel t) (Lu i),
        letI := c
        IsManifold (complexModel t) ∞ (Lu i) ∧
        Manifold.IsImmersion (complexModel t) (complexModel d) ∞ (Fu.leaf i).inclusion ∧
        ∃ upgrade : NativeLeafComplexUpgrade (d := d) (r := 2*t) t
            (Fu.leaf i).inclusion,
          upgrade.charts = c ∧
          ∀ z : Lu i, (mfderiv (complexModel t) (complexModel d)
            (Fu.leaf i).inclusion z).range = U.toDistribution ((Fu.leaf i).inclusion z)) := by
  
  have hnative := HPS.anosov_global_lamination_tensor_metric f.toReal P
    (StableFoliationsSupport.originalSmoothRealMetric h hh)
    (StableFoliationsSupport.tensor_bounds_of_exact_pairing f h hh P C rate hC hrate hs hu
      (StableFoliationsSupport.originalSmoothRealMetric h hh)
      (StableFoliationsSupport.originalSmoothRealMetric_inner h hh))
  have hstableJ := StableFoliationsSupport.original_stable_J_invariant
    f h P C rate hC hrate hs hu
  have hunstableJ : ∀ x (v : TangentSpace (realModel d) x),
      v ∈ P.unstable.toDistribution x →
      complexTangentToReal d x (Complex.I • (complexTangentToReal d x).symm v) ∈
        P.unstable.toDistribution x := by
    let Q : InvariantRealTangentSplitting (Biholomorph.toReal f.symm) :=
      TheoremAProof.inverseSplitting f.toReal P
    apply StableFoliationsSupport.original_stable_J_invariant
      f.symm h Q C rate hC hrate
    · intro n x v hv
      convert hu n x v hv using 1
      rfl
    · intro n x v hv
      convert hs n x v hv using 1
      rfl
  obtain ⟨S0, hS0⟩ : ∃ D : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x),
      ∀ x, ((D x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.stable.toDistribution x := by
    choose D hD using fun x ↦
      (StableFoliationsSupport.existsUnique_complexSubmodule_of_J_invariant
        (complexTangentToReal d x).toLinearEquiv (P.stable.toDistribution x)
        (hstableJ x)).exists
    exact ⟨D, hD⟩
  have hstableComplex := complex_subbundle_of_realification P.stable S0 hS0
  obtain ⟨U0, hU0⟩ : ∃ D : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x),
      ∀ x, ((D x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap = P.unstable.toDistribution x := by
    choose D hD using fun x ↦
      (StableFoliationsSupport.existsUnique_complexSubmodule_of_J_invariant
        (complexTangentToReal d x).toLinearEquiv (P.unstable.toDistribution x)
        (hunstableJ x)).exists
    exact ⟨D, hD⟩
  have hunstableComplex := complex_subbundle_of_realification P.unstable U0 hU0
  obtain ⟨Srank, hSrank⟩ := hstableComplex
  obtain ⟨Urank, hUrank⟩ := hunstableComplex
  obtain ⟨sRank, tRank, hstRank, hrankRank⟩ :=
    complex_rank_split_from_realification P.stable.toDistribution
      P.unstable.toDistribution P.isCompl Srank Urank
      (fun x ↦ by simpa [hSrank] using hS0 x)
      (fun x ↦ by simpa [hUrank] using hU0 x)
  refine ⟨sRank, tRank, hstRank, Srank, Urank, hrankRank,
    (fun x ↦ by simpa [hSrank] using hS0 x),
    (fun x ↦ by simpa [hUrank] using hU0 x), ?_⟩
  
  
  
  obtain ⟨ιs, Ls, rs, ts, css, mss, Fs, hboxesS, hinvS,
      familiesS, coherentS, hextraS⟩ := hnative.1
  let := ts
  let := css
  let := mss
  have hrs : ∀ i, rs i = 2 * sRank :=
    native_leaf_rank_eq_of_realification
      P.stable.toDistribution Srank
      (fun x ↦ by simpa [hSrank] using hS0 x) sRank
      (fun x ↦ (hrankRank x).1) Fs
  have hrsfun : rs = (fun _ ↦ 2 * sRank) := funext hrs
  cases hrsfun
  obtain ⟨ιu, Lu, ru, tu, c_u, m_u, Fu, hboxesU, hinvU,
      familiesU, coherentU, hextraU⟩ := hnative.2
  let := tu
  let := c_u
  let := m_u
  have hru : ∀ i, ru i = 2 * tRank :=
    native_leaf_rank_eq_of_realification
      P.unstable.toDistribution Urank
      (fun x ↦ by simpa [hUrank] using hU0 x) tRank
      (fun x ↦ (hrankRank x).2) Fu
  have hrufun : ru = (fun _ ↦ 2 * tRank) := funext hru
  cases hrufun
  refine ⟨ιs, ιu, Ls, Lu, ts, tu, css, c_u, mss, m_u, Fs, Fu, ?_⟩
  obtain ⟨_, _, _, _, ⟨identificationS, _⟩, _, _⟩ := hextraS
  obtain ⟨_, _, _, _, ⟨identificationU, _⟩, _, _⟩ := hextraU
  refine ⟨?_, ?_, ?_⟩
  · intro i a
    exact identificationS.range_eq_forwardAsymptotic i a
  · intro i a
    exact identificationU.range_eq_forwardAsymptotic i a
  obtain ⟨βs, ds, Ts, topTs, ⟨Bs⟩⟩ := hboxesS
  let := topTs
  have hds : ds = (fun _ ↦ 2 * sRank) :=
    funext (fun b ↦ (Bs.boxes b).dimension_eq)
  cases hds
  obtain ⟨βu, du, Tu, topTu, ⟨Bu⟩⟩ := hboxesU
  let := topTu
  have hdu : du = (fun _ ↦ 2 * tRank) :=
    funext (fun b ↦ (Bu.boxes b).dimension_eq)
  cases hdu
  
  suffices hremaining : _ ∧ _ ∧ _ by
    exact ⟨hremaining.1, hremaining.2.1, hinvS, hinvU,
      ⟨βs, βu, Ts, Tu, topTs, topTu, ⟨Bs⟩, ⟨Bu⟩⟩, hremaining.2.2⟩
  obtain ⟨heuS, heuU, _, _, _, hpaired, _, _, hcomplexS, hcomplexU⟩ :=
    stableFoliations_global_euclidean_paired_complex_completion
      f h hh P C rate hC hrate hs hu (S := Srank) (U := Urank) hstRank
      (fun x ↦ by simpa [hSrank] using hS0 x)
      (fun x ↦ by simpa [hUrank] using hU0 x) Fs Fu
  exact ⟨heuS, heuU, hpaired,
    (fun p ↦ (familiesS.family p).coordinate_export),
    (fun p ↦ (familiesU.family p).coordinate_export), hcomplexS, hcomplexU⟩



end HolomorphicAnosov
