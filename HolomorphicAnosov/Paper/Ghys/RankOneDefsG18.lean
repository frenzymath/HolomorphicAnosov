import HolomorphicAnosov.Geometry.PlaquePhysicalNormalG18
import HolomorphicAnosov.Geometry.NativePlaqueTubePairUniquenessG18
import HolomorphicAnosov.Geometry.NativePlaqueChartFromLiftG18
import HolomorphicAnosov.Analysis.MetricPullbackCompactLowerBound
import HolomorphicAnosov.Topology.ParametricPathSubdivisionG18
import HolomorphicAnosov.Geometry.NativeIdentificationStableProductsG18
import HolomorphicAnosov.Geometry.NativeIdentificationStablePlaqueLiftG18
import HolomorphicAnosov.Geometry.PathHolonomyStableRelation
import HolomorphicAnosov.Geometry.Holonomy.ContinuousPrefixFamilyG18
import HolomorphicAnosov.Geometry.NativePlaqueIntrinsicPathBoundsLowerG18
import HolomorphicAnosov.Geometry.NativePlaqueMetricTubeG18
import HolomorphicAnosov.Geometry.CompactParametricTubeInjectivityG18
import HolomorphicAnosov.Ghys.BufferedDiskInjectivityG18
import HolomorphicAnosov.Geometry.ParametricMetricNormalFrameG18
import HolomorphicAnosov.Geometry.HPSRealAnosovEstimateDataTensorToBundle
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateSymmVal
import HolomorphicAnosov.Geometry.ContinuousUnstableLeafLiftG1
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticApplyIff
import HolomorphicAnosov.Paper.Ghys.ProjectiveNativeIdentification
import HolomorphicAnosov.Analysis.MovingAlmostIsometryG18
import HolomorphicAnosov.Analysis.ParametricInverseSpatialRegularityG18
import HolomorphicAnosov.Geometry.PlaqueMetricNormalProjectionG18
import HolomorphicAnosov.Geometry.ParametricPlaqueTubeInverseG18
import HolomorphicAnosov.Geometry.NativePlaqueSecondDerivativeG18
import HolomorphicAnosov.Ghys.ComparisonBoundaryAvoidanceG18
import HolomorphicAnosov.Geometry.ExponentialDerivativeZeroG18
import HolomorphicAnosov.Geometry.MetricChartTensorG18
import HolomorphicAnosov.Dynamics.Anosov.NativeLeafRank
import HolomorphicAnosov.Dynamics.Anosov.DistanceIdentificationNativeDatum
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Analysis.CommonReceivingImage
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorDistance
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorMetric
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalSmoothRealMetricInner
import HolomorphicAnosov.Analysis.BoundedContinuousInvariantSections
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Topology.DiskDegreeLocalHomeomorphismCount
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.LinearAlgebra.Determinant

/-!
This file defines intrinsic rank-one unstable leaves, Hermitian Anosov estimates, and expanding
plaque comparisons. It also constructs smooth iterate maps on these leaves and relates the
Hermitian estimates to Anosov data. (Ghys, Prop. 2.2, pp.588–590)
-/

open Manifold MeasureTheory

namespace HolomorphicAnosov.Ghys

open Set Filter _root_.Topology
open scoped ContDiff

noncomputable section

universe u

section OriginalAmbient

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]

attribute [local instance] complex_isManifold_real

/-- A metric compatible with the ambient manifold topology. -/
abbrev rankComparisonMetric : MetricSpace M :=
  letI := Manifold.metrizableSpace (realModel d) M
  TopologicalSpace.metrizableSpaceMetric M

/-- The norm induced by the Hermitian metric on the underlying real tangent fibre.
(Ghys, p.588; Demailly, VI §4, pp.296–297) -/
def givenHermitianNorm (h : HermitianTangentMetricCore d M) (x : M)
    (v : TangentSpace (realModel d) x) : ℝ :=
  Real.sqrt (hermitianTangentRealPairing h x v v)

/-- Uniform exponential contraction of stable vectors under positive iterates and unstable
vectors under inverse iterates, measured in the Hermitian norm. (Ghys, p.588) -/
def HermitianAllTimeAnosov (f : Biholomorph d d M M)
    (h : HermitianTangentMetricCore d M)
    (S : InvariantRealTangentSplitting f.toReal) : Prop :=
  ∃ C expansion : ℝ, 0 < C ∧ 1 < expansion ∧
    (∀ (n : ℕ), 0 < n → ∀ (x : M) (v : TangentSpace (realModel d) x),
      v ∈ S.stable.toDistribution x →
      givenHermitianNorm h ((f^[n]) x)
          (mfderiv (realModel d) (realModel d) (f^[n]) x v) ≤
        C * expansion ^ (-(n : ℤ)) * givenHermitianNorm h x v) ∧
    (∀ (n : ℕ), 0 < n → ∀ (x : M) (v : TangentSpace (realModel d) x),
      v ∈ S.unstable.toDistribution x →
      givenHermitianNorm h ((f.symm^[n]) x)
          (mfderiv (realModel d) (realModel d) (f.symm^[n]) x v) ≤
        C * expansion ^ (-(n : ℤ)) * givenHermitianNorm h x v)

end OriginalAmbient

section NativeFamily

variable {d : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]

attribute [local instance] complex_isManifold_real

/-- Intrinsic asymptotic leaves and transverse product boxes, together with smooth unstable
iterate maps agreeing with the ambient iterates. (HPS, §5–7, pp.61–62, 114–116;
Ghys, pp.589–590) -/
structure RankOneNativeLeaves (f : Biholomorph d d M M)
    (S : InvariantRealTangentSplitting f.toReal) where
  stableDimension : ℕ
  identification : NativeTransverseAsymptoticIdentification.{u, u}
    f.toHomeomorph S.stable.toDistribution S.unstable.toDistribution stableDimension 2
  iterateUnstable : ∀ (n : ℕ) (x : M),
    letI := identification.unstableTopology x
    letI := identification.unstableCharts x
    letI := identification.unstableTopology ((f^[n]) x)
    letI := identification.unstableCharts ((f^[n]) x)
    Diffeomorph (modelWithCornersSelf ℝ (Fin (identification.nativeU x).rank → ℝ))
      (modelWithCornersSelf ℝ (Fin (identification.nativeU ((f^[n]) x)).rank → ℝ))
      (UnstableAsymptoticLeaf f.toHomeomorph x)
      (UnstableAsymptoticLeaf f.toHomeomorph ((f^[n]) x)) ∞
  iterateUnstable_points : ∀ (n : ℕ) (x : M)
      (z : UnstableAsymptoticLeaf f.toHomeomorph x),
    (iterateUnstable n x z).val = (f^[n]) z.val

namespace RankOneNativeLeaves

variable {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
variable (L : RankOneNativeLeaves f S)

/-- The intrinsic real unstable leaf through `x`. (HPS, pp.114–116) -/
abbrev unstable (x : M) := L.identification.nativeU x

/-- The complex curve structure on the unstable leaf through `x`. (Ghys, p.589) -/
abbrev complexUnstable (x : M) := L.identification.complexU1 x

/-- The real ambient atlas associated with the transverse foliation.
(Demailly, p.23) -/
abbrev realAmbientCharts := L.identification.realAmbientCharts

/-- The continuous transverse stable and unstable foliations. (HPS, p.115) -/
abbrev foliation := L.identification.F

/-- The point-preserving homeomorphism from the intrinsic unstable partition class to the
unstable asymptotic leaf through `x`. -/
abbrev unstableClass (x : M) := L.identification.unstableClassHomeomorph x

/-- The unstable asymptotic leaf through `x`. (Ghys, p.589) -/
def U (_L : RankOneNativeLeaves f S) (x : M) := UnstableAsymptoticLeaf f.toHomeomorph x

instance (priority := 2000) uTopology (x : M) : TopologicalSpace (L.U x) :=
  (L.unstable x).topology
instance (priority := 2000) uRealCharts (x : M) :
    ChartedSpace (Fin (L.unstable x).rank → ℝ) (L.U x) :=
  (L.unstable x).charts

local instance : ChartedSpace (Fin (L.stableDimension + 2) → ℝ) M := L.realAmbientCharts

/-- The real coordinate model for the intrinsic unstable leaf through `x`.
(HPS, pp.114–116) -/
abbrev uModel (x : M) := modelWithCornersSelf ℝ (Fin (L.unstable x).rank → ℝ)

/-- The distinguished point of the unstable leaf through `x`, with ambient value `x`.
(Ghys, p.589) -/
def uPoint (x : M) : L.U x :=
  letI := L.realAmbientCharts
  L.unstableClass x (L.foliation.uPoint x)

/-- A set is a complex closed disk if it is the inverse chart image of a positive-radius
closed ball contained in the chart target. (Ghys, pp.589–590) -/
def IsComplexClosedDisk (x : M) (W : Set (L.U x)) : Prop :=
  letI := L.identification.unstableTopology x
  letI := L.identification.unstableCharts x
  letI : TopologicalSpace (L.U x) := (L.unstable x).topology
  letI : ChartedSpace (ComplexModel 1) (L.U x) := (L.complexUnstable x).charts
  ∃ c : OpenPartialHomeomorph (L.U x) (ComplexModel 1),
    c ∈ atlas (ComplexModel 1) (L.U x) ∧
    ∃ a : ComplexModel 1, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall a r ⊆ c.target ∧ W = c.symm '' Metric.closedBall a r

/-- The local holonomy map along a stable path, expressed on its endpoint unstable asymptotic
leaves via the point-preserving identifications. (Ghys, p.589) -/
def holonomyRepresentative
    {q : Quotient L.foliation.stablePartition}
    {x y : IntrinsicFoliationLeaf L.foliation.stablePartition q}
    (γ : Path x y) (e : PathHolonomyRepresentative L.foliation γ 0 1) :
    L.U (γ 0).val → L.U (γ 1).val :=
  letI := L.identification.unstableTopology (γ 0).val
  letI := L.identification.unstableTopology (γ 1).val
  fun z ↦ L.unstableClass (γ 1).val (e.map ((L.unstableClass (γ 0).val).symm z))

/-- On forward images of a disk, the conjugated holonomy admits orientation-preserving real
C¹ comparisons whose Hermitian derivative distortion and intrinsic leaf-distance error tend
to zero. (Ghys, pp.589–590) -/
def ComparisonOnDisk (hmetric : HermitianTangentMetricCore d M) (x y : M)
    (h : @OpenPartialHomeomorph (L.U x) (L.U y)
      ((L.unstable x).topology) ((L.unstable y).topology)) (W : Set (L.U x)) : Prop :=
  letI := L.identification.unstableTopology x
  letI := L.identification.unstableTopology y
  letI := L.identification.unstableCharts x
  letI := L.identification.unstableCharts y
  ∃ ε δ : ℕ → ℝ,
    (∀ k, 0 ≤ ε k) ∧ (∀ k, 0 ≤ δ k) ∧
    Tendsto ε atTop (𝓝 0) ∧ Tendsto δ atTop (𝓝 0) ∧
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      let xk := (f^[k]) x
      let yk := (f^[k]) y
      letI := L.identification.unstableTopology xk
      letI := L.identification.unstableTopology yk
      letI := L.identification.unstableCharts xk
      letI := L.identification.unstableCharts yk
      let Wk := L.iterateUnstable k x '' W
      let Hk := L.iterateUnstable k y ∘ h ∘ (L.iterateUnstable k x).symm
      ∃ π : OpenPartialHomeomorph (L.U xk) (L.U yk),
        Wk ⊆ π.source ∧
        ContMDiffOn (L.uModel xk) (L.uModel yk) 1 π π.source ∧
        ContMDiffOn (L.uModel yk) (L.uModel xk) 1 π.symm π.target ∧
        InjOn π Wk ∧
        (∀ z ∈ Wk,
          letI : ChartedSpace (ComplexModel 1) (L.U xk) := (L.complexUnstable xk).charts
          letI : ChartedSpace (ComplexModel 1) (L.U yk) := (L.complexUnstable yk).charts
          0 < LinearMap.det
            (fderiv ℝ
              ((chartAt (M := L.U yk) (ComplexModel 1) (π z)) ∘ π ∘
                (chartAt (M := L.U xk) (ComplexModel 1) z).symm)
              (chartAt (M := L.U xk) (ComplexModel 1) z z)).toLinearMap) ∧
        (∀ (z : L.U xk), z ∈ Wk →
          ∀ v : TangentSpace (L.uModel xk) z,
            (1 - ε k) * leafPullbackHermitianNorm (d := d) Subtype.val hmetric z v ≤
              leafPullbackHermitianNorm (d := d) Subtype.val hmetric (π z)
                (mfderiv (L.uModel xk) (L.uModel yk) π z v) ∧
            leafPullbackHermitianNorm (d := d) Subtype.val hmetric (π z)
                (mfderiv (L.uModel xk) (L.uModel yk) π z v) ≤
              (1 + ε k) * leafPullbackHermitianNorm (d := d) Subtype.val hmetric z v) ∧
        (∀ z ∈ Wk,
          intrinsicHermitianLeafEDist (d := d) (r := (L.unstable yk).rank)
            Subtype.val hmetric (π z) (Hk z) ≤
            ENNReal.ofReal (δ k))

/-- Every stable holonomy germ admits expanding-disk comparisons on all sufficiently small
complex closed disks around its initial point. (Ghys, pp.589–590) -/
def ComparisonProperty (hmetric : HermitianTangentMetricCore d M) : Prop :=
  letI := L.realAmbientCharts
  ∀ q : Quotient L.foliation.stablePartition,
    letI := L.foliation.stableTopology q
    ∀ x y : IntrinsicFoliationLeaf L.foliation.stablePartition q,
      ∀ γ : Path x y, ∀ e : PathHolonomyRepresentative L.foliation γ 0 1,
        let x0 := (γ 0).val
        let y0 := (γ 1).val
        letI := L.identification.unstableTopology x0
        letI := L.identification.unstableTopology y0
        ∀ h : OpenPartialHomeomorph (L.U x0) (L.U y0),
          L.uPoint x0 ∈ h.source → h (L.uPoint x0) = L.uPoint y0 →
          (∀ᶠ z in 𝓝 (L.uPoint x0), h z = L.holonomyRepresentative γ e z) →
          ∃ N : Set (L.U x0), IsOpen N ∧ L.uPoint x0 ∈ N ∧ N ⊆ h.source ∧
            ∀ W : Set (L.U x0), L.IsComplexClosedDisk x0 W →
              W ⊆ N → L.uPoint x0 ∈ interior W → L.ComparisonOnDisk hmetric x0 y0 h W

end RankOneNativeLeaves

end NativeFamily

end
end HolomorphicAnosov.Ghys

noncomputable section
open scoped ContDiff Bundle
open Filter
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
universe u
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]

/-- Uniform exponential tensor bounds yield an Anosov datum with the specified splitting
and Riemannian metric. -/
theorem anosovDatum_of_tensorBounds_g18
    (f : Biholomorph d d M M) (S : InvariantRealTangentSplitting f.toReal)
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (hb : Nonempty (TensorAnosovBounds f.toReal S g)) :
    ∃ a : AnosovDatum f, a.splitting = S ∧ a.metric = g := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace (realModel d) x) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨C, r, hC, hr, hr1, hs, hu⟩ := tensorAnosovBounds_to_bundle f.toReal S g hb
  have ht : Tendsto (fun n : ℕ ↦ C * r ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).const_mul C
  obtain ⟨k, hk, hsmall⟩ := ((eventually_ge_atTop 1).and (ht.eventually (gt_mem_nhds zero_lt_one))).exists
  have hnonneg : 0 ≤ C * r ^ k := mul_nonneg hC.le (pow_nonneg hr.le _)
  refine ⟨{
    metric := g
    splitting := S
    k := k
    one_le_k := hk
    stable_contracting := ?_
    unstable_contracting := ?_ }, rfl, rfl⟩
  · intro x
    apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ hnonneg ?_) hsmall
    intro v
    change ‖mfderiv (realModel d) (realModel d) (realIterate (realModel d) f.toReal k) x v.val‖ ≤ _
    exact hs k x v.val v.property
  · intro x
    apply lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ hnonneg ?_) hsmall
    intro v
    change ‖((restrictedIterateDerivative f.toReal S.unstable.toDistribution S.unstable_map k x).symm v).val‖ ≤ _
    rw [FixedBlockEstimates.Inverse.restricted_iterate_symm_val]
    have hnorm := congrArg (fun z : M ↦
      (fun w : ComplexModel d ↦ @norm (TangentSpace (realModel d) z) inferInstance w))
      (inverse_iterate_basepoint f.toReal k x)
    have h := hu k ((f.toReal^[k]) x) v.val v.property
    change @norm (TangentSpace (realModel d) ((f.toReal.symm^[k]) ((f.toReal^[k]) x)))
      inferInstance (mfderiv (realModel d) (realModel d) (f.toReal.symm^[k])
        ((f.toReal^[k]) x) v.val) ≤ _ at h
    exact (congrFun hnorm
      (mfderiv (realModel d) (realModel d) (f.toReal.symm^[k])
        ((f.toReal^[k]) x) v.val)).ge.trans h
end HolomorphicAnosov

noncomputable section
set_option linter.style.haveILetI false
open Set Filter TopologicalSpace
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real
variable {d s : ℕ} {M : Type u} [MetricSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  {f : Biholomorph d d M M} {S : InvariantRealTangentSplitting f.toReal}
  (A : NativeTransverseAsymptoticIdentification.{u,u} f.toHomeomorph
    S.stable.toDistribution S.unstable.toDistribution s 2)

omit [CompactSpace M] in
/-- A map between intrinsic unstable leaves is continuous if its composition with the
ambient inclusion is continuous. -/
theorem native_unstable_continuous_lift_g18 (x y : M) :
    letI := A.unstableTopology x
    letI := A.unstableTopology y
    ∀ g : UnstableAsymptoticLeaf f.toHomeomorph x → UnstableAsymptoticLeaf f.toHomeomorph y,
      Continuous (fun z ↦ (g z).val) → Continuous g := by
  letI := A.realAmbientCharts
  letI := A.unstableTopology x
  letI := A.unstableCharts x
  letI := A.unstableTopology y
  letI := (A.nativeU y).secondCountable
  letI : LocallyConnectedSpace (UnstableAsymptoticLeaf f.toHomeomorph x) :=
    ChartedSpace.locallyConnectedSpace (Fin (A.nativeU x).rank → ℝ) _
  intro g hg
  let e := A.unstableClassHomeomorph y
  letI : SecondCountableTopology (A.F.ULeaf y) := e.secondCountableTopology
  have he (z : UnstableAsymptoticLeaf f.toHomeomorph y) : (e.symm z).val = z.val := by
    have h := A.unstable_points y (e.symm z)
    change (e (e.symm z)).val = _ at h
    simpa only [e.apply_symm_apply] using h.symm
  have hcomp : Continuous (e.symm ∘ g) := by
    apply continuous_unstable_leaf_lift_g1 A.F (Quotient.mk A.F.unstablePartition y)
      inferInstance (e.symm ∘ g)
    simpa only [Function.comp_apply, he] using hg
  simpa only [Function.comp_def, e.apply_symm_apply] using e.continuous.comp hcomp

omit [CompactSpace M] in
/-- Every forward iterate restricts to a smooth diffeomorphism between the corresponding
intrinsic unstable asymptotic leaves. -/
theorem native_unstable_iterate_diffeomorph_g18 (n : ℕ) (x : M) :
    letI := A.unstableTopology x
    letI := A.unstableCharts x
    letI := A.unstableTopology ((f^[n]) x)
    letI := A.unstableCharts ((f^[n]) x)
    ∃ e : Diffeomorph 𝓘(ℝ, Fin (A.nativeU x).rank → ℝ)
      𝓘(ℝ, Fin (A.nativeU ((f^[n]) x)).rank → ℝ)
      (UnstableAsymptoticLeaf f.toHomeomorph x)
      (UnstableAsymptoticLeaf f.toHomeomorph ((f^[n]) x)) ∞,
      ∀ z, (e z).val = (f^[n]) z.val := by
  letI := A.unstableTopology x
  letI := A.unstableCharts x
  letI := A.unstableTopology ((f^[n]) x)
  letI := A.unstableCharts ((f^[n]) x)
  have hf (k : ℕ) (a b : M) :
      ForwardAsymptotic f.symm ((f^[k]) a) ((f^[k]) b) ↔ ForwardAsymptotic f.symm a b := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have h := StableFoliationsSupport.forwardAsymptotic_apply_iff
        (f.symm : M → M) (f ((f^[k]) a)) (f ((f^[k]) b))
      simp only [f.symm_apply_apply] at h
      exact h.symm.trans ih
  have hi (k : ℕ) (a b : M) :
      ForwardAsymptotic f.symm ((f.symm^[k]) a) ((f.symm^[k]) b) ↔ ForwardAsymptotic f.symm a b := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (StableFoliationsSupport.forwardAsymptotic_apply_iff f.symm _ _).trans ih
  have hinv : Function.LeftInverse (f.symm : M → M) f := f.symm_apply_apply
  have hinv' : Function.RightInverse (f.symm : M → M) f := f.apply_symm_apply
  let e : UnstableAsymptoticLeaf f.toHomeomorph x ≃
      UnstableAsymptoticLeaf f.toHomeomorph ((f^[n]) x) := {
    toFun := fun z ↦ ⟨(f^[n]) z.val, (hf n x z.val).mpr z.property⟩
    invFun := fun z ↦ ⟨(f.symm^[n]) z.val, by
      have h := (hi n ((f^[n]) x) z.val).mpr z.property
      change ForwardAsymptotic (f.symm : M → M) x _
      simpa only [hinv.iterate n x] using h⟩
    left_inv := fun z ↦ Subtype.ext (hinv.iterate n z.val)
    right_inv := fun z ↦ Subtype.ext (hinv'.iterate n z.val) }
  have he : Continuous e := native_unstable_continuous_lift_g18 A x ((f^[n]) x) e
    ((f.continuous.iterate n).comp (A.nativeU x).inclusion_smooth.continuous)
  have hei : Continuous e.symm := native_unstable_continuous_lift_g18 A ((f^[n]) x) x e.symm
    ((f.symm.continuous.iterate n).comp (A.nativeU ((f^[n]) x)).inclusion_smooth.continuous)
  refine ⟨{ toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }, fun _ ↦ rfl⟩
  · intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt ((A.nativeU ((f^[n]) x)).inclusion_immersion (e z))).mpr
    exact ⟨he.continuousAt, ((f.toReal.contMDiff.iterate n).comp (A.nativeU x).inclusion_smooth) z⟩
  · intro z
    apply (ContMDiffAt.iff_comp_isImmersionAt ((A.nativeU x).inclusion_immersion (e.symm z))).mpr
    exact ⟨hei.continuousAt, ((f.toReal.symm.contMDiff.iterate n).comp
      (A.nativeU ((f^[n]) x)).inclusion_smooth) z⟩
/-- The family of intrinsic leaves and smooth unstable iterate maps associated with a
transverse asymptotic identification. -/
def rankOneNativeLeavesOfIdentification_g18 : RankOneNativeLeaves f S where
  stableDimension := s
  identification := A
  iterateUnstable := fun n x ↦ Classical.choose (native_unstable_iterate_diffeomorph_g18 A n x)
  iterateUnstable_points := fun n x ↦ Classical.choose_spec (native_unstable_iterate_diffeomorph_g18 A n x)

end HolomorphicAnosov.Ghys


namespace HolomorphicAnosov.Ghys
universe u
open scoped ContDiff
variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real
omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
/-- Positive-iterate Hermitian Anosov estimates imply tensor Anosov bounds in the associated
smooth real Riemannian metric. -/
theorem hermitian_tensor_bounds_g18
    (f : Biholomorph d d M M) (hmetric : HermitianTangentMetricCore d M)
    (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric)
    (S : InvariantRealTangentSplitting f.toReal)
    (hAnosov : HermitianAllTimeAnosov f hmetric S) :
    Nonempty (TensorAnosovBounds f.toReal S
      (StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth)) := by
  obtain ⟨C, expansion, hC, hexpansion, hs, hu⟩ := hAnosov
  have hexpansion_pos : 0 < expansion := lt_trans zero_lt_one hexpansion
  have hrate : 0 < expansion⁻¹ ∧ expansion⁻¹ < 1 :=
    ⟨inv_pos.mpr hexpansion_pos, (inv_lt_one₀ hexpansion_pos).mpr hexpansion⟩
  
  have hs_all : ∀ (n : ℕ) (x : M) (v : TangentSpace (realModel d) x),
      v ∈ S.stable.toDistribution x →
      givenHermitianNorm hmetric ((f^[n]) x)
          (mfderiv (realModel d) (realModel d) (f^[n]) x v) ≤
        max C 1 * (expansion⁻¹) ^ n * givenHermitianNorm hmetric x v := by
    intro n x v hv
    cases n with
    | zero =>
      simp only [Function.iterate_zero, mfderiv_id, pow_zero, mul_one]
      change Real.sqrt (hermitianTangentRealPairing hmetric x v v) ≤
        max C 1 * Real.sqrt (hermitianTangentRealPairing hmetric x v v)
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (le_max_right C 1)
          (Real.sqrt_nonneg (hermitianTangentRealPairing hmetric x v v)))
    | succ n =>
      have h := hs (n + 1) (Nat.succ_pos n) x v hv
      simp only [zpow_neg, zpow_natCast, ← inv_pow] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1)
          (pow_nonneg hrate.1.le _))
        (Real.sqrt_nonneg (hermitianTangentRealPairing hmetric x v v)))
  have hu_all : ∀ (n : ℕ) (x : M) (v : TangentSpace (realModel d) x),
      v ∈ S.unstable.toDistribution x →
      givenHermitianNorm hmetric ((f.symm^[n]) x)
          (mfderiv (realModel d) (realModel d) (f.symm^[n]) x v) ≤
        max C 1 * (expansion⁻¹) ^ n * givenHermitianNorm hmetric x v := by
    intro n x v hv
    cases n with
    | zero =>
      simp only [Function.iterate_zero, mfderiv_id, pow_zero, mul_one]
      change Real.sqrt (hermitianTangentRealPairing hmetric x v v) ≤
        max C 1 * Real.sqrt (hermitianTangentRealPairing hmetric x v v)
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (le_max_right C 1)
          (Real.sqrt_nonneg (hermitianTangentRealPairing hmetric x v v)))
    | succ n =>
      have h := hu (n + 1) (Nat.succ_pos n) x v hv
      simp only [zpow_neg, zpow_natCast, ← inv_pow] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1)
          (pow_nonneg hrate.1.le _))
        (Real.sqrt_nonneg (hermitianTangentRealPairing hmetric x v v)))
  let g := StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth
  have hb : Nonempty (TensorAnosovBounds f.toReal S g) := by
    refine ⟨⟨max C 1, expansion⁻¹, lt_of_lt_of_le hC (le_max_left _ _),
      hrate.1, hrate.2, ?_, ?_⟩⟩
    · intro n x v hv
      simp only [g, StableFoliationsSupport.originalSmoothRealMetric_inner]
      exact hs_all n x v hv
    · intro n x v hv
      simp only [g, StableFoliationsSupport.originalSmoothRealMetric_inner]
      exact hu_all n x v hv
  exact hb

theorem exists_rank_one_native_leaves_g18
    (f : Biholomorph d d M M) (hmetric : HermitianTangentMetricCore d M)
    (hmetric_smooth : IsSmoothHermitianTangentMetric hmetric)
    (S : InvariantRealTangentSplitting f.toReal)
    (hAnosov : HermitianAllTimeAnosov f hmetric S)
    (hRank : HasComplexRankOne S.unstable.toDistribution) :
    letI : MetricSpace M := rankComparisonMetric (d := d)
    Nonempty M → Nonempty (RankOneNativeLeaves f S) := by
  classical
  let : MetricSpace M := rankComparisonMetric (d := d)
  intro hM
  let g := StableFoliationsSupport.originalSmoothRealMetric hmetric hmetric_smooth
  have hb := hermitian_tensor_bounds_g18 f hmetric hmetric_smooth S hAnosov
  obtain ⟨a, ha, _⟩ := anosovDatum_of_tensorBounds_g18 f S g hb
  obtain ⟨x⟩ := hM
  have hrank : ∀ x, Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2 := by
    intro x
    rw [ha]
    exact TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hRank x
  obtain ⟨s, A, _⟩ := projective_native_identification f a x hrank
  exact ⟨by simpa only [ha] using rankOneNativeLeavesOfIdentification_g18 A⟩

end HolomorphicAnosov.Ghys
