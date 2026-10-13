import HolomorphicAnosov.Geometry.Riemannian.RiemannianEDistEqPiecewiseSmooth
import HolomorphicAnosov.Geometry.NativePlaqueConnectedCapture
import HolomorphicAnosov.Dynamics.BowenConnectedCoreSlices
import HolomorphicAnosov.Geometry.NativePlaqueFamilyMetricContraction
import HolomorphicAnosov.Geometry.Riemannian.LocalDerivativeDistanceBound
import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Dynamics.NativeLeafPathAdvanceEDist
import HolomorphicAnosov.Dynamics.NativeLeafPathEDistFinite
import HolomorphicAnosov.Dynamics.Anosov.InvariantRealTangentSplitting
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorDistance
import HolomorphicAnosov.Dynamics.Anosov.InverseDistributionInvariant
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothRiemannianEDistLePath
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Geometry.Riemannian.RiemannianEDistLePiecewiseSmooth
import HolomorphicAnosov.Dynamics.NativeLaminationLeafLift
import HolomorphicAnosov.Dynamics.NativeLeafPathEDistLocal
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ManifoldInverse
import HolomorphicAnosov.Geometry.OpenDiffeomorphMaximalChartField
import HolomorphicAnosov.Dynamics.ContinuousTangentSubbundleOnUniv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricContractingBracket
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowNegCoe
import HolomorphicAnosov.Dynamics.Bowen.CompactProductDataOfFactOne

namespace HolomorphicAnosov
universe u v

open Set
open scoped ContDiff Manifold ENNReal Bundle

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
variable [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]

/--
The native local geometry package used by the adapted orbit-plaque theorem.

Source: Hirsch--Pugh--Shub (1977), §§5--6B and Shub (1987), §§6 and 10.
The source construction chooses a common plaque radius, identifies the literal
stable and unstable orbit sets with embedded native plaques, and applies the
local product (bracket) argument.  It also gives finiteness of the intrinsic
piecewise-smooth path distance on each native leaf.  The detailed source
construction is recorded in the parent DAG node
`dynamics.hirsch_pugh_adapted_orbit_plaques_g2`; this theorem isolates that
remaining named obligation so the parent proof can consume it directly.

Statement correction: the previous unrestricted contract was false. Taking
`γCore = 0` contradicts `0 < γ ∧ γ ≤ γCore`, even on an empty manifold.
On the circle, the identity, the splitting `0 ⊕ TM`, and singleton stable
leaves also contradict `plaque_in_leaf`: every positive-radius orbit plaque
is an ordinary non-singleton ball. The corrected contract requires a positive
core bound, strict contraction of the actual stable and unstable derivatives,
and a compatible metric equal to the selected Riemannian distance on each
component. These are the hypotheses used by Shub Theorem 6.2, pp.71–72.

For nonempty M, apply the stable manifold graph construction to the adapted
tensor and its complementary invariant splitting. Unique local stable and
unstable integral plaques identify the supplied coherent leaf inclusions with
the source plaques. Compactness gives uniform enlarged charts and a common
positive radius, decreased below γCore. The strict derivative contraction
makes the small closed and open orbit cores the corresponding metric-ball
sections of each enlarged plaque. The local product construction and its
stable/unstable projections give the continuous bracket and its inverse as
in Shub Proposition 10.10, pp.126–127. Connected components are open; compactness
makes their number finite, so metric compatibility gives positive separation
between distinct components. Decrease the bracket radius to stay inside each
component. Intrinsic path-distance finiteness follows from the existing
nativeLeafPathEDist_lt_top theorem. The empty-manifold case is proved below.
-/
theorem hirschPughAdaptedOrbitPlaques_geometry
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (splitting : InvariantRealTangentSplitting f)
    (h : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x))
    (d : MetricSpace M) (γCore : ℝ)
    (hγCore : 0 < γCore)
    (hdtop : d.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M))
    (hdcomp : ∀ x y : M, y ∈ connectedComponent x →
      ENNReal.ofReal (d.dist x y) = piecewiseSmoothRiemannianEDist h x y)
    (θ : ℝ) (hθpos : 0 < θ) (hθlt : θ < 1)
    (hs : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      v ∈ splitting.stable.toDistribution x →
        hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) ≤
          θ * hyperbolicRiemannianNorm h v)
    (hu : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      v ∈ splitting.unstable.toDistribution x →
        hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f.symm x v) ≤
          θ * hyperbolicRiemannianNorm h v)
    (S : NativeInvariantLeafSystem 𝓘(ℝ, E) splitting.stable.toDistribution f)
    (U : NativeInvariantLeafSystem 𝓘(ℝ, E) splitting.unstable.toDistribution f.symm) :
    ∃ β γ ε : ℝ, 0 < γ ∧ γ ≤ γCore ∧ 2 * γ < β ∧ 0 < ε ∧
      Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f
        splitting.stable.toDistribution d β γ S) ∧
      Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm
        splitting.unstable.toDistribution d β γ U) ∧
      (∀ (x : M) (y z : (S.leaf x).Carrier),
        nativeLeafPathEDist 𝓘(ℝ, E) h (S.leaf x) y z < ⊤) ∧
      (∀ (x : M) (y z : (U.leaf x).Carrier),
        nativeLeafPathEDist 𝓘(ℝ, E) h (U.leaf x) y z < ⊤) ∧
      ∃ bracket : adaptedClosePairDomain (M := M) d ε → M,
        Continuous bracket ∧
        (∀ p : adaptedClosePairDomain (M := M) d ε,
          adaptedClosedOrbitCore 𝓘(ℝ, E) f d γ p.1.1 ∩
            adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm d γ p.1.2 = {bracket p}) ∧
        ∀ x : M, Nonempty (AdaptedNativeProduct 𝓘(ℝ, E) f
          splitting.stable.toDistribution splitting.unstable.toDistribution
          d γ ε S U bracket x) := by
  classical
  cases isEmpty_or_nonempty M with
  | inl hempty =>
    have stablePlaques : Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f
        splitting.stable.toDistribution d (2 * γCore) (γCore / 2) S) := by
      constructor
      constructor <;> intro x <;> exact isEmptyElim x
    have unstablePlaques : Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm
        splitting.unstable.toDistribution d (2 * γCore) (γCore / 2) U) := by
      constructor
      constructor <;> intro x <;> exact isEmptyElim x
    refine ⟨2 * γCore, γCore / 2, 1, by positivity, by linarith, by linarith,
      by norm_num, stablePlaques, unstablePlaques, ?_, ?_, ?_⟩
    · intro x
      exact isEmptyElim x
    · intro x
      exact isEmptyElim x
    · refine ⟨fun p ↦ isEmptyElim p.1.1, continuous_of_discreteTopology, ?_, ?_⟩
      · intro p
        exact isEmptyElim p.1.1
      · intro x
        exact isEmptyElim x
  | inr hnonempty =>
    have iterate_bound (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        (P : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
        (hP : ∀ x, (P x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x).toLinearMap = P (g x))
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ P x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (n : ℕ) (x : M) (v : TangentSpace 𝓘(ℝ, E) x) (hv : v ∈ P x) :
        hyperbolicRiemannianNorm h
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[n]) x v) ≤
          θ ^ n * hyperbolicRiemannianNorm h v := by
      induction n generalizing x with
      | zero =>
        simp only [Function.iterate_zero, mfderiv_id, pow_zero, one_mul]
        exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ, mfderiv_comp x
          ((g.contMDiff.iterate n).mdifferentiableAt (by simp))
          (g.contMDiff.mdifferentiableAt (by simp))]
        have hmem : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v ∈ P (g x) := by
          rw [← hP x]
          exact ⟨v, hv, rfl⟩
        calc
          _ ≤ θ ^ n * hyperbolicRiemannianNorm h
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) := ih (g x) _ hmem
          _ ≤ θ ^ n * (θ * hyperbolicRiemannianNorm h v) :=
            mul_le_mul_of_nonneg_left (hstep x v hv) (pow_nonneg hθpos.le n)
          _ = _ := by rw [pow_succ, mul_assoc]
    let bounds : TensorAnosovBounds f splitting h :=
      { C := 1
        lambda := θ
        C_pos := zero_lt_one
        lambda_pos := hθpos
        lambda_lt_one := hθlt
        stable := fun n x v hv ↦ by
          change hyperbolicRiemannianNorm h
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f : M → M)^[n]) x v) ≤
            1 * θ ^ n * hyperbolicRiemannianNorm h v
          simpa only [one_mul] using iterate_bound f splitting.stable.toDistribution splitting.stable_map hs n x v hv
        unstable := fun n x v hv ↦ by
          change hyperbolicRiemannianNorm h
              (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f.symm : M → M)^[n]) x v) ≤
            1 * θ ^ n * hyperbolicRiemannianNorm h v
          simpa only [one_mul] using iterate_bound f.symm splitting.unstable.toDistribution
            (FixedBlockEstimates.Inverse.inverse_distribution_invariant f
              splitting.unstable.toDistribution splitting.unstable_map) hu n x v hv }
    have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact E M
    have ambient_le_native {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        {x : M} (L : NativeSmoothLeaf 𝓘(ℝ, E) D x) (y z : L.Carrier) :
        piecewiseSmoothRiemannianEDist h (L.inclusion y) (L.inclusion z) ≤
          nativeLeafPathEDist 𝓘(ℝ, E) h L y z := by
      apply le_iInf
      intro p
      exact piecewiseSmoothRiemannianEDist_le_path h (p.map L.inclusion L.inclusion_smooth)
    have metric_le_native {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        {x : M} (L : NativeSmoothLeaf 𝓘(ℝ, E) D x) (y z : L.Carrier) :
        ENNReal.ofReal (d.dist (L.inclusion y) (L.inclusion z)) ≤
          nativeLeafPathEDist 𝓘(ℝ, E) h L y z := by
      have hcc : L.inclusion z ∈ connectedComponent (L.inclusion y) :=
        (isPreconnected_range L.inclusion_smooth.continuous).subset_connectedComponent
          (mem_range_self y) (mem_range_self z)
      rw [hdcomp _ _ hcc]
      exact ambient_le_native L y z
    have leaf_metric_estimate (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (n : ℕ) (x : M) (y z : (R.leaf x).Carrier) :
        ENNReal.ofReal (d.dist ((g : M → M)^[n] ((R.leaf x).inclusion y))
          ((g : M → M)^[n] ((R.leaf x).inclusion z))) ≤
            ENNReal.ofReal θ ^ n * nativeLeafPathEDist 𝓘(ℝ, E) h (R.leaf x) y z := by
      induction n generalizing x with
      | zero => simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using metric_le_native (R.leaf x) y z
      | succ n ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
          ← R.inclusion_advance x y, ← R.inclusion_advance x z]
        calc
          _ ≤ ENNReal.ofReal θ ^ n * nativeLeafPathEDist 𝓘(ℝ, E) h (R.leaf (g x))
              (R.advance x y) (R.advance x z) := ih (g x) _ _
          _ ≤ ENNReal.ofReal θ ^ n * (ENNReal.ofReal θ * nativeLeafPathEDist 𝓘(ℝ, E) h (R.leaf x) y z) :=
            mul_le_mul_right (nativeLeafPathEDist_advance_le g R h hθpos hstep x y z) _
          _ = _ := by rw [pow_succ, mul_assoc]
    have leaf_asymptotic (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (x : M) (y z : (R.leaf x).Carrier) :
        Filter.Tendsto (fun n : ℕ ↦ piecewiseSmoothRiemannianEDist h
          ((g : M → M)^[n] ((R.leaf x).inclusion y))
          ((g : M → M)^[n] ((R.leaf x).inclusion z))) Filter.atTop (nhds 0) := by
      let Pair := Σ x : M, (R.leaf x).Carrier × (R.leaf x).Carrier
      let advance : Pair → Pair := fun p ↦
        ⟨g p.1, R.advance p.1 p.2.1, R.advance p.1 p.2.2⟩
      let δ : Pair → ℝ≥0∞ := fun p ↦ nativeLeafPathEDist 𝓘(ℝ, E) h (R.leaf p.1) p.2.1 p.2.2
      let left : Pair → M := fun p ↦ (R.leaf p.1).inclusion p.2.1
      let right : Pair → M := fun p ↦ (R.leaf p.1).inclusion p.2.2
      have hδ (p : Pair) : δ (advance p) ≤ ENNReal.ofReal θ * δ p :=
        nativeLeafPathEDist_advance_le g R h hθpos hstep p.1 p.2.1 p.2.2
      have hδn (n : ℕ) (p : Pair) : δ (advance^[n] p) ≤ ENNReal.ofReal θ ^ n * δ p := by
        induction n generalizing p with
        | zero => simp
        | succ n ih =>
          rw [Function.iterate_succ_apply']
          calc
            _ ≤ ENNReal.ofReal θ * δ (advance^[n] p) := hδ _
            _ ≤ ENNReal.ofReal θ * (ENNReal.ofReal θ ^ n * δ p) := mul_le_mul_right (ih p) _
            _ = _ := by rw [pow_succ']; ac_rfl
      have hleft (n : ℕ) (p : Pair) : left (advance^[n] p) = (g : M → M)^[n] (left p) := by
        induction n generalizing p with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
          congr 1
          exact R.inclusion_advance p.1 p.2.1
      have hright (n : ℕ) (p : Pair) : right (advance^[n] p) = (g : M → M)^[n] (right p) := by
        induction n generalizing p with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
          congr 1
          exact R.inclusion_advance p.1 p.2.2
      let p : Pair := ⟨x, y, z⟩
      have hbound (n : ℕ) : piecewiseSmoothRiemannianEDist h
          ((g : M → M)^[n] ((R.leaf x).inclusion y))
          ((g : M → M)^[n] ((R.leaf x).inclusion z)) ≤ ENNReal.ofReal θ ^ n * δ p := by
        rw [← hleft n p, ← hright n p]
        exact (ambient_le_native _ _ _).trans (hδn n p)
      have hzero : Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal θ ^ n * δ p)
          Filter.atTop (nhds 0) := by
        have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          ((ENNReal.ofReal_lt_one).mpr hθlt)
        simpa using ENNReal.Tendsto.mul_const hpow (Or.inr
          (ne_of_lt (nativeLeafPathEDist_lt_top h (R.leaf x) y z)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
        (fun _ ↦ bot_le) hbound
    have intrinsic_orbit_open (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (β : ℝ) (hβ : 0 < β) (x : M) :
        IsOpen ((R.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x) := by
      let : MetricSpace M := d.replaceTopology hdtop.symm
      rw [isOpen_iff_mem_nhds]
      intro z hz
      let δ := nativeLeafPathEDist 𝓘(ℝ, E) h (R.leaf x) z (R.leaf x).point
      have hzero : Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal θ ^ n * δ)
          Filter.atTop (nhds 0) := by
        have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          ((ENNReal.ofReal_lt_one).mpr hθlt)
        simpa using ENNReal.Tendsto.mul_const hpow (Or.inr
          (ne_of_lt (nativeLeafPathEDist_lt_top h (R.leaf x) z (R.leaf x).point)))
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        (hzero.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hβ))))
      have hearly : ∀ᶠ y in nhds z, ∀ n : Fin N,
          d.dist ((g : M → M)^[n.val] ((R.leaf x).inclusion y))
            ((g : M → M)^[n.val] x) < β := by
        apply Filter.eventually_all.mpr
        intro n
        have hc : Continuous (fun y : (R.leaf x).Carrier ↦
            d.dist ((g : M → M)^[n.val] ((R.leaf x).inclusion y)) ((g : M → M)^[n.val] x)) :=
          ((g.continuous.iterate n.val).comp (R.leaf x).inclusion_smooth.continuous).dist continuous_const
        exact hc.continuousAt.eventually (gt_mem_nhds (hz n.val))
      filter_upwards [hearly, nativeLeafPathEDist_small h (R.leaf x) z (β / 2) (half_pos hβ)] with y hy hsmall
      intro n
      by_cases hn : n < N
      · exact hy ⟨n, hn⟩
      · have htail : d.dist ((g : M → M)^[n] ((R.leaf x).inclusion z))
            ((g : M → M)^[n] x) < β / 2 := by
          apply (ENNReal.ofReal_lt_ofReal_iff (half_pos hβ)).mp
          have hb := leaf_metric_estimate g R hstep n x z (R.leaf x).point
          rw [(R.leaf x).inclusion_point] at hb
          exact hb.trans_lt (hN n (le_of_not_gt hn))
        have hnear : d.dist ((g : M → M)^[n] ((R.leaf x).inclusion z))
            ((g : M → M)^[n] ((R.leaf x).inclusion y)) < β / 2 := by
          apply (ENNReal.ofReal_lt_ofReal_iff (half_pos hβ)).mp
          apply (leaf_metric_estimate g R hstep n x z y).trans_lt
          have hp : ENNReal.ofReal θ ^ n ≤ 1 :=
            pow_le_one₀ zero_le ((ENNReal.ofReal_le_one).mpr hθlt.le)
          exact (mul_le_of_le_one_left zero_le hp).trans_lt hsmall
        calc
          _ ≤ d.dist ((g : M → M)^[n] ((R.leaf x).inclusion y))
                ((g : M → M)^[n] ((R.leaf x).inclusion z)) +
              d.dist ((g : M → M)^[n] ((R.leaf x).inclusion z)) ((g : M → M)^[n] x) := dist_triangle _ _ _
          _ < β / 2 + β / 2 := add_lt_add (by simpa only [dist_comm] using hnear) htail
          _ = β := add_halves _
    have source_leaf_equiv
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        {ιs : Type _} {Ls : ιs → Type _} {rs : ιs → ℕ}
        [∀ i, TopologicalSpace (Ls i)] [∀ i, ChartedSpace (Fin (rs i) → ℝ) (Ls i)]
        [∀ i, IsManifold 𝓘(ℝ, Fin (rs i) → ℝ) ∞ (Ls i)]
        (Fs : HPS.LeafPartition D ιs Ls rs)
        {βs : Type _} {ds : βs → ℕ} {Ts : βs → Type _} [∀ b, TopologicalSpace (Ts b)]
        (Bs : HPS.LaminationBoxes Fs βs ds Ts) (label : M → ιs)
        (hcontains : ∀ x (y : (R.leaf x).Carrier),
          (R.leaf x).inclusion y ∈ range (Fs.leaf (label x)).inclusion) :
        ∀ x : M, ∃ e : Diffeomorph 𝓘(ℝ, Fin (R.leaf x).rank → ℝ)
            𝓘(ℝ, Fin (rs (label x)) → ℝ) (R.leaf x).Carrier (Ls (label x)) ∞,
          ∀ y, (Fs.leaf (label x)).inclusion (e y) = (R.leaf x).inclusion y := by
      let liftS (x : M) (y : (R.leaf x).Carrier) : Ls (label x) :=
        (hcontains x y).choose
      have liftS_eq (x : M) (y : (R.leaf x).Carrier) :
          (Fs.leaf (label x)).inclusion (liftS x y) = (R.leaf x).inclusion y :=
        (hcontains x y).choose_spec
      have liftS_smooth (x : M) :
          ContMDiff 𝓘(ℝ, Fin (R.leaf x).rank → ℝ)
            𝓘(ℝ, Fin (rs (label x)) → ℝ) ∞ (liftS x) := by
        have : LocallyConnectedSpace (R.leaf x).Carrier :=
          ChartedSpace.locallyConnectedSpace (Fin (R.leaf x).rank → ℝ) (R.leaf x).Carrier
        apply HPS.native_lamination_leaf_lift_contMDiff Fs Bs (label x)
        have heq : (Fs.leaf (label x)).inclusion ∘ liftS x = (R.leaf x).inclusion :=
          funext (liftS_eq x)
        rw [heq]
        exact (R.leaf x).inclusion_smooth
      have liftS_local (x : M) : IsLocalDiffeomorph
          𝓘(ℝ, Fin (R.leaf x).rank → ℝ) 𝓘(ℝ, Fin (rs (label x)) → ℝ)
          ∞ (liftS x) := by
        intro y
        let A := mfderiv 𝓘(ℝ, Fin (R.leaf x).rank → ℝ) 𝓘(ℝ, E) (R.leaf x).inclusion y
        let B := mfderiv 𝓘(ℝ, Fin (rs (label x)) → ℝ) 𝓘(ℝ, E)
          (Fs.leaf (label x)).inclusion (liftS x y)
        let C := mfderiv 𝓘(ℝ, Fin (R.leaf x).rank → ℝ)
          𝓘(ℝ, Fin (rs (label x)) → ℝ) (liftS x) y
        have hchain : B.comp C = A := by
          rw [← mfderiv_comp y
            ((Fs.leaf (label x)).immersion.contMDiff.mdifferentiableAt (by simp))
            ((liftS_smooth x).mdifferentiableAt (by simp))]
          congr 1
          exact funext (liftS_eq x)
        have hbij : Function.Bijective C := by
          constructor
          · intro v w hvw
            apply (R.leaf x).inclusion_immersed y
            change A v = A w
            rw [← hchain]
            exact congrArg B hvw
          · intro w
            have hmem : B w ∈ D ((R.leaf x).inclusion y) := by
              rw [← liftS_eq x y, ← (Fs.leaf (label x)).tangent]
              exact ⟨w, rfl⟩
            rw [← (R.leaf x).inclusion_tangent y] at hmem
            obtain ⟨v, hv⟩ := hmem
            refine ⟨v, ?_⟩
            apply (Fs.leaf (label x)).immersion.mfderiv_injective (by simp) (liftS x y)
            change B (C v) = B w
            change (B.comp C) v = B w
            rw [hchain]
            exact hv
        let a := (LinearEquiv.ofBijective C.toLinearMap hbij).toContinuousLinearEquiv
        obtain ⟨e, hy, _, he⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph
          isOpen_univ (Set.mem_univ y) (liftS_smooth x).contMDiffOn a (by rfl)
        exact ⟨e, hy, he⟩
      have rebase_range (x : M) (y : (R.leaf x).Carrier) :
          range (R.leaf ((R.leaf x).inclusion y)).inclusion = range (R.leaf x).inclusion := by
        ext z
        constructor
        · rintro ⟨w, rfl⟩
          obtain ⟨v, rfl⟩ := (R.rebase x y).surjective w
          exact ⟨v, (R.inclusion_rebase x y v).symm⟩
        · rintro ⟨v, rfl⟩
          exact ⟨R.rebase x y v, R.inclusion_rebase x y v⟩
      have range_overlap (x z : M) (a : (R.leaf x).Carrier) (b : (R.leaf z).Carrier)
          (heq : (R.leaf x).inclusion a = (R.leaf z).inclusion b) :
          range (R.leaf x).inclusion = range (R.leaf z).inclusion := by
        rw [← rebase_range x a, ← rebase_range z b, heq]
      have liftS_bijective (x : M) : Function.Bijective (liftS x) := by
        have hinj : Function.Injective (liftS x) := by
          intro y z heq
          apply (R.leaf x).inclusion_injective
          rw [← liftS_eq x y, ← liftS_eq x z, heq]
        refine ⟨hinj, ?_⟩
        have : ConnectedSpace (Ls (label x)) :=
          (Fs.leaf (label x)).connected
        have hopen := (liftS_local x).isOpen_range
        have hclosed : IsClosed (range (liftS x)) := by
          apply isOpen_compl_iff.mp
          rw [isOpen_iff_mem_nhds]
          intro a ha
          let z := (Fs.leaf (label x)).inclusion a
          have hlabel : label z = label x := by
            apply Fs.disjoint _ _ (liftS z (R.leaf z).point) a
            rw [liftS_eq, (R.leaf z).inclusion_point]
          let liftZ (v : (R.leaf z).Carrier) : Ls (label x) := hlabel ▸ liftS z v
          have hfactor (v : (R.leaf z).Carrier) :
              (Fs.leaf (label x)).inclusion (liftZ v) = (R.leaf z).inclusion v := by
            have hgeneral (j : ιs) (hj : label z = j) :
                (Fs.leaf j).inclusion (hj ▸ liftS z v) = (R.leaf z).inclusion v := by
              subst j
              exact liftS_eq z v
            exact hgeneral _ hlabel
          have hZopen : IsOpen (range liftZ) := by
            have hgeneral (j : ιs) (hj : label z = j) :
                IsOpen (range (fun v : (R.leaf z).Carrier ↦ (hj ▸ liftS z v : Ls j))) := by
              subst j
              exact (liftS_local z).isOpen_range
            exact hgeneral _ hlabel
          have haZ : a ∈ range liftZ := by
            refine ⟨(R.leaf z).point, ?_⟩
            apply (Fs.leaf (label x)).injective
            rw [hfactor, (R.leaf z).inclusion_point]
          have hsub : range liftZ ⊆ (range (liftS x))ᶜ := by
            rintro c ⟨v, rfl⟩ ⟨w, hw⟩
            have heq : (R.leaf x).inclusion w = (R.leaf z).inclusion v := by
              rw [← liftS_eq x w, hw, hfactor]
            have hz : z ∈ range (R.leaf x).inclusion := by
              rw [range_overlap x z w v heq]
              exact ⟨(R.leaf z).point, (R.leaf z).inclusion_point⟩
            obtain ⟨u, hu⟩ := hz
            apply ha
            refine ⟨u, ?_⟩
            apply (Fs.leaf (label x)).injective
            rw [liftS_eq, hu]
          exact Filter.mem_of_superset (hZopen.mem_nhds haZ) hsub
        have hall := (show IsClopen (range (liftS x)) from ⟨hclosed, hopen⟩).eq_univ
          ⟨liftS x (R.leaf x).point, mem_range_self _⟩
        intro y
        have hy : y ∈ range (liftS x) := hall.symm ▸ mem_univ y
        exact hy
      intro x
      refine ⟨(liftS_local x).diffeomorphOfBijective (liftS_bijective x), ?_⟩
      exact liftS_eq x
    have intrinsic_chart_of_source
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
        (L : NativeSmoothLeaf 𝓘(ℝ, E) D x) {r k : ℕ}
        {Y : Type v} [TopologicalSpace Y] [ChartedSpace (Fin r → ℝ) Y]
        [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ Y]
        (j : Y → M) (P : NativeEmbeddedPlaque 𝓘(ℝ, E) (V := Fin k → ℝ) D x)
        (O : TopologicalSpace.Opens Y)
        (chart : Diffeomorph 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, Fin r → ℝ)
          (⟨P.domain, P.domain_open⟩ : TopologicalSpace.Opens (Fin k → ℝ)) O ∞)
        (hchart : ∀ v, j (chart v) = P.param v)
        (e : Diffeomorph 𝓘(ℝ, Fin L.rank → ℝ) 𝓘(ℝ, Fin r → ℝ) L.Carrier Y ∞)
        (he : ∀ y, j (e y) = L.inclusion y) :
        ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E) (W := Fin L.rank → ℝ)
          (L := L.Carrier) D x P, T.inclusion = L.inclusion := by
      have hkr : k = r := by
        have hh := (chart.mfderivToContinuousLinearEquiv (by simp)
          (⟨0, P.zero_mem⟩ : P.domain)).toLinearEquiv.finrank_eq
        change Module.finrank ℝ (Fin k → ℝ) = Module.finrank ℝ (Fin r → ℝ) at hh
        simpa only [Module.finrank_fin_fun] using hh
      subst r
      obtain ⟨c, hc, hcsource, hctarget, hcval, _⟩ := open_diffeomorph_maximal_chart_field
        (⟨P.domain, P.domain_open⟩ : TopologicalSpace.Opens (Fin k → ℝ)) O
        ⟨0, P.zero_mem⟩ chart
      change c.target = P.domain at hctarget
      have himage : (e.symm ∘ c.symm) '' P.domain = e.symm '' c.source := by
        rw [Set.image_comp, ← hctarget, c.symm_image_target_eq_source]
      refine ⟨{
        inclusion := L.inclusion
        inclusion_smooth := L.inclusion_smooth
        inclusion_injective := L.inclusion_injective
        inclusion_immersed := L.inclusion_immersed
        inclusion_tangent := L.inclusion_tangent
        toLeaf := e.symm ∘ c.symm
        leafImage_open := ?_
        toLeaf_smooth := ?_
        inverse := c ∘ e
        inverse_smooth := ?_
        inverse_toLeaf := ?_
        toLeaf_inverse := ?_
        inclusion_toLeaf := ?_ }, rfl⟩
      · rw [himage]
        exact e.symm.toHomeomorph.isOpenMap _ c.open_source
      · apply e.symm.contMDiff.comp_contMDiffOn
        rw [← hctarget]
        exact contMDiffOn_symm_of_mem_maximalAtlas hc
      · apply (contMDiffOn_of_mem_maximalAtlas hc).comp e.contMDiff.contMDiffOn
        rintro y ⟨v, hv, rfl⟩
        change e (e.symm (c.symm v)) ∈ c.source
        rw [e.apply_symm_apply]
        exact c.map_target (hctarget.symm ▸ hv)
      · intro v hv
        change c (e (e.symm (c.symm v))) = v
        rw [e.apply_symm_apply]
        exact c.right_inv (hctarget.symm ▸ hv)
      · rintro y ⟨v, hv, rfl⟩
        change e.symm (c.symm (c (e (e.symm (c.symm v))))) = e.symm (c.symm v)
        rw [e.apply_symm_apply, c.right_inv (hctarget.symm ▸ hv)]
      · intro v hv
        change L.inclusion (e.symm (c.symm v)) = P.param v
        rw [← he, e.apply_symm_apply, hcval ⟨v, hv⟩]
        exact hchart ⟨v, hv⟩
    have restrict_native_chart
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
        (L : NativeSmoothLeaf 𝓘(ℝ, E) D x) {r : ℕ}
        (P : NativeEmbeddedPlaque 𝓘(ℝ, E) (V := Fin r → ℝ) D x)
        (T : NativePlaqueIntrinsicChart 𝓘(ℝ, E) (W := Fin L.rank → ℝ)
          (L := L.Carrier) D x P) (hT : T.inclusion = L.inclusion)
        (Q : Set M) (hxQ : x ∈ Q) (hQP : Q ⊆ P.image)
        (hopen : IsOpen (L.inclusion ⁻¹' Q)) :
        ∃ P' : NativeEmbeddedPlaque 𝓘(ℝ, E) (V := Fin r → ℝ) D x,
          P'.image = Q ∧ ∃ T' : NativePlaqueIntrinsicChart 𝓘(ℝ, E)
            (W := Fin L.rank → ℝ) (L := L.Carrier) D x P', T'.inclusion = L.inclusion := by
      let O := P.domain ∩ P.param ⁻¹' Q
      have hOeq : O = P.domain ∩ T.toLeaf ⁻¹' (L.inclusion ⁻¹' Q) := by
        ext v
        constructor
        · intro hv
          refine ⟨hv.1, ?_⟩
          change L.inclusion (T.toLeaf v) ∈ Q
          rw [← hT, T.inclusion_toLeaf v hv.1]
          exact hv.2
        · intro hv
          refine ⟨hv.1, ?_⟩
          change P.param v ∈ Q
          rw [← T.inclusion_toLeaf v hv.1, hT]
          exact hv.2
      have hO : IsOpen O := by
        rw [hOeq]
        exact T.toLeaf_smooth.continuousOn.isOpen_inter_preimage P.domain_open hopen
      let P' : NativeEmbeddedPlaque 𝓘(ℝ, E) (V := Fin r → ℝ) D x :=
        { domain := O
          domain_open := hO
          zero_mem := ⟨P.zero_mem, by simpa only [mem_preimage, P.centered] using hxQ⟩
          param := P.param
          centered := P.centered
          smooth := P.smooth.mono inter_subset_left
          embedded := P.embedded.comp (Topology.IsEmbedding.inclusion (show O ⊆ P.domain from inter_subset_left))
          immersed := fun v hv ↦ P.immersed v hv.1
          tangent := fun v hv ↦ P.tangent v hv.1 }
      have himage : T.toLeaf '' O = T.toLeaf '' P.domain ∩ L.inclusion ⁻¹' Q := by
        ext z
        constructor
        · rintro ⟨v, hv, rfl⟩
          refine ⟨⟨v,hv.1,rfl⟩, ?_⟩
          change L.inclusion (T.toLeaf v) ∈ Q
          rw [← hT, T.inclusion_toLeaf v hv.1]
          exact hv.2
        · rintro ⟨⟨v,hv,rfl⟩,hz⟩
          refine ⟨v, ⟨hv, ?_⟩, rfl⟩
          change L.inclusion (T.toLeaf v) ∈ Q at hz
          rwa [← hT, T.inclusion_toLeaf v hv] at hz
      refine ⟨P', ?_, ?_⟩
      · ext y
        constructor
        · rintro ⟨v,hv,rfl⟩; exact hv.2
        · intro hy
          obtain ⟨v,hv,rfl⟩ := hQP hy
          exact ⟨v, ⟨hv,hy⟩,rfl⟩
      · exact ⟨{
          inclusion := T.inclusion
          inclusion_smooth := T.inclusion_smooth
          inclusion_injective := T.inclusion_injective
          inclusion_immersed := T.inclusion_immersed
          inclusion_tangent := T.inclusion_tangent
          toLeaf := T.toLeaf
          leafImage_open := by change IsOpen (T.toLeaf '' O); rw [himage]; exact T.leafImage_open.inter hopen
          toLeaf_smooth := T.toLeaf_smooth.mono inter_subset_left
          inverse := T.inverse
          inverse_smooth := T.inverse_smooth.mono (image_mono inter_subset_left)
          inverse_toLeaf := fun v hv ↦ T.inverse_toLeaf v hv.1
          toLeaf_inverse := fun y hy ↦ T.toLeaf_inverse y (image_mono inter_subset_left hy)
          inclusion_toLeaf := fun v hv ↦ T.inclusion_toLeaf v hv.1 }, hT⟩
    let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
      ⟨h.toRiemannianMetric⟩
    have source_laminations := HPS.anosov_global_lamination_tensor_distance f splitting h ⟨bounds⟩
    obtain ⟨ιs, Ls, rs, tops, chartss, smooths, Fs, boxess, invariances,
      familiess, coherents, outputs⟩ := source_laminations.1
    let := tops
    let := chartss
    let := smooths
    obtain ⟨βs, ds, Ts, topTs, ⟨Bs⟩⟩ := boxess
    let := topTs
    obtain ⟨labels, discss, mapss, stagess, ⟨identifications, hlabels⟩, hgermss, hcoherents⟩ := outputs
    have source_contains (x : M) (y : (S.leaf x).Carrier) :
        (S.leaf x).inclusion y ∈ range (Fs.leaf (identifications.label x)).inclusion := by
      rw [identifications.equality x]
      change Filter.Tendsto (fun n : ℕ ↦ Manifold.riemannianEDist 𝓘(ℝ, E)
        ((f : M → M)^[n] ((S.leaf x).inclusion y)) ((f : M → M)^[n] x))
          Filter.atTop (nhds 0)
      have hps := leaf_asymptotic f S hs x y (S.leaf x).point
      rw [(S.leaf x).inclusion_point] at hps
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hps
        (fun _ ↦ bot_le) (fun n ↦ riemannianEDist_le_piecewiseSmoothRiemannianEDist h _ _)
    have stableSourceEquiv := source_leaf_equiv f S Fs Bs identifications.label source_contains
    obtain ⟨ιu, Lu, ru, topu, chartsu, smoothu, Fu, boxesu, invarianceu,
      familiesu, coherentu, outputu⟩ := source_laminations.2
    let := topu
    let := chartsu
    let := smoothu
    obtain ⟨βu, du, Tu, topTu, ⟨Bu⟩⟩ := boxesu
    let := topTu
    obtain ⟨labelu, discsu, mapsu, stagesu, ⟨identificationu, hlabelu⟩, hgermsu, hcoherentu⟩ := outputu
    have source_contains_u (x : M) (y : (U.leaf x).Carrier) :
        (U.leaf x).inclusion y ∈ range (Fu.leaf (identificationu.label x)).inclusion := by
      rw [identificationu.equality x]
      change Filter.Tendsto (fun n : ℕ ↦ Manifold.riemannianEDist 𝓘(ℝ, E)
        ((f.symm : M → M)^[n] ((U.leaf x).inclusion y)) ((f.symm : M → M)^[n] x))
          Filter.atTop (nhds 0)
      have hps := leaf_asymptotic f.symm U hu x y (U.leaf x).point
      rw [(U.leaf x).inclusion_point] at hps
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hps
        (fun _ ↦ bot_le) (fun n ↦ riemannianEDist_le_piecewiseSmoothRiemannianEDist h _ _)
    have unstableSourceEquiv := source_leaf_equiv f.symm U Fu Bu identificationu.label source_contains_u
    have stable_intrinsic_families (x : M) : ∃ r : ℕ,
        ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) splitting.stable.toDistribution x,
          ∀ p : F.centerDomain, ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E)
            (W := Fin (S.leaf p.1).rank → ℝ) (L := (S.leaf p.1).Carrier)
            splitting.stable.toDistribution p.1 (F.plaque p),
              T.inclusion = (S.leaf p.1).inclusion := by
      let Φ := familiess.family x
      refine ⟨familiess.dimension x, Φ.family, ?_⟩
      intro p
      have htag : Φ.label p = identifications.label p :=
        ((hgermss x).2 p).trans (congrFun hlabels p).symm
      obtain ⟨e, he⟩ : ∃ e : Diffeomorph 𝓘(ℝ, Fin (S.leaf p.1).rank → ℝ)
          𝓘(ℝ, Fin (rs (Φ.label p)) → ℝ) (S.leaf p.1).Carrier (Ls (Φ.label p)) ∞,
          ∀ y, (Fs.leaf (Φ.label p)).inclusion (e y) = (S.leaf p.1).inclusion y := by
        rw [htag]
        exact stableSourceEquiv p
      have hdata : ∃ chart : Diffeomorph 𝓘(ℝ, Fin (familiess.dimension x) → ℝ)
          𝓘(ℝ, Fin (rs (Φ.label p)) → ℝ)
          (⟨(Φ.family.plaque p).domain, (Φ.family.plaque p).domain_open⟩ :
            TopologicalSpace.Opens (Fin (familiess.dimension x) → ℝ)) (Φ.receivingPlaque p) ∞,
          ∀ v, (Fs.leaf (Φ.label p)).inclusion (chart v) = (Φ.family.plaque p).param v := by
        have hdom : (⟨(Φ.family.plaque p).domain, (Φ.family.plaque p).domain_open⟩ :
            TopologicalSpace.Opens _) = ⟨Metric.ball 0 Φ.family.radius, Metric.isOpen_ball⟩ := by
          apply SetLike.coe_injective
          exact Φ.family.domain_eq p
        rw [hdom]
        exact ⟨Φ.chart p, fun v ↦ (Φ.factorization p v).symm⟩
      obtain ⟨chart, hchart⟩ := hdata
      exact intrinsic_chart_of_source (S.leaf p.1) (Fs.leaf (Φ.label p)).inclusion
        (Φ.family.plaque p) (Φ.receivingPlaque p) chart hchart e he
    have unstable_intrinsic_families (x : M) : ∃ r : ℕ,
        ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) splitting.unstable.toDistribution x,
          ∀ p : F.centerDomain, ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E)
            (W := Fin (U.leaf p.1).rank → ℝ) (L := (U.leaf p.1).Carrier)
            splitting.unstable.toDistribution p.1 (F.plaque p),
              T.inclusion = (U.leaf p.1).inclusion := by
      let Φ := familiesu.family x
      refine ⟨familiesu.dimension x, Φ.family, ?_⟩
      intro p
      have htag : Φ.label p = identificationu.label p :=
        ((hgermsu x).2 p).trans (congrFun hlabelu p).symm
      obtain ⟨e, he⟩ : ∃ e : Diffeomorph 𝓘(ℝ, Fin (U.leaf p.1).rank → ℝ)
          𝓘(ℝ, Fin (ru (Φ.label p)) → ℝ) (U.leaf p.1).Carrier (Lu (Φ.label p)) ∞,
          ∀ y, (Fu.leaf (Φ.label p)).inclusion (e y) = (U.leaf p.1).inclusion y := by
        rw [htag]
        exact unstableSourceEquiv p
      have hdata : ∃ chart : Diffeomorph 𝓘(ℝ, Fin (familiesu.dimension x) → ℝ)
          𝓘(ℝ, Fin (ru (Φ.label p)) → ℝ)
          (⟨(Φ.family.plaque p).domain, (Φ.family.plaque p).domain_open⟩ :
            TopologicalSpace.Opens (Fin (familiesu.dimension x) → ℝ)) (Φ.receivingPlaque p) ∞,
          ∀ v, (Fu.leaf (Φ.label p)).inclusion (chart v) = (Φ.family.plaque p).param v := by
        have hdom : (⟨(Φ.family.plaque p).domain, (Φ.family.plaque p).domain_open⟩ :
            TopologicalSpace.Opens _) = ⟨Metric.ball 0 Φ.family.radius, Metric.isOpen_ball⟩ := by
          apply SetLike.coe_injective
          exact Φ.family.domain_eq p
        rw [hdom]
        exact ⟨Φ.chart p, fun v ↦ (Φ.factorization p v).symm⟩
      obtain ⟨chart, hchart⟩ := hdata
      exact intrinsic_chart_of_source (U.leaf p.1) (Fu.leaf (Φ.label p)).inclusion
        (Φ.family.plaque p) (Φ.receivingPlaque p) chart hchart e he
    obtain ⟨stableOn, hstableOn⟩ := continuousRealTangentSubbundle_on_univ splitting.stable
    obtain ⟨unstableOn, hunstableOn⟩ := continuousRealTangentSubbundle_on_univ splitting.unstable
    let H : HyperbolicSetFactOneDatum f Set.univ :=
      { nonempty := Set.univ_nonempty
        compact := isCompact_univ
        forward_mem := fun _ _ ↦ Set.mem_univ _
        backward_mem := fun _ _ ↦ Set.mem_univ _
        originalMetric := h
        stable := stableOn
        unstable := unstableOn
        complementary := fun x ↦ by
          rw [hstableOn, hunstableOn]
          exact splitting.isCompl x
        stable_invariant := fun x ↦ by
          rw [hstableOn, hstableOn]
          exact splitting.stable_map x
        unstable_invariant := fun x ↦ by
          rw [hunstableOn, hunstableOn]
          exact splitting.unstable_map x
        C := 1
        one_le_C := le_rfl
        rate := θ
        rate_pos := hθpos
        rate_lt_one := hθlt
        stable_estimate := fun n x v hv ↦ bounds.stable n x v (by simpa [hstableOn] using hv)
        unstable_estimate := fun n x v hv ↦ bounds.unstable n x v (by simpa [hunstableOn] using hv)
        isolatingNeighborhood := Set.univ
        isolating_open := isOpen_univ
        subset_isolating := Set.Subset.rfl
        locally_maximal := fun _ ↦ by simp }
    obtain ⟨hFact, aFact, dFact, κ, γFact, εFact, haFact, hsFact, huFact,
      htFact, hdFact, hκ, hκ1, hγFact, hεFact, hcontractS, hcontractU,
      bracketFact, hbracketFact, hsingleFact⟩ :=
      hirschPughHyperbolicSetFactOne f Set.univ H
    let dF : MetricSpace M := dFact.replaceTopology htFact.symm
    let : MetricSpace M := dF
    obtain ⟨βcapture, hβcapture, hcapture⟩ :=
      Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_modulus
        d hdtop γFact hγFact
    have native_orbit_equicontinuous
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (x : M) (z : (R.leaf x).Carrier) (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ y in nhds z, ∀ n : ℕ,
          dF.dist ((g : M → M)^[n] ((R.leaf x).inclusion z))
            ((g : M → M)^[n] ((R.leaf x).inclusion y)) < ε := by
      obtain ⟨δ, hδ, hmod⟩ :=
        Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_modulus d hdtop ε hε
      filter_upwards [nativeLeafPathEDist_small h (R.leaf x) z δ hδ] with y hy
      intro n
      apply hmod
      apply (ENNReal.ofReal_lt_ofReal_iff hδ).mp
      apply (leaf_metric_estimate g R hstep n x z y).trans_lt
      have hp : ENNReal.ofReal θ ^ n ≤ 1 :=
        pow_le_one₀ zero_le ((ENNReal.ofReal_le_one).mpr hθlt.le)
      exact (mul_le_of_le_one_left zero_le hp).trans_lt hy
    have fact_converges_to_source (a b : ℕ → M)
        (hab : Filter.Tendsto (fun n ↦ dF.dist (a n) (b n)) Filter.atTop (nhds 0)) :
        Filter.Tendsto (fun n ↦ Manifold.riemannianEDist 𝓘(ℝ, E) (a n) (b n))
          Filter.atTop (nhds 0) := by
      have hcont : IsContinuousRiemannianBundle E
          (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := by
        change letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
          ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
          IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
        infer_instance
      let eR : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
      have hc : @Continuous M M dF.toUniformSpace.toTopologicalSpace
          eR.toUniformSpace.toTopologicalSpace id := continuous_id
      have huc := @CompactSpace.uniformContinuous_of_continuous M M
        dF.toUniformSpace eR.toUniformSpace inferInstance id hc
      apply ENNReal.tendsto_nhds_zero.mpr
      intro ε hε
      obtain ⟨δ, hδ, hδε⟩ := (@Metric.mem_uniformity_dist M dF.toPseudoMetricSpace _).mp
        (huc (@edist_mem_uniformity M eR.toPseudoEMetricSpace ε hε))
      filter_upwards [hab.eventually (gt_mem_nhds hδ)] with n hn
      exact (hδε hn).le
    have fact_core_asymptotic
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        (x y : M)
        (hc : ∀ n : ℕ, dFact.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤
          κ ^ n * dFact.dist y x) :
        Filter.Tendsto (fun n : ℕ ↦ Manifold.riemannianEDist 𝓘(ℝ, E)
          ((g : M → M)^[n] y) ((g : M → M)^[n] x)) Filter.atTop (nhds 0) := by
      apply fact_converges_to_source
      have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hκ.le hκ1).mul_const (dFact.dist y x)
      simp only [zero_mul] at hz
      exact squeeze_zero (fun n ↦ @dist_nonneg M dF.toPseudoMetricSpace _ _) hc hz
    have fact_stable_core_in_leaf (x : M) :
        Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x ⊆ range (S.leaf x).inclusion := by
      intro y hy
      have hasym := fact_core_asymptotic f x y (fun n ↦
        hcontractS x (mem_univ _) y ⟨mem_univ _, hy⟩ x
          ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n)
      have hsource : y ∈ range (Fs.leaf (identifications.label x)).inclusion := by
        rw [identifications.equality x]
        exact hasym
      obtain ⟨z, rfl⟩ := hsource
      obtain ⟨e, he⟩ := stableSourceEquiv x
      exact ⟨e.symm z, by rw [← he, e.apply_symm_apply]⟩
    have fact_unstable_core_in_leaf (x : M) :
        Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x ⊆ range (U.leaf x).inclusion := by
      intro y hy
      have hasym := fact_core_asymptotic f.symm x y (fun n ↦
        hcontractU x (mem_univ _) y ⟨mem_univ _, hy⟩ x
          ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n)
      have hsource : y ∈ range (Fu.leaf (identificationu.label x)).inclusion := by
        rw [identificationu.equality x]
        exact hasym
      obtain ⟨z, rfl⟩ := hsource
      obtain ⟨e, he⟩ := unstableSourceEquiv x
      exact ⟨e.symm z, by rw [← he, e.apply_symm_apply]⟩
    have stable_continuous_lift {X : Type v} [TopologicalSpace X] [LocallyConnectedSpace X]
        (x : M) (a : X → M) (ha : Continuous a)
        (hr : ∀ t, a t ∈ range (S.leaf x).inclusion) :
        ∃ l : X → (S.leaf x).Carrier, Continuous l ∧ ∀ t, (S.leaf x).inclusion (l t) = a t := by
      let l : X → (S.leaf x).Carrier := fun t ↦ (hr t).choose
      have hl (t : X) : (S.leaf x).inclusion (l t) = a t := (hr t).choose_spec
      obtain ⟨e, he⟩ := stableSourceEquiv x
      have hc : Continuous (e ∘ l) := HPS.native_lamination_leaf_lift_continuous Fs Bs
        (identifications.label x) (e ∘ l) (by simpa only [Function.comp_def, he, hl] using ha)
      refine ⟨l, ?_, hl⟩
      simpa only [Function.comp_def, e.symm_apply_apply] using e.symm.continuous.comp hc
    have unstable_continuous_lift {X : Type v} [TopologicalSpace X] [LocallyConnectedSpace X]
        (x : M) (a : X → M) (ha : Continuous a)
        (hr : ∀ t, a t ∈ range (U.leaf x).inclusion) :
        ∃ l : X → (U.leaf x).Carrier, Continuous l ∧ ∀ t, (U.leaf x).inclusion (l t) = a t := by
      let l : X → (U.leaf x).Carrier := fun t ↦ (hr t).choose
      have hl (t : X) : (U.leaf x).inclusion (l t) = a t := (hr t).choose_spec
      obtain ⟨e, he⟩ := unstableSourceEquiv x
      have hc : Continuous (e ∘ l) := HPS.native_lamination_leaf_lift_continuous Fu Bu
        (identificationu.label x) (e ∘ l) (by simpa only [Function.comp_def, he, hl] using ha)
      refine ⟨l, ?_, hl⟩
      simpa only [Function.comp_def, e.symm_apply_apply] using e.symm.continuous.comp hc
    have capture_source (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        (hc : ∀ x y, (∀ n : ℕ, dFact.dist ((g : M → M)^[n] y)
            ((g : M → M)^[n] x) ≤ γFact) → ∀ n : ℕ,
          dFact.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤
            κ ^ n * dFact.dist y x)
        (x y : M) (hy : y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d βcapture x) :
        Filter.Tendsto (fun n : ℕ ↦ Manifold.riemannianEDist 𝓘(ℝ, E)
          ((g : M → M)^[n] y) ((g : M → M)^[n] x)) Filter.atTop (nhds 0) := by
      have hb := hc x y (fun n ↦ (hcapture _ _ (hy n)).le)
      apply fact_converges_to_source
      have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one hκ.le hκ1).mul_const (dFact.dist y x)
      simp only [zero_mul] at hz
      exact squeeze_zero (fun n ↦ @dist_nonneg M dF.toPseudoMetricSpace _ _) hb hz
    have stable_plaque_in_leaf (x : M) :
        adaptedOpenOrbitPlaque 𝓘(ℝ, E) f d βcapture x ⊆ range (S.leaf x).inclusion := by
      intro y hy
      have hasym := capture_source f (fun x y hy n ↦
        hcontractS x (mem_univ _) y ⟨mem_univ _, hy⟩ x
          ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n) x y hy
      have hsource : y ∈ range (Fs.leaf (identifications.label x)).inclusion := by
        rw [identifications.equality x]
        exact hasym
      obtain ⟨z, rfl⟩ := hsource
      obtain ⟨e, he⟩ := stableSourceEquiv x
      exact ⟨e.symm z, by rw [← he, e.apply_symm_apply]⟩
    have unstable_plaque_in_leaf (x : M) :
        adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm d βcapture x ⊆ range (U.leaf x).inclusion := by
      intro y hy
      have hasym := capture_source f.symm (fun x y hy n ↦
        hcontractU x (mem_univ _) y ⟨mem_univ _, hy⟩ x
          ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n) x y hy
      have hsource : y ∈ range (Fu.leaf (identificationu.label x)).inclusion := by
        rw [identificationu.equality x]
        exact hasym
      obtain ⟨z, rfl⟩ := hsource
      obtain ⟨e, he⟩ := unstableSourceEquiv x
      exact ⟨e.symm z, by rw [← he, e.apply_symm_apply]⟩
    let B : {p : M × M // dF.dist p.1 p.2 ≤ εFact} → M :=
      fun p ↦ (bracketFact ⟨p.val, mem_univ _, mem_univ _, p.property⟩).val
    have hB : Continuous B := continuous_subtype_val.comp
      (hbracketFact.comp (continuous_subtype_val.subtype_mk _))
    have hBmem (p : {p : M × M // dF.dist p.1 p.2 ≤ εFact}) :
        hyperbolicClosedStablePlaque f univ dFact γFact p.val.1 ∩
          hyperbolicClosedUnstablePlaque f univ dFact γFact p.val.2 = {B p} :=
      hsingleFact ⟨p.val, mem_univ _, mem_univ _, p.property⟩
    have hBdiag (x : M) : B ⟨(x, x), by simpa using hεFact.le⟩ = x := by
      apply Eq.symm
      have hself : x ∈ hyperbolicClosedStablePlaque f univ dFact γFact x ∩
          hyperbolicClosedUnstablePlaque f univ dFact γFact x :=
        ⟨⟨mem_univ _, fun n ↦ by simpa using hγFact.le⟩,
          ⟨mem_univ _, fun n ↦ by simpa using hγFact.le⟩⟩
      rwa [hBmem ⟨(x, x), by simpa using hεFact.le⟩] at hself
    have hBS (p : {p : M × M // dF.dist p.1 p.2 ≤ εFact}) (n : ℕ) :
        dF.dist ((f.toHomeomorph ^ (n : ℤ)) (B p))
          ((f.toHomeomorph ^ (n : ℤ)) p.val.1) ≤ κ ^ n * dF.dist (B p) p.val.1 := by
      have hm : B p ∈ hyperbolicClosedStablePlaque f univ dFact γFact p.val.1 ∩
          hyperbolicClosedUnstablePlaque f univ dFact γFact p.val.2 := by
        rw [hBmem]; exact mem_singleton _
      simpa only [zpow_natCast,
        Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe, Diffeomorph.coe_toHomeomorph] using
        hcontractS p.val.1 (mem_univ _) (B p) hm.1 p.val.1
          ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n
    have hBU (p : {p : M × M // dF.dist p.1 p.2 ≤ εFact}) (n : ℕ) :
        dF.dist ((f.toHomeomorph ^ (-(n : ℤ))) (B p))
          ((f.toHomeomorph ^ (-(n : ℤ))) p.val.2) ≤ κ ^ n * dF.dist (B p) p.val.2 := by
      have hm : B p ∈ hyperbolicClosedStablePlaque f univ dFact γFact p.val.1 ∩
          hyperbolicClosedUnstablePlaque f univ dFact γFact p.val.2 := by
        rw [hBmem]; exact mem_singleton _
      simpa only [Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_neg_coe, Diffeomorph.coe_toHomeomorph_symm] using
        hcontractU p.val.2 (mem_univ _) (B p) hm.2 p.val.2
          ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n
    let b : M → M → M := fun x y ↦ if hxy : dF.dist x y ≤ εFact then B ⟨(x,y), hxy⟩ else x
    have hb (x y : M) (hxy : dF.dist x y ≤ εFact) : b x y = B ⟨(x,y), hxy⟩ := dite_eq_left hxy
    have hbmem (x y : M) (hxy : dF.dist x y ≤ εFact) :
        b x y ∈ Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x ∩
          Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact y := by
      have hm : B ⟨(x,y), hxy⟩ ∈ hyperbolicClosedStablePlaque f univ dFact γFact x ∩
          hyperbolicClosedUnstablePlaque f univ dFact γFact y := by
        rw [hBmem ⟨(x,y),hxy⟩]; exact mem_singleton _
      rw [hb x y hxy]
      exact ⟨hm.1.2, hm.2.2⟩
    have hbuniq (x y z : M) (hxy : dF.dist x y ≤ εFact)
        (hz : z ∈ Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x ∩
          Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact y) : z = b x y := by
      rw [hb x y hxy]
      have hm : z ∈ hyperbolicClosedStablePlaque f univ dFact γFact x ∩
          hyperbolicClosedUnstablePlaque f univ dFact γFact y :=
        ⟨⟨mem_univ _, hz.1⟩, ⟨mem_univ _, hz.2⟩⟩
      rwa [hBmem ⟨(x,y),hxy⟩] at hm
    have hbcont : ContinuousOn (fun p : M × M ↦ b p.1 p.2)
        {p | dF.dist p.1 p.2 ≤ εFact} := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      exact hB.congr (fun p ↦ (hb _ _ p.property).symm)
    obtain ⟨prodFact⟩ := BowenBasicSetCoding.compact_product_data_of_factOne
      f.toHomeomorph γFact κ εFact hγFact hκ hκ1 hεFact b hbmem hbuniq hbcont
      (fun x y z hy hz n ↦ hcontractS x (mem_univ _) y ⟨mem_univ _, hy⟩ z ⟨mem_univ _, hz⟩ n)
      (fun x y z hy hz n ↦ hcontractU x (mem_univ _) y ⟨mem_univ _, hy⟩ z ⟨mem_univ _, hz⟩ n)
    have fact_core_collar_open
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (x : M) (ρ : ℝ) (hργ : ρ ≤ γFact)
        (hc : ∀ y, (∀ n : ℕ, dF.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤ γFact) →
          ∀ n : ℕ, dF.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤ κ ^ n * dF.dist y x) :
        IsOpen ((R.leaf x).inclusion ⁻¹'
          ({y | ∀ n : ℕ, dF.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤ γFact} ∩
            Metric.ball x ρ)) := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      have hgap : 0 < γFact - dF.dist ((R.leaf x).inclusion z) x :=
        sub_pos.mpr (hz.2.trans_le hργ)
      have hball : ∀ᶠ y in nhds z, dF.dist ((R.leaf x).inclusion y) x < ρ :=
        ((R.leaf x).inclusion_smooth.continuous.dist continuous_const).continuousAt.eventually
          (gt_mem_nhds hz.2)
      filter_upwards [native_orbit_equicontinuous g R hstep x z _ hgap, hball] with y hy hyball
      refine ⟨?_, hyball⟩
      intro n
      have hcenter := (hc _ hz.1 n).trans
        (mul_le_of_le_one_left (dist_nonneg : 0 ≤ dF.dist ((R.leaf x).inclusion z) x)
          (pow_le_one₀ hκ.le hκ1.le))
      have htri := dist_triangle ((g : M → M)^[n] ((R.leaf x).inclusion y))
        ((g : M → M)^[n] ((R.leaf x).inclusion z)) ((g : M → M)^[n] x)
      have hnear := hy n
      rw [dist_comm] at hnear
      linarith
    have fact_factors_locally_connected (x : M) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ γFact ∧
        LocallyConnectedSpace {u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x //
          dF.dist u.val x < ρ} ∧
        LocallyConnectedSpace {s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x //
          dF.dist s.val x < ρ} := by
      obtain ⟨ρ, hρ, hργ, hρε, hcharts⟩ := prodFact.product_chart x
      let U₀ : Set M := Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x ∩ Metric.ball x ρ
      let S₀ : Set M := Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x ∩ Metric.ball x ρ
      have hselfS : x ∈ Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x :=
        fun n ↦ by simpa using hγFact.le
      have hselfU : x ∈ Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x :=
        fun n ↦ by simpa using hγFact.le
      have hU : U₀ ⊆ Dynamics.relativeClosedUnstablePlaque f.toHomeomorph ρ x := by
        intro y hy n
        have hc := prodFact.unstable_contraction x y x hy.1 hselfU n
        exact hc.trans ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dF.dist y x)
          (pow_le_one₀ hκ.le hκ1.le)).trans hy.2.le)
      have hS : S₀ ⊆ Dynamics.relativeClosedStablePlaque f.toHomeomorph ρ x := by
        intro y hy n
        have hc := prodFact.stable_contraction x y x hy.1 hselfS n
        exact hc.trans ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dF.dist y x)
          (pow_le_one₀ hκ.le hκ1.le)).trans hy.2.le)
      have hUopen : IsOpen {u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x | u.val ∈ U₀} := by
        have heq : {u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x | u.val ∈ U₀} =
            Subtype.val ⁻¹' Metric.ball x ρ := by ext u; simp [U₀]
        rw [heq]
        exact Metric.isOpen_ball.preimage continuous_subtype_val
      have hSopen : IsOpen {s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x | s.val ∈ S₀} := by
        have heq : {s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x | s.val ∈ S₀} =
            Subtype.val ⁻¹' Metric.ball x ρ := by ext s; simp [S₀]
        rw [heq]
        exact Metric.isOpen_ball.preimage continuous_subtype_val
      obtain ⟨himage, chart, hchart⟩ := hcharts U₀ S₀ hU hS hUopen hSopen
      have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
      have : LocallyConnectedSpace {z : M // z ∈ image2 prodFact.bracket U₀ S₀} := himage.locallyConnectedSpace
      have hlocal := chart.isOpenEmbedding.locallyConnectedSpace
      have hUset : {u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x | u.val ∈ U₀} =
          {u | dF.dist u.val x < ρ} := by ext u; simp [U₀, Metric.mem_ball]
      have hSset : {s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x | s.val ∈ S₀} =
          {s | dF.dist s.val x < ρ} := by ext s; simp [S₀, Metric.mem_ball]
      change LocallyConnectedSpace
        (({u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x | u.val ∈ U₀} : Set _) ×
          ({s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x | s.val ∈ S₀} : Set _)) at hlocal
      rw [hUset, hSset] at hlocal
      let AU := {u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x // dF.dist u.val x < ρ}
      let AS := {s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x // dF.dist s.val x < ρ}
      have : Nonempty AU := ⟨⟨⟨x, hselfU⟩, by simpa using hρ⟩⟩
      have : Nonempty AS := ⟨⟨⟨x, hselfS⟩, by simpa using hρ⟩⟩
      have : LocallyConnectedSpace (AU × AS) := hlocal
      exact ⟨ρ, hρ, hργ,
        (@isQuotientMap_fst AU AS _ _ inferInstance).isCoinducing.locallyConnectedSpace,
        (@isQuotientMap_snd AU AS _ _ inferInstance).isCoinducing.locallyConnectedSpace⟩
    have fact_native_factors (x : M) : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ γFact ∧
        (∃ l : {s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x // dF.dist s.val x < ρ} →
            (S.leaf x).Carrier,
          Topology.IsOpenEmbedding l ∧ ∀ s, (S.leaf x).inclusion (l s) = s.val.val) ∧
        (∃ l : {u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x // dF.dist u.val x < ρ} →
            (U.leaf x).Carrier,
          Topology.IsOpenEmbedding l ∧ ∀ u, (U.leaf x).inclusion (l u) = u.val.val) := by
      obtain ⟨ρ, hρ, hργ, hlocalU, hlocalS⟩ := fact_factors_locally_connected x
      let AS := {s : Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x // dF.dist s.val x < ρ}
      let AU := {u : Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x // dF.dist u.val x < ρ}
      have : LocallyConnectedSpace AS := hlocalS
      have : LocallyConnectedSpace AU := hlocalU
      obtain ⟨ls, hls, hlsval⟩ := stable_continuous_lift x (fun s : AS ↦ s.val.val)
        (continuous_subtype_val.comp continuous_subtype_val) (fun s ↦ fact_stable_core_in_leaf x s.val.property)
      obtain ⟨lu, hlu, hluval⟩ := unstable_continuous_lift x (fun u : AU ↦ u.val.val)
        (continuous_subtype_val.comp continuous_subtype_val) (fun u ↦ fact_unstable_core_in_leaf x u.val.property)
      refine ⟨ρ, hρ, hργ, ⟨ls, ?_, hlsval⟩, ⟨lu, ?_, hluval⟩⟩
      · have hemb : Topology.IsEmbedding ls := Topology.IsEmbedding.of_comp hls
          (S.leaf x).inclusion_smooth.continuous (by
            have heq : (S.leaf x).inclusion ∘ ls = fun s : AS ↦ s.val.val := funext hlsval
            rw [heq]
            exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
        refine ⟨hemb, ?_⟩
        have hrange : range ls = (S.leaf x).inclusion ⁻¹'
            (Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x ∩ Metric.ball x ρ) := by
          ext z
          constructor
          · rintro ⟨s, rfl⟩
            rw [mem_preimage, hlsval]
            exact ⟨s.val.property, s.property⟩
          · intro hz
            refine ⟨⟨⟨(S.leaf x).inclusion z, hz.1⟩, hz.2⟩, ?_⟩
            apply (S.leaf x).inclusion_injective
            exact hlsval _
        rw [hrange]
        exact fact_core_collar_open f S hs x ρ hργ (fun y hy n ↦
          hcontractS x (mem_univ _) y ⟨mem_univ _, hy⟩ x
            ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n)
      · have hemb : Topology.IsEmbedding lu := Topology.IsEmbedding.of_comp hlu
          (U.leaf x).inclusion_smooth.continuous (by
            have heq : (U.leaf x).inclusion ∘ lu = fun u : AU ↦ u.val.val := funext hluval
            rw [heq]
            exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
        refine ⟨hemb, ?_⟩
        have hrange : range lu = (U.leaf x).inclusion ⁻¹'
            (Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x ∩ Metric.ball x ρ) := by
          ext z
          constructor
          · rintro ⟨u, rfl⟩
            rw [mem_preimage, hluval]
            exact ⟨u.val.property, u.property⟩
          · intro hz
            refine ⟨⟨⟨(U.leaf x).inclusion z, hz.1⟩, hz.2⟩, ?_⟩
            apply (U.leaf x).inclusion_injective
            exact hluval _
        rw [hrange]
        exact fact_core_collar_open f.symm U hu x ρ hργ (fun y hy n ↦
          hcontractU x (mem_univ _) y ⟨mem_univ _, hy⟩ x
            ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n)
    obtain ⟨βembed, hβembed, hembedmod⟩ :=
      Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_modulus
        d hdtop (γFact / 3) (div_pos hγFact (by norm_num))
    have orbit_embedded
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hfactors : ∀ x : M, ∃ ρ : ℝ, 0 < ρ ∧
          ∃ l : {s : {y : M | ∀ n : ℕ, dF.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤ γFact} //
            dF.dist s.val x < ρ} → (R.leaf x).Carrier,
          Topology.IsOpenEmbedding l ∧ ∀ s, (R.leaf x).inclusion (l s) = s.val.val)
        (β : ℝ) (hβ : β ≤ βembed)
        (hcontains : ∀ x, adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ⊆ range (R.leaf x).inclusion)
        (x : M) : Topology.IsEmbedding
          (fun y : (R.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ↦
            (R.leaf x).inclusion y.val) := by
      let P := adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x
      let lift : P → (R.leaf x).Carrier := fun y ↦ (hcontains x y.property).choose
      have hlift (y : P) : (R.leaf x).inclusion (lift y) = y.val :=
        (hcontains x y.property).choose_spec
      have hcontinuous : Continuous lift := by
        rw [continuous_iff_continuousAt]
        intro y
        obtain ⟨ρ, hρ, l, hl, hlval⟩ := hfactors y.val
        let A := {s : {z : M | ∀ n : ℕ,
          dF.dist ((g : M → M)^[n] z) ((g : M → M)^[n] y.val) ≤ γFact} // dF.dist s.val y.val < ρ}
        let V : Set P := {z | dF.dist z.val y.val < ρ}
        have hV : IsOpen V := isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
        have hyV : y ∈ V := by simpa [V] using hρ
        have hcore (z : P) : ∀ n : ℕ,
            dF.dist ((g : M → M)^[n] z.val) ((g : M → M)^[n] y.val) ≤ γFact := by
          intro n
          have hz := hembedmod _ _ ((z.property n).trans_le hβ)
          have hy := hembedmod _ _ ((y.property n).trans_le hβ)
          have ht := dist_triangle ((g : M → M)^[n] z.val)
            ((g : M → M)^[n] x) ((g : M → M)^[n] y.val)
          rw [dist_comm ((g : M → M)^[n] x)] at ht
          linarith
        let into : V → A := fun z ↦ ⟨⟨z.val.val, hcore z.val⟩, z.property⟩
        have hinto : Continuous into :=
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
        let rebase := R.rebase x (lift y)
        have hybase : (R.leaf x).inclusion (lift y) = y.val := hlift y
        have hrebase : ∃ e : Diffeomorph 𝓘(ℝ, Fin (R.leaf x).rank → ℝ)
            𝓘(ℝ, Fin (R.leaf y.val).rank → ℝ) (R.leaf x).Carrier (R.leaf y.val).Carrier ∞,
            ∀ z, (R.leaf y.val).inclusion (e z) = (R.leaf x).inclusion z := by
          rw [← hybase]
          exact ⟨R.rebase x (lift y), R.inclusion_rebase x (lift y)⟩
        obtain ⟨e, he⟩ := hrebase
        have heq (z : V) : lift z.val = e.symm (l (into z)) := by
          apply (R.leaf x).inclusion_injective
          rw [hlift, ← he, e.apply_symm_apply, hlval]
        have hc : Continuous (fun z : V ↦ lift z.val) :=
          (e.symm.continuous.comp (hl.continuous.comp hinto)).congr (fun z ↦ (heq z).symm)
        exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt (hV.mem_nhds hyV)
      let Q := (R.leaf x).inclusion ⁻¹' P
      let H : Q ≃ₜ P :=
        { toFun := fun y ↦ ⟨(R.leaf x).inclusion y.val, y.property⟩
          invFun := fun y ↦ ⟨lift y, by change (R.leaf x).inclusion (lift y) ∈ P; rw [hlift]; exact y.property⟩
          left_inv := fun y ↦ by
            apply Subtype.ext
            apply (R.leaf x).inclusion_injective
            exact hlift _
          right_inv := fun y ↦ Subtype.ext (hlift y)
          continuous_toFun := ((R.leaf x).inclusion_smooth.continuous.comp continuous_subtype_val).subtype_mk (fun y : Q ↦ y.property)
          continuous_invFun := hcontinuous.subtype_mk (fun y : P ↦ by
            change (R.leaf x).inclusion (lift y) ∈ P
            rw [hlift]
            exact y.property) }
      exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
    have stable_orbit_embedded (β : ℝ) (hβ : β ≤ min βembed βcapture) (x : M) : Topology.IsEmbedding
        (fun y : (S.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque 𝓘(ℝ, E) f d β x ↦ (S.leaf x).inclusion y.val) := by
      apply orbit_embedded f S (fun x ↦ ?_) β (hβ.trans (min_le_left _ _)) (fun x y hy ↦
        stable_plaque_in_leaf x (fun n ↦ (hy n).trans_le (hβ.trans (min_le_right _ _)))) x
      obtain ⟨ρ, hρ, hργ, ⟨l, hl, hv⟩, _⟩ := fact_native_factors x
      exact ⟨ρ, hρ, l, hl, hv⟩
    have unstable_orbit_embedded (β : ℝ) (hβ : β ≤ min βembed βcapture) (x : M) : Topology.IsEmbedding
        (fun y : (U.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm d β x ↦ (U.leaf x).inclusion y.val) := by
      apply orbit_embedded f.symm U (fun x ↦ ?_) β (hβ.trans (min_le_left _ _)) (fun x y hy ↦
        unstable_plaque_in_leaf x (fun n ↦ (hy n).trans_le (hβ.trans (min_le_right _ _)))) x
      obtain ⟨ρ, hρ, hργ, _, ⟨l, hl, hv⟩⟩ := fact_native_factors x
      exact ⟨ρ, hρ, l, hl, hv⟩
    have factor_homeomorph
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)} {x : M}
        (L : NativeSmoothLeaf 𝓘(ℝ, E) D x) (K : Set M) (ρ δ : ℝ) (hδρ : δ ≤ ρ)
        (l : {s : K // dF.dist s.val x < ρ} → L.Carrier)
        (hl : Continuous l) (hval : ∀ s, L.inclusion (l s) = s.val.val) :
        ∃ H : (L.inclusion ⁻¹' (K ∩ Metric.ball x δ)) ≃ₜ {s : K // dF.dist s.val x < δ},
          ∀ z, (H z).val.val = L.inclusion z.val := by
      let into : {s : K // dF.dist s.val x < δ} → {s : K // dF.dist s.val x < ρ} :=
        fun s ↦ ⟨s.val, s.property.trans_le hδρ⟩
      have hinto : Continuous into := continuous_subtype_val.subtype_mk _
      let forward : (L.inclusion ⁻¹' (K ∩ Metric.ball x δ)) → {s : K // dF.dist s.val x < δ} :=
        fun z ↦ ⟨⟨L.inclusion z.val, z.property.1⟩, z.property.2⟩
      let backward : {s : K // dF.dist s.val x < δ} → (L.inclusion ⁻¹' (K ∩ Metric.ball x δ)) :=
        fun s ↦ ⟨l (into s), by rw [mem_preimage, hval]; exact ⟨s.val.property, s.property⟩⟩
      let H : (L.inclusion ⁻¹' (K ∩ Metric.ball x δ)) ≃ₜ {s : K // dF.dist s.val x < δ} :=
        { toFun := forward
          invFun := backward
          left_inv := fun z ↦ by
            apply Subtype.ext
            apply L.inclusion_injective
            exact hval _
          right_inv := fun s ↦ by
            apply Subtype.ext
            apply Subtype.ext
            exact hval _
          continuous_toFun := ((L.inclusion_smooth.continuous.comp continuous_subtype_val).subtype_mk
            (fun z ↦ z.property.1)).subtype_mk (fun z ↦ z.property.2)
          continuous_invFun := (hl.comp hinto).subtype_mk (fun s ↦ by
            change L.inclusion (l (into s)) ∈ K ∩ Metric.ball x δ
            rw [hval]; exact ⟨s.val.property, s.property⟩) }
      exact ⟨H, fun z ↦ rfl⟩
    have hexp (x y : M)
        (hxy : ∀ j : ℤ, d.dist ((f.toHomeomorph ^ j) x)
          ((f.toHomeomorph ^ j) y) ≤ βcapture / 2) : x = y := by
      have hmem : x ∈ hyperbolicClosedStablePlaque f univ dFact γFact y ∩
          hyperbolicClosedUnstablePlaque f univ dFact γFact y := by
        constructor
        · refine ⟨mem_univ _, fun n ↦ ?_⟩
          apply le_of_lt (hcapture _ _ ?_)
          have hn := (hxy (n : ℤ)).trans_lt (half_lt_self hβcapture)
          simpa only [zpow_natCast,
            Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe, Diffeomorph.coe_toHomeomorph] using hn
        · refine ⟨mem_univ _, fun n ↦ ?_⟩
          apply le_of_lt (hcapture _ _ ?_)
          have hn := (hxy (-(n : ℤ))).trans_lt (half_lt_self hβcapture)
          simpa only [Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_neg_coe, Diffeomorph.coe_toHomeomorph_symm] using hn
      rw [hBmem ⟨(y, y), by simpa using hεFact.le⟩, mem_singleton_iff, hBdiag] at hmem
      exact hmem
    have bracket_at_radius (γ : ℝ) (hγ : 0 < γ) (hsmall : 2 * γ ≤ βcapture / 2) :
        ∃ ε : ℝ, 0 < ε ∧ ∃ bracket : adaptedClosePairDomain (M := M) d ε → M,
          Continuous bracket ∧ ∀ p : adaptedClosePairDomain (M := M) d ε,
            adaptedClosedOrbitCore 𝓘(ℝ, E) f d γ p.val.1 ∩
              adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm d γ p.val.2 = {bracket p} := by
      obtain ⟨ε, hε, C, hC, hCm, hCu⟩ :=
        Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_contracting_bracket
          f.toHomeomorph hεFact hκ.le hκ1.le B hB hBdiag hBS hBU d hdtop hγ hsmall hexp
      let bracket : adaptedClosePairDomain (M := M) d ε → M := fun p ↦ C ⟨p.val, p.property.le⟩
      refine ⟨ε, hε, bracket, hC.comp (continuous_subtype_val.subtype_mk _), ?_⟩
      intro p
      ext z
      constructor
      · intro hz
        exact hCu ⟨p.val, p.property.le⟩ z
          (fun n ↦ by simpa only [zpow_natCast,
            Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe, Diffeomorph.coe_toHomeomorph] using hz.1 n)
          (fun n ↦ by simpa only [
            Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_neg_coe, Diffeomorph.coe_toHomeomorph_symm] using hz.2 n)
      · intro hz
        rcases hz with rfl
        have hm := hCm ⟨p.val, p.property.le⟩
        constructor
        · intro n
          simpa only [zpow_natCast,
            Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_pow_coe, Diffeomorph.coe_toHomeomorph, bracket] using hm.1 n
        · intro n
          simpa only [Dynamics.ManningOriginalBasicSetSignedTraceG7.CarrierAdapter.homeomorph_zpow_neg_coe, Diffeomorph.coe_toHomeomorph_symm, bracket] using hm.2 n
    have native_product_of_bracket (γ ε : ℝ) (hγ : 0 < γ) (hγcap : γ < βcapture) (hε : 0 < ε)
        (bracket : adaptedClosePairDomain (M := M) d ε → M)
        (hsingle : ∀ p, adaptedClosedOrbitCore 𝓘(ℝ, E) f d γ p.val.1 ∩
          adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm d γ p.val.2 = {bracket p})
        (x : M) : Nonempty (AdaptedNativeProduct 𝓘(ℝ, E) f
          splitting.stable.toDistribution splitting.unstable.toDistribution d γ ε S U bracket x) := by
      obtain ⟨ρp, hρp, hρpγ, hρpε, hcharts⟩ := prodFact.product_chart x
      obtain ⟨ρn, hρn, hρnγ, ⟨ls, hls, hlsval⟩, ⟨lu, hlu, hluval⟩⟩ := fact_native_factors x
      obtain ⟨ηγ, hηγ, hmodγ⟩ :=
        @Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_modulus
          M (d.replaceTopology hdtop.symm) inferInstance dF rfl γ hγ
      obtain ⟨ηε, hηε, hmodε⟩ :=
        @Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_modulus
          M (d.replaceTopology hdtop.symm) inferInstance dF rfl (ε / 2) (half_pos hε)
      let δ := min (min ρp ρn) (min ηγ ηε) / 2
      have hδ : 0 < δ := half_pos (lt_min (lt_min hρp hρn) (lt_min hηγ hηε))
      have hδp : δ ≤ ρp := (half_le_self (le_of_lt (lt_min (lt_min hρp hρn) (lt_min hηγ hηε)))).trans
        ((min_le_left _ _).trans (min_le_left _ _))
      have hδn : δ ≤ ρn := (half_le_self (le_of_lt (lt_min (lt_min hρp hρn) (lt_min hηγ hηε)))).trans
        ((min_le_left _ _).trans (min_le_right _ _))
      have hδγ : δ ≤ ηγ := (half_le_self (le_of_lt (lt_min (lt_min hρp hρn) (lt_min hηγ hηε)))).trans
        ((min_le_right _ _).trans (min_le_left _ _))
      have hδε : δ ≤ ηε := (half_le_self (le_of_lt (lt_min (lt_min hρp hρn) (lt_min hηγ hηε)))).trans
        ((min_le_right _ _).trans (min_le_right _ _))
      let KS := Dynamics.relativeClosedStablePlaque f.toHomeomorph γFact x
      let KU := Dynamics.relativeClosedUnstablePlaque f.toHomeomorph γFact x
      let V : Set M := KS ∩ Metric.ball x δ
      let W : Set M := KU ∩ Metric.ball x δ
      have hselfS : x ∈ KS := fun n ↦ by simpa using hγFact.le
      have hselfU : x ∈ KU := fun n ↦ by simpa using hγFact.le
      have hV : V ⊆ Dynamics.relativeClosedStablePlaque f.toHomeomorph ρp x := by
        intro y hy n
        exact (prodFact.stable_contraction x y x hy.1 hselfS n).trans
          ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dF.dist y x) (pow_le_one₀ hκ.le hκ1.le)).trans
            (hy.2.le.trans hδp))
      have hW : W ⊆ Dynamics.relativeClosedUnstablePlaque f.toHomeomorph ρp x := by
        intro y hy n
        exact (prodFact.unstable_contraction x y x hy.1 hselfU n).trans
          ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dF.dist y x) (pow_le_one₀ hκ.le hκ1.le)).trans
            (hy.2.le.trans hδp))
      have hVopen : IsOpen {s : KS | s.val ∈ V} := by
        have heq : {s : KS | s.val ∈ V} = Subtype.val ⁻¹' Metric.ball x δ := by ext s; simp [V]
        rw [heq]
        exact Metric.isOpen_ball.preimage continuous_subtype_val
      have hWopen : IsOpen {u : KU | u.val ∈ W} := by
        have heq : {u : KU | u.val ∈ W} = Subtype.val ⁻¹' Metric.ball x δ := by ext u; simp [W]
        rw [heq]
        exact Metric.isOpen_ball.preimage continuous_subtype_val
      obtain ⟨himage, chart, hchart⟩ := hcharts W V hW hV hWopen hVopen
      have hVS : IsOpen ((S.leaf x).inclusion ⁻¹' V) :=
        fact_core_collar_open f S hs x δ (hδp.trans hρpγ) (fun y hy n ↦
          hcontractS x (mem_univ _) y ⟨mem_univ _, hy⟩ x
            ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n)
      have hWU : IsOpen ((U.leaf x).inclusion ⁻¹' W) :=
        fact_core_collar_open f.symm U hu x δ (hδp.trans hρpγ) (fun y hy n ↦
          hcontractU x (mem_univ _) y ⟨mem_univ _, hy⟩ x
            ⟨mem_univ _, fun k ↦ by simpa using hγFact.le⟩ n)
      obtain ⟨HS, hHS⟩ := factor_homeomorph (S.leaf x) KS ρn δ hδn ls hls.continuous hlsval
      obtain ⟨HU, hHU⟩ := factor_homeomorph (U.leaf x) KU ρn δ hδn lu hlu.continuous hluval
      have hVset : (fun s : KS ↦ s.val ∈ V) = (fun s ↦ dF.dist s.val x < δ) := by
        funext s; exact propext (by simp [V, Metric.mem_ball])
      have hWset : (fun u : KU ↦ u.val ∈ W) = (fun u ↦ dF.dist u.val x < δ) := by
        funext u; exact propext (by simp [W, Metric.mem_ball])
      let HSp : ((S.leaf x).inclusion ⁻¹' V) ≃ₜ {s : KS // s.val ∈ V} :=
        HS.trans (Homeomorph.setCongr (congrArg Set.ofPred hVset).symm)
      let HUp : ((U.leaf x).inclusion ⁻¹' W) ≃ₜ {u : KU // u.val ∈ W} :=
        HU.trans (Homeomorph.setCongr (congrArg Set.ofPred hWset).symm)
      have hHSp (s) : (HSp s).val.val = (S.leaf x).inclusion s.val := hHS s
      have hHUp (u) : (HUp u).val.val = (U.leaf x).inclusion u.val := hHU u
      have hcaller (s : (S.leaf x).inclusion ⁻¹' V) (u : (U.leaf x).inclusion ⁻¹' W) :
          d.dist ((U.leaf x).inclusion u.val) ((S.leaf x).inclusion s.val) < ε := by
        have hu := hmodε _ _ (u.property.2.trans_le hδε)
        have hs := hmodε _ _ (s.property.2.trans_le hδε)
        have ht := @dist_triangle M d.toPseudoMetricSpace ((U.leaf x).inclusion u.val) x ((S.leaf x).inclusion s.val)
        rw [@dist_comm M d.toPseudoMetricSpace x] at ht
        linarith
      let product := ((HSp.prodCongr HUp).trans (Homeomorph.prodComm _ _)).trans chart
      refine ⟨{ stableDomain := (S.leaf x).inclusion ⁻¹' V
                unstableDomain := (U.leaf x).inclusion ⁻¹' W
                stable_open := hVS
                unstable_open := hWU
                stable_center := by rw [mem_preimage, (S.leaf x).inclusion_point]; exact ⟨hselfS, Metric.mem_ball_self hδ⟩
                unstable_center := by rw [mem_preimage, (U.leaf x).inclusion_point]; exact ⟨hselfU, Metric.mem_ball_self hδ⟩
                stable_core := ?_
                unstable_core := ?_
                caller := hcaller
                neighborhood := image2 prodFact.bracket W V
                neighborhood_open := himage
                neighborhood_center := ?_
                product := product
                product_eq := ?_ }⟩
      · intro s hs n
        apply le_of_lt (hmodγ _ _ ?_)
        exact (prodFact.stable_contraction x _ x hs.1 hselfS n).trans_lt
          ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dF.dist ((S.leaf x).inclusion s) x)
            (pow_le_one₀ hκ.le hκ1.le)).trans_lt (hs.2.trans_le hδγ))
      · intro u hu n
        apply le_of_lt (hmodγ _ _ ?_)
        exact (prodFact.unstable_contraction x _ x hu.1 hselfU n).trans_lt
          ((mul_le_of_le_one_left (dist_nonneg : 0 ≤ dF.dist ((U.leaf x).inclusion u) x)
            (pow_le_one₀ hκ.le hκ1.le)).trans_lt (hu.2.trans_le hδγ))
      · refine ⟨x, ⟨hselfU, Metric.mem_ball_self hδ⟩, x, ⟨hselfS, Metric.mem_ball_self hδ⟩, ?_⟩
        exact (prodFact.bracket_unique x x x (by simpa using prodFact.closeRadius_pos.le) ⟨hselfS,hselfU⟩).symm
      · intro s u
        have hprod : (product (s,u)).val = prodFact.bracket ((U.leaf x).inclusion u.val) ((S.leaf x).inclusion s.val) := by
          change (chart (HUp u, HSp s)).val = _
          simpa only [hHSp, hHUp] using hchart (HUp u, HSp s)
        rw [hprod]
        apply Eq.symm
        have hm : bracket ⟨((U.leaf x).inclusion u.val, (S.leaf x).inclusion s.val), hcaller s u⟩ ∈
            adaptedClosedOrbitCore 𝓘(ℝ, E) f d γ ((U.leaf x).inclusion u.val) ∩
            adaptedClosedOrbitCore 𝓘(ℝ, E) f.symm d γ ((S.leaf x).inclusion s.val) := by
          have hh := hsingle ⟨((U.leaf x).inclusion u.val, (S.leaf x).inclusion s.val), hcaller s u⟩
          exact hh.symm ▸ mem_singleton _
        apply prodFact.bracket_unique
        · have ht := dist_triangle ((U.leaf x).inclusion u.val) x ((S.leaf x).inclusion s.val)
          rw [dist_comm x] at ht
          have hu := u.property.2.le.trans hδp
          have hs := s.property.2.le.trans hδp
          linarith
        · exact ⟨fun n ↦ (hcapture _ _ ((hm.1 n).trans_lt hγcap)).le,
            fun n ↦ (hcapture _ _ ((hm.2 n).trans_lt hγcap)).le⟩
    have cores_of_nonexpansion
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        (β γ : ℝ) (hγβ : γ < β)
        (hc : ∀ x y, y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x →
          d.dist (g y) (g x) ≤ d.dist y x) :
        (∀ x, adaptedClosedOrbitCore 𝓘(ℝ, E) g d γ x =
          adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ∩ adaptedMetricClosedBall d x γ) ∧
        (∀ x, adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d γ x =
          adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ∩ adaptedMetricBall d x γ) := by
      have hbound (x y : M) (hy : y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x)
          (n : ℕ) : d.dist ((g : M → M)^[n] y) ((g : M → M)^[n] x) ≤ d.dist y x := by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          apply (hc _ _ ?_).trans ih
          intro k
          simpa only [← Function.iterate_add_apply] using hy (k+n)
      constructor
      · intro x
        ext y
        constructor
        · intro hy
          exact ⟨fun n ↦ (hy n).trans_lt hγβ, hy 0⟩
        · rintro ⟨hy,hball⟩ n
          exact (hbound x y hy n).trans hball
      · intro x
        ext y
        constructor
        · intro hy
          exact ⟨fun n ↦ (hy n).trans hγβ, hy 0⟩
        · rintro ⟨hy,hball⟩ n
          exact (hbound x y hy n).trans_lt hball
    have assemble_orbit_plaques
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
        (hcontains : ∀ x, adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ⊆ range (R.leaf x).inclusion)
        (hemb : ∀ x, Topology.IsEmbedding
          (fun y : (R.leaf x).inclusion ⁻¹' adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ↦
            (R.leaf x).inclusion y.val))
        (hclosed : ∀ x, adaptedClosedOrbitCore 𝓘(ℝ, E) g d γ x =
          adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ∩ adaptedMetricClosedBall d x γ)
        (hstrict : ∀ x, adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d γ x =
          adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x ∩ adaptedMetricBall d x γ)
        (hfamily : ∀ x, ∃ r : ℕ,
          ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) D x,
            ∀ p : F.centerDomain,
              adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β p.val ⊆ (F.plaque p).image ∧
              ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E) (W := Fin (R.leaf p.val).rank → ℝ)
                (L := (R.leaf p.val).Carrier) D p.val (F.plaque p), T.inclusion = (R.leaf p.val).inclusion) :
        Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) g D d β γ R) := by
      have hcenter (r : ℝ) (hr : 0 < r) (x : M) : x ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d r x :=
        fun n ↦ by simpa only [d.dist_self] using hr
      refine ⟨{ plaque_in_leaf := hcontains
                plaque_intrinsic_open := intrinsic_orbit_open g R hstep β hβ
                plaque_contains_center := hcenter β hβ
                plaque_embedded := hemb
                plaque_native_chart := ?_
                closed_core := hclosed
                strict_core := hstrict
                strict_core_intrinsic_open := intrinsic_orbit_open g R hstep γ hγ
                strict_core_contains_center := hcenter γ hγ
                local_C1_family := hfamily }⟩
      intro x
      obtain ⟨r, F, hF⟩ := hfamily x
      obtain ⟨hsub, T, hT⟩ := hF ⟨x,F.center_mem⟩
      obtain ⟨P, hP, T', hT'⟩ := restrict_native_chart (R.leaf x) (F.plaque ⟨x,F.center_mem⟩) T hT
        (adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x) (hcenter β hβ x) hsub (intrinsic_orbit_open g R hstep β hβ x)
      exact ⟨r,P,hP,T',hT'⟩
    have hcontMetric : IsContinuousRiemannianBundle E
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) := by
      change letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
        ⟨h.toContinuousRiemannianMetric.toRiemannianMetric⟩
        IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
      infer_instance
    have metric_on_leaf {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        {x : M} (L : NativeSmoothLeaf 𝓘(ℝ, E) D x) (y z : L.Carrier) :
        ENNReal.ofReal (d.dist (L.inclusion y) (L.inclusion z)) =
          Manifold.riemannianEDist 𝓘(ℝ, E) (L.inclusion y) (L.inclusion z) := by
      rw [riemannianEDist_eq_piecewiseSmoothRiemannianEDist h]
      exact hdcomp _ _ ((isPreconnected_range L.inclusion_smooth.continuous).subset_connectedComponent
        (mem_range_self y) (mem_range_self z))
    have local_family_capture
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hstep : ∀ x (v : TangentSpace 𝓘(ℝ, E) x), v ∈ D x →
          hyperbolicRiemannianNorm h (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
            θ * hyperbolicRiemannianNorm h v)
        (H : Dynamics.Bowen.CompactLocalProductData g.toHomeomorph γFact κ)
        (hlocal : ∀ x, ∃ ρ : ℝ, 0 < ρ ∧
          LocallyConnectedSpace {s : Dynamics.relativeClosedStablePlaque g.toHomeomorph γFact x // dF.dist s.val x < ρ})
        (hcore : ∀ x, Dynamics.relativeClosedStablePlaque g.toHomeomorph γFact x ⊆ range (R.leaf x).inclusion)
        (hlift : ∀ {X : Type v} [TopologicalSpace X] [LocallyConnectedSpace X]
          (x : M) (a : X → M), Continuous a → (∀ t, a t ∈ range (R.leaf x).inclusion) →
          ∃ l : X → (R.leaf x).Carrier, Continuous l ∧ ∀ t, (R.leaf x).inclusion (l t) = a t)
        (hfamily : ∀ x, ∃ r : ℕ, ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) D x,
          ∀ p : F.centerDomain, ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E)
            (W := Fin (R.leaf p.val).rank → ℝ) (L := (R.leaf p.val).Carrier) D p.val (F.plaque p),
              T.inclusion = (R.leaf p.val).inclusion)
        (x : M) : ∃ β : ℝ, 0 < β ∧ ∃ r : ℕ,
          ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) D x,
            ∀ p : F.centerDomain,
              (∀ y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β p.val, d.dist (g y) (g p.val) ≤ d.dist y p.val) ∧
              adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β p.val ⊆ (F.plaque p).image ∧
              ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E)
                (W := Fin (R.leaf p.val).rank → ℝ) (L := (R.leaf p.val).Carrier) D p.val (F.plaque p),
                  T.inclusion = (R.leaf p.val).inclusion := by
      obtain ⟨r, Φ, hΦ⟩ := hfamily x
      have hnorm (z : M) (v : TangentSpace 𝓘(ℝ, E) z) : hyperbolicRiemannianNorm h v = ‖v‖ := by
        rw [norm_eq_sqrt_real_inner]
        rfl
      obtain ⟨N₁, hN₁, hxN₁, a, ha, haR, hcontract⟩ :=
        Φ.local_riemannian_contraction g hθpos hθlt (fun z v hv ↦ by
          simpa only [hnorm] using hstep z v hv)
      obtain ⟨N₂, hN₂, hxN₂, η, hη, hboundary⟩ :=
        Φ.uniform_inner_sphere_separation (half_pos ha) ((half_lt_self ha).trans haR)
      obtain ⟨O, hO, hxO, δ, hδ, hslices⟩ := H.local_stable_connected_slice x η hη (hlocal x)
      obtain ⟨ζ, hζ, hζO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hxO)
      let N : Set Φ.centerDomain := N₁ ∩ N₂ ∩ {p | dF.dist p.val x < ζ / 2}
      have hN : IsOpen N := (hN₁.inter hN₂).inter
        (isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const)
      have hxN : (⟨x, Φ.center_mem⟩ : Φ.centerDomain) ∈ N :=
        ⟨⟨hxN₁,hxN₂⟩, by simpa using half_pos hζ⟩
      let V := Subtype.val '' N
      have hV : IsOpen V := Φ.centerDomain_open.isOpenMap_subtype_val _ hN
      have hxV : x ∈ V := ⟨⟨x, Φ.center_mem⟩,hxN,rfl⟩
      have hVsub : V ⊆ Φ.centerDomain := by rintro _ ⟨p,hp,rfl⟩; exact p.property
      let F := Φ.restrictCenters V hV hxV hVsub
      obtain ⟨β, hβ, hmod⟩ :=
        Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_modulus
          d hdtop (min δ (ζ / 2)) (lt_min hδ (half_pos hζ))
      refine ⟨β,hβ,r,F,?_⟩
      intro p
      let p' : Φ.centerDomain := ⟨p.val, hVsub p.property⟩
      have hpN : p' ∈ N := by
        obtain ⟨q,hq,heq⟩ := p.property
        have hqq : q = p' := Subtype.ext heq
        rwa [← hqq]
      have hpO : p.val ∈ O := hζO (hpN.2.trans (half_lt_self hζ))
      obtain ⟨T,hT⟩ := hΦ p'
      have hcapture (y : M) (hy : y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β p.val) :
          y ∈ (Φ.plaque p').param '' Metric.ball (0 : Fin r → ℝ) (a / 2) := by
        have hys : y ∈ Dynamics.relativeClosedStablePlaque g.toHomeomorph δ p.val := by
          intro n
          exact ((hmod _ _ (hy n)).trans_le (min_le_left _ _)).le
        have hy0 : dF.dist y p.val < ζ / 2 := by
          have hh := (hmod _ _ (hy 0)).trans_le (min_le_right _ _)
          simpa only [Function.iterate_zero_apply] using hh
        have hyO : y ∈ O := by
          apply hζO
          change dF.dist y x < ζ
          have ht := dist_triangle y p.val x
          have hpdist : dF.dist p.val x < ζ / 2 := hpN.2
          linarith
        obtain ⟨X,tX,lX,cX,q,hq,hpq,hyq,hqr⟩ := hslices p.val hpO y hyO hys
        let : TopologicalSpace X := tX
        let : LocallyConnectedSpace X := lX
        let : ConnectedSpace X := cX
        obtain ⟨l,hl,hlval⟩ := hlift p.val q hq (fun z ↦ hcore p.val (hqr z).1)
        obtain ⟨z₀,hz₀⟩ := hpq
        have hcap := T.connected_map_captured (half_pos ha)
          (by rw [Φ.domain_eq]; exact Metric.closedBall_subset_ball ((half_lt_self ha).trans haR))
          (hboundary p' hpN.1.2) l hl z₀
          (by rw [hT,hlval]; exact hz₀)
          (fun z ↦ by rw [hT,hlval]; exact (hqr z).2)
        obtain ⟨z,hz⟩ := hyq
        have hh := hcap z
        rwa [hT,hlval,hz] at hh
      refine ⟨?_, ?_, T,hT⟩
      · intro y hy
        obtain ⟨v,hv,hvy⟩ := hcapture y hy
        have hvR : v ∈ (Φ.plaque p').domain := by
          rw [Φ.domain_eq]
          exact (Metric.ball_subset_ball ((half_lt_self ha).trans haR).le) hv
        have hyLeaf : (R.leaf p.val).inclusion (T.toLeaf v) = y := by
          rw [← hT,T.inclusion_toLeaf v hvR]
          exact hvy
        have hh := hcontract p' hpN.1.1 v ((Metric.ball_subset_ball (half_lt_self ha).le) hv)
        rw [hvy] at hh
        apply ENNReal.ofReal_le_ofReal_iff (@dist_nonneg M d.toPseudoMetricSpace y p.val) |>.mp
        have heq0 := metric_on_leaf (R.leaf p.val) (T.toLeaf v) (R.leaf p.val).point
        rw [hyLeaf,(R.leaf p.val).inclusion_point] at heq0
        have heq1 := metric_on_leaf (R.leaf (g p.val)) (R.advance p.val (T.toLeaf v))
          (R.advance p.val (R.leaf p.val).point)
        rw [R.inclusion_advance,R.inclusion_advance,hyLeaf,(R.leaf p.val).inclusion_point] at heq1
        rw [heq0,heq1]
        exact hh
      · intro y hy
        obtain ⟨v,hv,hvy⟩ := hcapture y hy
        exact ⟨v, by change v ∈ (Φ.plaque p').domain; rw [Φ.domain_eq]; exact (Metric.ball_subset_ball ((half_lt_self ha).trans haR).le) hv, hvy⟩
    have global_family_capture
        (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
        {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
        (R : NativeInvariantLeafSystem 𝓘(ℝ, E) D g)
        (hlocal : ∀ x : M, ∃ β : ℝ, 0 < β ∧ ∃ r : ℕ,
          ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) D x,
            ∀ p : F.centerDomain,
              (∀ y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β p.val, d.dist (g y) (g p.val) ≤ d.dist y p.val) ∧
              adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β p.val ⊆ (F.plaque p).image ∧
              ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E)
                (W := Fin (R.leaf p.val).rank → ℝ) (L := (R.leaf p.val).Carrier) D p.val (F.plaque p),
                  T.inclusion = (R.leaf p.val).inclusion) :
        ∃ β : ℝ, 0 < β ∧
          (∀ x y, y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β x → d.dist (g y) (g x) ≤ d.dist y x) ∧
          (∀ x, ∃ r : ℕ, ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) D x,
            ∀ p : F.centerDomain,
              adaptedOpenOrbitPlaque 𝓘(ℝ, E) g d β p.val ⊆ (F.plaque p).image ∧
              ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E)
                (W := Fin (R.leaf p.val).rank → ℝ) (L := (R.leaf p.val).Carrier) D p.val (F.plaque p),
                  T.inclusion = (R.leaf p.val).inclusion) := by
      choose β hβ r F hF using hlocal
      obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (F x).centerDomain)
        (fun x ↦ (F x).centerDomain_open) (fun x _ ↦ mem_iUnion.mpr ⟨x,(F x).center_mem⟩)
      have hmin (t : Finset M) : ∃ b : ℝ, 0 < b ∧ ∀ x ∈ t, b ≤ β x := by
        induction t using Finset.induction_on with
        | empty => exact ⟨1,by norm_num,by simp⟩
        | @insert x t hxt ih =>
          obtain ⟨b,hb,ht⟩ := ih
          refine ⟨min b (β x), lt_min hb (hβ x), ?_⟩
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact min_le_right _ _
          · exact (min_le_left _ _).trans (ht y hy)
      obtain ⟨b,hb,hbt⟩ := hmin t
      have hcover (x : M) : ∃ y ∈ t, x ∈ (F y).centerDomain := by
        exact mem_iUnion.mp (ht (mem_univ x)) |>.imp fun y hy ↦ by
          obtain ⟨hy,hx⟩ := mem_iUnion.mp hy
          exact ⟨hy,hx⟩
      refine ⟨b,hb,?_,?_⟩
      · intro x y hy
        obtain ⟨z,hzt,hxz⟩ := hcover x
        exact (hF z ⟨x,hxz⟩).1 y (fun n ↦ (hy n).trans_le (hbt z hzt))
      · intro x
        obtain ⟨z,hzt,hxz⟩ := hcover x
        refine ⟨r z,(F z).recenter x hxz,?_⟩
        intro p
        obtain ⟨_,hcap,T,hT⟩ := hF z p
        exact ⟨fun y hy ↦ hcap (fun n ↦ (hy n).trans_le (hbt z hzt)),T,hT⟩
    have hlocalS := local_family_capture f S hs prodFact
      (fun x ↦ by
        obtain ⟨ρ,hρ,hργ,hu,hs⟩ := fact_factors_locally_connected x
        exact ⟨ρ,hρ,hs⟩)
      (fun x ↦ fact_stable_core_in_leaf x)
      (fun {X} _ _ ↦ stable_continuous_lift)
      stable_intrinsic_families
    have hlocalU := local_family_capture f.symm U hu prodFact.reverse
      (fun x ↦ by
        obtain ⟨ρ,hρ,hργ,hu,hs⟩ := fact_factors_locally_connected x
        exact ⟨ρ,hρ,hu⟩)
      (fun x ↦ fact_unstable_core_in_leaf x)
      (fun {X} _ _ ↦ unstable_continuous_lift)
      unstable_intrinsic_families
    obtain ⟨βs,hβs,hnonS,hfamilyS⟩ := global_family_capture f S hlocalS
    obtain ⟨βu,hβu,hnonU,hfamilyU⟩ := global_family_capture f.symm U hlocalU
    suffices hgeometry : ∃ β γ : ℝ, 0 < γ ∧ γ ≤ γCore ∧ 2 * γ < β ∧
        2 * γ ≤ βcapture / 2 ∧
        Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f
          splitting.stable.toDistribution d β γ S) ∧
        Nonempty (AdaptedNativeOrbitPlaques 𝓘(ℝ, E) f.symm
          splitting.unstable.toDistribution d β γ U) by
      obtain ⟨β, γ, hγ, hγle, hβ, hγsmall, hS, hU⟩ := hgeometry
      obtain ⟨ε, hε, bracket, hb, hsingle⟩ := bracket_at_radius γ hγ hγsmall
      refine ⟨β, γ, ε, hγ, hγle, hβ, hε, hS, hU,
        fun x y z ↦ nativeLeafPathEDist_lt_top h (S.leaf x) y z,
        fun x y z ↦ nativeLeafPathEDist_lt_top h (U.leaf x) y z,
        bracket, hb, hsingle, ?_⟩
      exact native_product_of_bracket γ ε hγ (by linarith) hε bracket hsingle
    suffices hlocal : ∃ β : ℝ, 0 < β ∧ β ≤ min βembed βcapture ∧
        (∀ x y, y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) f d β x → d.dist (f y) (f x) ≤ d.dist y x) ∧
        (∀ x y, y ∈ adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm d β x → d.dist (f.symm y) (f.symm x) ≤ d.dist y x) ∧
        (∀ x, ∃ r : ℕ, ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) splitting.stable.toDistribution x,
          ∀ p : F.centerDomain,
            adaptedOpenOrbitPlaque 𝓘(ℝ, E) f d β p.val ⊆ (F.plaque p).image ∧
            ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E) (W := Fin (S.leaf p.val).rank → ℝ)
              (L := (S.leaf p.val).Carrier) splitting.stable.toDistribution p.val (F.plaque p),
              T.inclusion = (S.leaf p.val).inclusion) ∧
        (∀ x, ∃ r : ℕ, ∃ F : NativePlaqueFamily 𝓘(ℝ, E) (V := Fin r → ℝ) splitting.unstable.toDistribution x,
          ∀ p : F.centerDomain,
            adaptedOpenOrbitPlaque 𝓘(ℝ, E) f.symm d β p.val ⊆ (F.plaque p).image ∧
            ∃ T : NativePlaqueIntrinsicChart 𝓘(ℝ, E) (W := Fin (U.leaf p.val).rank → ℝ)
              (L := (U.leaf p.val).Carrier) splitting.unstable.toDistribution p.val (F.plaque p),
              T.inclusion = (U.leaf p.val).inclusion) by
      obtain ⟨β, hβ, hβsmall, hnonexpS, hnonexpU, hfamilyS, hfamilyU⟩ := hlocal
      let γ := min (min γCore (β / 4)) (βcapture / 8)
      have hγ : 0 < γ := lt_min (lt_min hγCore (div_pos hβ (by norm_num))) (div_pos hβcapture (by norm_num))
      have hγcore : γ ≤ γCore := (min_le_left _ _).trans (min_le_left _ _)
      have hγβ : γ ≤ β / 4 := (min_le_left _ _).trans (min_le_right _ _)
      have hγcap : γ ≤ βcapture / 8 := min_le_right _ _
      obtain ⟨hclosedS, hstrictS⟩ := cores_of_nonexpansion f β γ (by linarith) hnonexpS
      obtain ⟨hclosedU, hstrictU⟩ := cores_of_nonexpansion f.symm β γ (by linarith) hnonexpU
      refine ⟨β, γ, hγ, hγcore, by linarith, by linarith, ?_, ?_⟩
      · exact assemble_orbit_plaques f S hs β γ hβ hγ
          (fun x y hy ↦ stable_plaque_in_leaf x (fun n ↦ (hy n).trans_le (hβsmall.trans (min_le_right _ _))))
          (stable_orbit_embedded β hβsmall) hclosedS hstrictS hfamilyS
      · exact assemble_orbit_plaques f.symm U hu β γ hβ hγ
          (fun x y hy ↦ unstable_plaque_in_leaf x (fun n ↦ (hy n).trans_le (hβsmall.trans (min_le_right _ _))))
          (unstable_orbit_embedded β hβsmall) hclosedU hstrictU hfamilyU
    let β := min (min βs βu) (min βembed βcapture)
    have hβ : 0 < β := lt_min (lt_min hβs hβu) (lt_min hβembed hβcapture)
    have hβs' : β ≤ βs := (min_le_left _ _).trans (min_le_left _ _)
    have hβu' : β ≤ βu := (min_le_left _ _).trans (min_le_right _ _)
    refine ⟨β,hβ,min_le_right _ _,?_,?_,?_,?_⟩
    · intro x y hy
      exact hnonS x y (fun n ↦ (hy n).trans_le hβs')
    · intro x y hy
      exact hnonU x y (fun n ↦ (hy n).trans_le hβu')
    · intro x
      obtain ⟨r,F,hF⟩ := hfamilyS x
      refine ⟨r,F,?_⟩
      intro p
      obtain ⟨hcap,T,hT⟩ := hF p
      exact ⟨fun y hy ↦ hcap (fun n ↦ (hy n).trans_le hβs'),T,hT⟩
    · intro x
      obtain ⟨r,F,hF⟩ := hfamilyU x
      refine ⟨r,F,?_⟩
      intro p
      obtain ⟨hcap,T,hT⟩ := hF p
      exact ⟨fun y hy ↦ hcap (fun n ↦ (hy n).trans_le hβu'),T,hT⟩


end HolomorphicAnosov
