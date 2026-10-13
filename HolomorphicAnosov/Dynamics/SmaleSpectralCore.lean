import HolomorphicAnosov.Dynamics.SmaleDenseFullOrbitOfTransitivity
import HolomorphicAnosov.Dynamics.SmaleOriginalAnosovTransitiveComponents
import HolomorphicAnosov.Dynamics.SmaleCyclicShadowing
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricExpansivity
import HolomorphicAnosov.Dynamics.SmaleCompactShadowing
import HolomorphicAnosov.Dynamics.SmaleShadowingIsolation
import HolomorphicAnosov.Dynamics.SmalePeriodicShadowingClosure
import HolomorphicAnosov.Dynamics.SmalePeriodicOrbitVisits
import HolomorphicAnosov.Dynamics.ManeDenseOrbitOfSaturation
import Mathlib.Topology.Sequences
import HolomorphicAnosov.Dynamics.SmaleNonwanderingClosed
import HolomorphicAnosov.Dynamics.SmalePeriodicClosureNonwandering
import HolomorphicAnosov.Dynamics.SmaleOrbitClusterNonwandering
import HolomorphicAnosov.Dynamics.SmaleNonwanderingNonempty
import HolomorphicAnosov.Dynamics.SmaleOrbitEventuallyNearNonwandering
import HolomorphicAnosov.Dynamics.SmaleDisjointBasins
import HolomorphicAnosov.Dynamics.SmaleFiniteBasinPartition
import HolomorphicAnosov.Dynamics.SmaleOrbitComponentCapture
import HolomorphicAnosov.Dynamics.SmaleDistanceFromClusterLimits
import HolomorphicAnosov.Dynamics.SmaleBasinFromNeighborhood
import HolomorphicAnosov.Dynamics.SmaleBasinPartitionFromNeighborhoods
import HolomorphicAnosov.Dynamics.SmaleBasinPartitionFromComponents
import HolomorphicAnosov.Dynamics.SmaleNonwanderingInverse
import HolomorphicAnosov.Dynamics.SmaleTwoSidedBasinPartition
import HolomorphicAnosov.Dynamics.SmaleCaptureOtherComponent
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaques
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Dynamics.HyperbolicBracketOpenReturn
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.UniformExponentialLift
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle

/-! Spectral components of a real Anosov diffeomorphism, their periodic points, and their two-sided
basins (Shub, Thm. 8.13; Props. 9.7–9.8). -/

namespace HolomorphicAnosov

open Set Filter
open scoped ContDiff _root_.HolomorphicAnosov.Topology _root_.Topology Bundle

universe u


/-- The nonwandering set of an Anosov diffeomorphism is the closure of its periodic points and a
finite disjoint union of nonempty compact invariant locally maximal components with dense full
orbits and dense periodic points. Each component's stable and unstable basin intersection
consists of nonwandering points (Shub, Thm. 8.13; Props. 8.20–8.22 and 9.8; Mañé, I§11, Prop.
11.4). -/
theorem smale_original_anosov_spectral_core
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] [SecondCountableTopology M]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Es Eu : ContinuousRealTangentSubbundle
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M)
    (metric : Bundle.ContMDiffRiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x))
    (C lam : ℝ) :
    let I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    IsRiemannianManifold I M →
    0 < C → 0 < lam → lam < 1 →
    (∀ x, IsCompl (Es.toDistribution x) (Eu.toDistribution x)) →
    (∀ x, (Es.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Es.toDistribution (f x)) →
    (∀ x, (Eu.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Eu.toDistribution (f x)) →
    (∀ x k (v : TangentSpace I x), v ∈ Es.toDistribution x →
      ‖mfderiv I I ((f : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ x k (v : TangentSpace I x), v ∈ Eu.toDistribution x →
      ‖mfderiv I I ((f.symm : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    let Ω : Set M := {x | ∀ U : Set M, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (((f : M → M)^[k]) '' U ∩ U).Nonempty}
    let Ws : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    let Wu : Set M → Set M := fun L =>
      {x | Tendsto (fun k : ℕ => Metric.infDist (((f.symm : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    closure (Function.periodicPts (f : M → M)) = Ω ∧
    ∃ (b : ℕ) (L : Fin b → Set M), 1 ≤ b ∧
      (∀ i, (L i).Nonempty ∧ IsCompact (L i) ∧ f '' L i = L i) ∧
      Pairwise (fun i j => Disjoint (L i) (L j)) ∧
      Ω = ⋃ i, L i ∧
      (∀ i, ∃ x ∈ L i,
        closure (Set.range (fun k : ℤ => (f.toEquiv ^ k) x)) = L i) ∧
      (∀ i, closure (Function.periodicPts (f : M → M) ∩ L i) = L i) ∧
      (∀ i, ∃ U : Set M, IsOpen U ∧ L i ⊆ U ∧
        L i = ⋂ k : ℤ, (fun x => (f.toEquiv ^ k) x) '' U) ∧
      (∀ i, Ws (L i) ∩ Wu (L i) ⊆ Ω) := by
  classical
  dsimp only
  intro hR hC hlam hlam1 hcompl hEs hEu hs hu
  cases subsingleton_or_nontrivial M with
  | inl hM =>
    let : Subsingleton M := hM
    have hper : Function.periodicPts (f : M → M) = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      exact Function.mem_periodicPts.mpr ⟨1, by omega, Subsingleton.elim _ _⟩
    have hΩ : {x : M | ∀ U : Set M, IsOpen U → x ∈ U →
        ∃ k : ℕ, 0 < k ∧ (((f : M → M)^[k]) '' U ∩ U).Nonempty} = Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro U hU hx
      refine ⟨1, by omega, x, ⟨x, hx, Subsingleton.elim _ _⟩, hx⟩
    rw [hper, closure_univ, hΩ]
    refine ⟨rfl, 1, fun _ ↦ Set.univ, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨Set.univ_nonempty, isCompact_univ, Set.image_univ_of_surjective f.surjective⟩
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
    · exact Set.Subset.antisymm (fun x _ ↦ Set.mem_iUnion.mpr ⟨0, Set.mem_univ x⟩)
        (Set.subset_univ _)
    · intro i
      refine ⟨Classical.arbitrary M, Set.mem_univ _, ?_⟩
      have hrange : Set.range (fun k : ℤ ↦ (f.toEquiv ^ k) (Classical.arbitrary M)) =
          Set.univ := by
        ext x
        simp only [Set.mem_range, Set.mem_univ, iff_true]
        exact ⟨0, Subsingleton.elim _ _⟩
      rw [hrange, closure_univ]
    · intro i
      simp
    · intro i
      refine ⟨Set.univ, isOpen_univ, Set.Subset.rfl, ?_⟩
      simp only [Set.image_univ_of_surjective (Equiv.surjective _), Set.iInter_univ]
    · intro i
      exact Set.subset_univ _
  | inr hM =>
    let : Nontrivial M := hM
    let Ω : Set M := {x | ∀ U : Set M, IsOpen U → x ∈ U →
      ∃ k : ℕ, 0 < k ∧ (((f : M → M)^[k]) '' U ∩ U).Nonempty}
    let Ws : Set M → Set M := fun L ↦
      {x | Tendsto (fun k : ℕ ↦ Metric.infDist (((f : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    let Wu : Set M → Set M := fun L ↦
      {x | Tendsto (fun k : ℕ ↦ Metric.infDist (((f.symm : M → M)^[k]) x) L)
        atTop (𝓝 0)}
    let originalDistance : MetricSpace M := inferInstance
    let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
      ⟨metric.toRiemannianMetric⟩
    let splitting : InvariantRealTangentSplitting f :=
      { stable := Es
        unstable := Eu
        isCompl := hcompl
        stable_map := hEs
        unstable_map := hEu }
    have hsAP : ∀ x k (v : TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x),
        v ∈ splitting.stable.toDistribution x →
        hyperbolicRiemannianNorm metric (mfderiv _ _ ((f : M → M)^[k]) x v) ≤
          max 1 C * lam ^ k * hyperbolicRiemannianNorm metric v := by
      intro x k v hv
      have hbound := hs x k v hv
      have hmono : C * lam ^ k * ‖v‖ ≤ max 1 C * lam ^ k * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 C) (pow_nonneg hlam.le k))
          (norm_nonneg v)
      exact hbound.trans hmono
    have huAP : ∀ x k (v : TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x),
        v ∈ splitting.unstable.toDistribution x →
        hyperbolicRiemannianNorm metric (mfderiv _ _ ((f.symm : M → M)^[k]) x v) ≤
          max 1 C * lam ^ k * hyperbolicRiemannianNorm metric v := by
      intro x k v hv
      have hbound := hu x k v hv
      have hmono : C * lam ^ k * ‖v‖ ≤ max 1 C * lam ^ k * ‖v‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 C) (pow_nonneg hlam.le k))
          (norm_nonneg v)
      exact hbound.trans hmono
    obtain ⟨hAP, dAP, componentDistance, θAP, rateAP, βAP, γAP, εAP,
      hD, hθ, hθ1, hrate, hrate1, hγ, hβ, hε, htop, hmetric, hcomponents,
      hforward, hbackward, S, U, hS, hU, hstablePair, hunstablePair,
      hSlength, hUlength, hSadvance, hUadvance, bracket, hbracketContinuous,
      hbracketUnique, hproduct⟩ :=
      hirschPughAdaptedOrbitPlaques f splitting metric (max 1 C) lam
        (le_max_left 1 C) hlam hlam1 hsAP huAP
    let : MetricSpace M := originalDistance
    have hAPexpansive : ∀ x y : M,
        (∀ k : ℕ, dAP.dist (((f : M → M)^[k]) y) (((f : M → M)^[k]) x) ≤ γAP) →
        (∀ k : ℕ, dAP.dist (((f.symm : M → M)^[k]) y)
          (((f.symm : M → M)^[k]) x) ≤ γAP) → x = y := by
      intro x y hpos hneg
      let pair : adaptedClosePairDomain (M := M) dAP εAP :=
        ⟨(x, x), by change dAP.dist x x < εAP; rw [dAP.dist_self]; exact hε⟩
      have hset := hbracketUnique pair
      have hx : x ∈ adaptedClosedOrbitCore _ f dAP γAP x ∩
          adaptedClosedOrbitCore _ f.symm dAP γAP x := by
        constructor <;> intro k <;>
          rw [dAP.dist_self] <;> exact hγ.le
      have hy : y ∈ adaptedClosedOrbitCore _ f dAP γAP x ∩
          adaptedClosedOrbitCore _ f.symm dAP γAP x := ⟨hpos, hneg⟩
      rw [hset] at hx hy
      exact (Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm
    have hAPinteger : ∀ x y : M,
        (∀ k : ℤ, dAP.dist ((f.toEquiv ^ k) x) ((f.toEquiv ^ k) y) ≤ γAP) → x = y := by
      intro x y hxy
      apply hAPexpansive
      · intro k
        have hk := hxy (k : ℤ)
        rw [zpow_natCast, Equiv.Perm.coe_pow] at hk
        rw [dAP.dist_comm]
        exact hk
      · intro k
        have hk := hxy (-(k : ℤ))
        rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow] at hk
        rw [dAP.dist_comm]
        exact hk
    obtain ⟨expansiveRadius, hexpansiveRadius, hexpansive⟩ :=
      Dynamics.ManningOriginalBasicSetSignedTraceG7.MetricAdapter.compatible_metric_expansivity
        dAP htop f.toEquiv hγ hAPinteger
    have hcyclic := smale_original_anosov_cyclic_shadowing f Es Eu metric C lam
      hR hC hlam hlam1 hcompl hEs hEu hs hu
    obtain ⟨b, L, hL, hdisjoint, hcover, htransitive, hfinite, hbasins⟩ :=
      smale_original_anosov_transitive_components f Es Eu metric C lam
        hR hC hlam hlam1 hcompl hEs hEu hs hu hcyclic
    change Ω = ⋃ i, L i at hcover
    have hb : 1 ≤ b := by
      obtain ⟨x, hx⟩ := smale_nonwandering_nonempty (f : M → M)
      change x ∈ Ω at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ hx)
      exact Nat.succ_le_of_lt (Nat.zero_le i.val |>.trans_lt i.isLt)
    have hdense : ∀ i, ∃ x ∈ L i,
        closure (Set.range (fun k : ℤ => (f.toEquiv ^ k) x)) = L i := by
      intro i
      exact smale_dense_full_orbit_of_transitivity f.toHomeomorph (L i)
        (hL i).1 (hL i).2.1 (hL i).2.2 (htransitive i)
    have hperiodicGlobal : closure (Function.periodicPts (f : M → M)) = Ω :=
      smale_closure_periodic_eq_nonwandering_of_periodic_shadowing f
        (smale_periodic_shadowing_of_cyclic_semiconjugacy (f : M → M) hcyclic)
    have hperiodic : ∀ i, closure (Function.periodicPts (f : M → M) ∩ L i) = L i := by
      have hclosed : ∀ i, closure (Function.periodicPts (f : M → M) ∩ L i) ⊆ L i :=
        fun i ↦ closure_minimal Set.inter_subset_right (hL i).2.1.isClosed
      have hdecompose : Function.periodicPts (f : M → M) =
          ⋃ i, Function.periodicPts (f : M → M) ∩ L i := by
        apply Set.Subset.antisymm
        · intro x hx
          have hxΩ : x ∈ Ω := hperiodicGlobal ▸ subset_closure hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ hxΩ)
          exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
        · intro x hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          exact hi.1
      have hcoverClosure : Ω =
          ⋃ i, closure (Function.periodicPts (f : M → M) ∩ L i) := by
        calc
          Ω = closure (Function.periodicPts (f : M → M)) := hperiodicGlobal.symm
          _ = closure (⋃ i, Function.periodicPts (f : M → M) ∩ L i) :=
            congrArg closure hdecompose
          _ = ⋃ i, closure (Function.periodicPts (f : M → M) ∩ L i) :=
            closure_iUnion_of_finite _
      intro i
      apply Set.Subset.antisymm (hclosed i)
      intro x hx
      have hxΩ : x ∈ Ω := hcover ▸ Set.mem_iUnion.mpr ⟨i, hx⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcoverClosure ▸ hxΩ)
      have hij : i = j := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisjoint hne) hx (hclosed j hj)
      simpa only [hij] using hj
    refine ⟨hperiodicGlobal, b, L, hb, hL, hdisjoint, hcover, hdense,
      hperiodic, ?_, hbasins⟩
    intro i
    have hshadow := smale_shadowing_of_finite_shadowing f.toHomeomorph (L i)
      (hL i).2.1 (hL i).2.2 (hfinite i)
    exact smale_locallyMaximal_of_shadowing_of_expansive f.toEquiv (L i)
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (hL i).2.2 expansiveRadius hexpansiveRadius
      (fun x y hxy ↦ hexpansive x y (fun k ↦ (hxy k).le)) hshadow


end HolomorphicAnosov
