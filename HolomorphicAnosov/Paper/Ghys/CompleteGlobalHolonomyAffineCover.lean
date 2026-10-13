import HolomorphicAnosov.Geometry.CoveringGlobalHolonomyDevelopingGerm
import HolomorphicAnosov.Geometry.ProjectivePoleAffineChart
import HolomorphicAnosov.Geometry.CoveringDevelopingProductCharts
import HolomorphicAnosov.Geometry.CoveringPlaqueRelationEq
import HolomorphicAnosov.Geometry.NativeStableLeafEuclideanTransport
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalSmoothTangentMetricExists
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.OriginalAllIteratesHermitian
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ManifoldInverse
import HolomorphicAnosov.Geometry.ContinuousStableLeafLiftG9
import HolomorphicAnosov.Geometry.FinitePlaqueChainsOfLocalCoverG10
import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic
import HolomorphicAnosov.Geometry.ProjectiveFixedInfinityAffine
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveFiniteNeInfinity
import Mathlib.GroupTheory.GroupAction.Primitive
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import HolomorphicAnosov.Analysis.Complex.ConnectedCurveHolomorphicIdentity
import HolomorphicAnosov.Paper.Ghys.NativeStablePointHomeomorph
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Paper.Ghys.NativeUnstablePointBiholomorphG10
import HolomorphicAnosov.Geometry.GlobalHolonomyLiftGermG10
import HolomorphicAnosov.Geometry.GlobalHolonomyStableGermG10
import HolomorphicAnosov.Geometry.OmittedPointLeafConstG10
import HolomorphicAnosov.Paper.Ghys.ProjectiveDeveloping
import HolomorphicAnosov.Paper.Ghys.IntrinsicLeafProduct
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Topology.FreeAffineActionTranslations
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.NativeTransverseAsymptoticIdentification
import HolomorphicAnosov.Geometry.GlobalHolonomy
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.Deck
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.Paper.Ghys.PartitionRelationOfPointIdentification
import HolomorphicAnosov.Paper.Ghys.NativePartitionsEq
import HolomorphicAnosov.Paper.Ghys.InjectivePointedLeafLift
import HolomorphicAnosov.Paper.Ghys.HolomorphicOfLift
import HolomorphicAnosov.Paper.Ghys.ProjectionInjectiveOnLiftedFibre
import HolomorphicAnosov.Paper.Ghys.DeckIdentityOfFixedPoint
import HolomorphicAnosov.Paper.Ghys.TranslationsOfAffineDeveloping
import HolomorphicAnosov.Paper.Ghys.OmittedPointEqOfLeafIntertwining
import HolomorphicAnosov.Paper.Ghys.UniqueLeafProductEquiv
import HolomorphicAnosov.Paper.Ghys.ProductHomeomorphOfContinuousRetraction
import HolomorphicAnosov.Paper.Ghys.DevelopingFibreRetraction
import HolomorphicAnosov.Paper.Ghys.DevelopingFibreConnected
import HolomorphicAnosov.Paper.Ghys.LiftedLeafRangeOfDevelopingProduct
import HolomorphicAnosov.Paper.Ghys.ProjectionInjectiveOfDevelopingProduct
import HolomorphicAnosov.Geometry.ProjectiveDevelopingStableConstG10
import HolomorphicAnosov.Geometry.ReverseLiftEndpointG10

/-! This file constructs a developing product on the universal cover from global stable holonomy,
with a faithful translation action of the fundamental group. (Ghys, §5, pp. 597–598; Hatcher, Props.
1.33–1.34) -/


noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys

attribute [local instance] complex_isManifold_real

/-- Global stable holonomy yields a complex universal cover homeomorphic to `ℝ^(2*d)`, with a
surjective developing map to `ℂ` whose fibres are lifted stable leaves and whose restrictions to
lifted unstable leaves are biholomorphic coordinates. The cover is a product of a developing fibre
with `ℂ`, and its fundamental group acts faithfully by translations and is abelian and torsion-free.
(Ghys, §5, pp. 597–598; Hatcher, Props. 1.33–1.34) -/
theorem complete_global_holonomy_affine_cover
    {d s : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (ComplexModel d) M] [IsCompactComplexManifold d M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hrank : HasComplexRankOne a.splitting.unstable.toDistribution)
    (A : NativeTransverseAsymptoticIdentification.{u, w} (d := d)
      f.toHomeomorph a.splitting.stable.toDistribution
      a.splitting.unstable.toDistribution s 2) :
    letI := A.realAmbientCharts
    ∀ C : IntrinsicComplexUnstableLeaves A.F,
    (∀ q : Quotient A.F.unstablePartition,
      letI := A.F.unstableTopology q
      letI := C.charts q
      ContMDiff (complexModel 1) (complexModel d) ∞
        (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) ∧
      ∀ z : IntrinsicFoliationLeaf A.F.unstablePartition q,
        Manifold.IsImmersionAt (complexModel 1) (complexModel d) ∞
          (Subtype.val : IntrinsicFoliationLeaf A.F.unstablePartition q → M) z) →
    HasGlobalSHolonomy A.F C →
    ∀ (E : Type v) [TopologicalSpace E] [SimplyConnectedSpace E]
      (p : E → M), IsCoveringMap p → Function.Surjective p → ∀ e0 : E,
    let stableLink : E → E → Prop := fun x y ↦
      ∃ i : A.F.boxIndex, ∃ w : FoliationCoordinateDisk 2, ∃ β : Path x y,
        ∀ t : unitInterval, ∃ z : FoliationCoordinateDisk s,
          p (β t) = ((A.F.box i).chart (z, w)).val
    let unstableLink : E → E → Prop := fun x y ↦
      ∃ i : A.F.boxIndex, ∃ z : FoliationCoordinateDisk s, ∃ β : Path x y,
        ∀ t : unitInterval, ∃ w : FoliationCoordinateDisk 2,
          p (β t) = ((A.F.box i).chart (z, w)).val
    ∃ charts : ChartedSpace (ComplexModel d) E,
    letI := charts
    ∃ smooth : IsManifold (complexModel d) ∞ E,
    letI := smooth
    IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p ∧
    ∃ (D : C(E, ℂ)) (z0 : ℂ)
      (δ : FundamentalGroup M (p e0) ≃* deck p)
      (tau : FundamentalGroup M (p e0) →* Multiplicative ℂ),
      (∀ e : E,
        letI := A.F.stableTopology (Quotient.mk A.F.stablePartition (p e))
        ∃ (V : TopologicalSpace.Opens (IntrinsicFoliationLeaf A.F.stablePartition
            (Quotient.mk A.F.stablePartition (p e))))
          (W : TopologicalSpace.Opens ℂ) (O : TopologicalSpace.Opens E)
          (h : (V × W) ≃ₜ O),
          e ∈ O ∧ D e ∈ W ∧
          (∀ (r : V) (z : W), D (h (r, z)).val = z.val) ∧
          (∀ (r : V) (z : W), z.val = D e → p (h (r, z)).val = r.val.val) ∧
          (∃ (i : A.F.boxIndex) (w : FoliationCoordinateDisk 2),
            ∀ r : V, ∃ z : FoliationCoordinateDisk s,
              r.val.val = ((A.F.box i).chart (z, w)).val)) ∧
      Function.Surjective D ∧ Function.Injective tau ∧
      (∀ (γ : FundamentalGroup M (p e0)) (α : Path (p e0) (p e0)),
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α) = γ →
        ∃ β : Path e0 ((δ γ : E ≃ₜ E) e0),
          ∀ t : unitInterval, p (β t) = α.symm t) ∧
      (∀ (γ : FundamentalGroup M (p e0)) (e : E),
        D ((δ γ : E ≃ₜ E) e) = D e + (tau γ).toAdd) ∧
      (∀ x y : E, D x = D y ↔ Relation.EqvGen stableLink x y) ∧
      (∃ B : ({e : E // D e = z0} × ℂ) ≃ₜ E,
        ∀ (r : {e : E // D e = z0}) (z : ℂ), D (B (r, z)) = z) ∧
      (∀ e : E,
        letI := A.F.stableTopology (Quotient.mk A.F.stablePartition (p e))
        ∃ lift : IntrinsicFoliationLeaf A.F.stablePartition
            (Quotient.mk A.F.stablePartition (p e)) → E,
          Continuous lift ∧ Function.Injective lift ∧
          (∀ x, p (lift x) = x.val) ∧ (∀ x, x.val = p e → lift x = e) ∧
          Set.range lift = {y : E | Relation.EqvGen stableLink e y} ∧
          IsEmbedding lift) ∧
      (∀ e : E,
        letI := A.F.unstableTopology (Quotient.mk A.F.unstablePartition (p e))
        letI := C.charts (Quotient.mk A.F.unstablePartition (p e))
        ∃ (lift : A.F.ULeaf (p e) → E)
          (coordinate : Diffeomorph (complexModel 1) 𝓘(ℂ) (A.F.ULeaf (p e)) ℂ ∞),
          ContMDiff (complexModel 1) (complexModel d) ∞ lift ∧
          Function.Injective lift ∧ (∀ x, p (lift x) = x.val) ∧
          (∀ x, x.val = p e → lift x = e) ∧
          Set.range lift = {y : E | Relation.EqvGen unstableLink e y} ∧
          (∀ x, coordinate x = D (lift x))) ∧
      Nonempty (E ≃ₜ (Fin (2*d) → ℝ)) ∧
      (∀ x y : FundamentalGroup M (p e0), x * y = y * x) ∧
      (∀ γ : FundamentalGroup M (p e0), ∀ n : ℕ,
        0 < n → γ ^ n = 1 → γ = 1) := by
  classical
  let := A.realAmbientCharts
  intro C hC hHol E _ _ p hp hsurj e0
  have hu : ∀ x : M, Module.finrank ℝ (a.splitting.unstable.toDistribution x) = 2 :=
    fun x ↦ TheoremAProof.Dimension.HasComplexRankOne.real_finrank_eq_two hrank x
  obtain ⟨s', B, CB, hBcompat, hBhol, affine, hcomplete, atlas, hatlas, hdevelop⟩ :=
    projectiveDeveloping f a hu (p e0)
  have hpartitions := native_partitions_eq f a A B
  have hleafComplex := fun x : M ↦
    native_unstable_point_biholomorph_g10 A B C CB x
      (hC (Quotient.mk A.F.unstablePartition x)) (hBhol x) (hBcompat x).2
  let G := Classical.choice hHol
  have hholonomyPoint :
      ∀ {q : Quotient A.F.stablePartition}
        {x y : IntrinsicFoliationLeaf A.F.stablePartition q} (γ : Path x y),
        G.transport γ (A.F.uPoint x.val) = A.F.uPoint y.val := by
    intro q x y γ
    exact global_holonomy_map_point_g10 A.F C G γ
  have hholonomyStableGerm :
      ∀ {q : Quotient A.F.stablePartition}
        {x y : IntrinsicFoliationLeaf A.F.stablePartition q} (γ : Path x y),
        ∀ᶠ z : A.F.ULeaf x.val in 𝓝 (A.F.uPoint x.val),
          (letI := B.realAmbientCharts; B.F.stablePartition)
            z.val (G.transport γ z).val := by
    intro q x y γ
    rw [← hpartitions.1]
    exact global_holonomy_eventually_stable_related_g10 A.F C G γ
  have hrange : Set.range p = connectedComponent (p e0) := by
    rw [Set.range_eq_univ.mpr hsurj, PreconnectedSpace.connectedComponent_eq_univ]
  obtain ⟨charts, smooth, hlocal, D₀, hproducts, htransverse, δ, hendpoint, hrest⟩ :=
    hdevelop E p hp e0 rfl hrange
  let := charts
  let := smooth
  obtain ⟨ρ, hρ, hSlifts, hUlifts⟩ := hrest
  let := B.realAmbientCharts
  let stableLinkB : E → E → Prop := fun x y ↦
    ∃ i : B.F.boxIndex, ∃ w : FoliationCoordinateDisk 2, ∃ β : Path x y,
      ∀ t : unitInterval, ∃ z : FoliationCoordinateDisk s',
        p (β t) = ((B.F.box i).chart (z, w)).val
  have hstableD : ∀ x y : E,
      Relation.EqvGen stableLinkB x y → D₀ x = D₀ y := by
    apply projective_developing_eq_of_stable_link (D₀ : E → ComplexProjectiveLine) stableLinkB
    intro x
    obtain ⟨lift, hcont, hinj, hpoint, hlift, hrange, hfibre⟩ := hSlifts x
    exact ⟨_, lift, hrange, hfibre⟩
  let unstableLinkB : E → E → Prop := fun x y ↦
    ∃ i : B.F.boxIndex, ∃ z : FoliationCoordinateDisk s', ∃ β : Path x y,
      ∀ t : unitInterval, ∃ w : FoliationCoordinateDisk 2,
        p (β t) = ((B.F.box i).chart (z, w)).val
  have hAlifts : ∀ x : E,
      letI := A.realAmbientCharts
      letI := C.charts (Quotient.mk A.F.unstablePartition (p x))
      ∃ lift : A.F.ULeaf (p x) → E,
        ContMDiff (complexModel 1) (complexModel d) ∞ lift ∧
        Function.Injective lift ∧ (∀ z, p (lift z) = z.val) ∧
        (∀ z, z.val = p x → lift z = x) ∧
        Set.range lift = {y | Relation.EqvGen unstableLinkB x y} := by
    intro x
    let := A.realAmbientCharts
    let := C.charts (Quotient.mk A.F.unstablePartition (p x))
    let := CB.charts (Quotient.mk B.F.unstablePartition (p x))
    obtain ⟨e, he⟩ := hleafComplex (p x)
    obtain ⟨lift, hhol, hinj, hpoint, hproj, hrange, _⟩ := hUlifts x
    refine ⟨lift ∘ e, hhol.comp e.contMDiff, hinj.comp e.injective, ?_, ?_, ?_⟩
    · intro z
      exact (hproj (e z)).trans (he z)
    · intro z hz
      change lift (e z) = x
      have hz' : e z = B.F.uPoint (p x) := Subtype.ext ((he z).trans hz)
      rw [hz']
      exact hpoint
    · have herange : Set.range (e : A.F.ULeaf (p x) → B.F.ULeaf (p x)) = Set.univ :=
        Set.range_eq_univ.mpr e.surjective
      rw [Set.range_comp, herange, Set.image_univ]
      exact hrange
  have hleafPole : ∀ x : E, ∃ pole : ComplexProjectiveLine,
      D₀ '' {y : E | Relation.EqvGen unstableLinkB x y} = {pole}ᶜ := by
    intro x
    obtain ⟨lift, _, _, _, _, hliftRange, pole, e, hsource, htarget, he, _, _⟩ :=
      hUlifts x
    refine ⟨pole, ?_⟩
    rw [← hliftRange, ← Set.range_comp]
    have heq : (D₀ : E → ComplexProjectiveLine) ∘ lift = e := funext fun z ↦ (he z).symm
    rw [heq, ← Set.image_univ, ← hsource, e.image_source_eq_target, htarget]
  choose pole hpole using hleafPole
  have hpole_unstable : ∀ x y : E,
      Relation.EqvGen unstableLinkB x y → pole x = pole y := by
    intro x y hxy
    exact omitted_point_eq_of_leaf_class_g10 D₀ unstableLinkB pole hpole hxy
  have hASlifts : ∀ x : E,
      ∃ lift : IntrinsicFoliationLeaf A.F.stablePartition
          (Quotient.mk A.F.stablePartition (p x)) → E,
        Continuous lift ∧ lift ⟨p x, rfl⟩ = x ∧
        (∀ z, p (lift z) = z.val) ∧ (∀ z, D₀ (lift z) = D₀ x) := by
    intro x
    obtain ⟨H, hH⟩ := native_stable_point_homeomorph A B (p x)
    obtain ⟨l, hl, hi, hx, hproj, hrange, hfibre⟩ := hSlifts x
    refine ⟨l ∘ H, hl.comp H.continuous, ?_, ?_, ?_⟩
    · have hh : H ⟨p x, rfl⟩ = ⟨p x, rfl⟩ := Subtype.ext (hH _)
      simpa only [Function.comp_apply, hh] using hx
    · intro z
      exact (hproj (H z)).trans (hH z)
    · intro z
      apply Eq.symm
      apply hstableD x
      have hz : l (H z) ∈ Set.range l := ⟨H z, rfl⟩
      rw [hrange] at hz
      exact hz
  have hDbox : ∀ (i : A.F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk 2, E)),
      (∀ z, p (L z) = ((A.F.box i).chart z).val) →
      ∀ z z' w, D₀ (L (z, w)) = D₀ (L (z', w)) := covering_developing_const_on_box A.F p hp D₀ hASlifts
  have hAUdata : ∀ x : E,
      letI := C.charts (Quotient.mk A.F.unstablePartition (p x))
      ∃ lift : A.F.ULeaf (p x) → E,
        ContMDiff (complexModel 1) (complexModel d) ∞ lift ∧
        Function.Injective lift ∧ (∀ z, p (lift z) = z.val) ∧
        lift (A.F.uPoint (p x)) = x ∧
        Set.range lift = {y | Relation.EqvGen unstableLinkB x y} ∧
        ContMDiff (complexModel 1) (complexModel 1) ∞ (D₀ ∘ lift) ∧
        Set.range (D₀ ∘ lift) = {pole x}ᶜ := by
    intro x
    let := C.charts (Quotient.mk A.F.unstablePartition (p x))
    let := CB.charts (Quotient.mk B.F.unstablePartition (p x))
    obtain ⟨H, hH⟩ := hleafComplex (p x)
    obtain ⟨l, hl, hi, hx, hpL, hr, o, e, hes, het, he, hhol, hinv⟩ := hUlifts x
    have hj : Set.range (l ∘ H) = {y | Relation.EqvGen unstableLinkB x y} := by
      have hrH : Set.range (H : A.F.ULeaf (p x) → B.F.ULeaf (p x)) = Set.univ :=
        Set.range_eq_univ.mpr H.surjective
      rw [Set.range_comp, hrH, Set.image_univ]
      exact hr
    have hDH : ContMDiff (complexModel 1) (complexModel 1) ∞ (D₀ ∘ l ∘ H) := by
      have hh : ContMDiff (complexModel 1) (complexModel 1) ∞ e := by
        rw [hes] at hhol
        exact contMDiffOn_univ.mp hhol
      have heq : (D₀ : E → ComplexProjectiveLine) ∘ l = e := funext fun z ↦ (he z).symm
      rw [← Function.comp_assoc, heq]
      exact hh.comp H.contMDiff
    refine ⟨l ∘ H, hl.comp H.contMDiff, hi.comp H.injective,
      fun z ↦ (hpL (H z)).trans (hH z), ?_, hj, hDH, ?_⟩
    · have hh : H (A.F.uPoint (p x)) = B.F.uPoint (p x) := Subtype.ext (hH _)
      simpa only [Function.comp_apply, hh] using hx
    · rw [Set.range_comp, hj]
      exact hpole x
  choose UL hULhol hULinj hULproj hULpoint hULrange hULdev hULdevrange using hAUdata
  let : T2Space ComplexProjectiveLine := NativeProjectiveTopology.t2_native_projective_line
  have hpole_all : ∀ x : E, pole x = pole e0 :=
    covering_global_holonomy_common_pole A.F C G p hp D₀ unstableLinkB pole hDbox UL
      (fun x ↦ by
        let := C.charts (Quotient.mk A.F.unstablePartition (p x))
        exact (hULhol x).continuous)
      hULproj hULpoint hULrange hULdev hULdevrange hpole_unstable e0
  obtain ⟨m, hm, q, hqs, hqt, hqhol, hqinv, hqformula⟩ := projective_pole_affine_chart (pole e0)
  have hDsource (x : E) : D₀ x ∈ q.source := by
    rw [hqs, ← hpole_all x, ← hULdevrange x]
    exact ⟨A.F.uPoint (p x), congrArg D₀ (hULpoint x)⟩
  let D : C(E, ℂ) := ⟨q ∘ D₀, q.continuousOn.comp_continuous D₀.continuous hDsource⟩
  have hDinj {x y : E} : D x = D y ↔ D₀ x = D₀ y :=
    ⟨q.injOn (hDsource x) (hDsource y), congrArg q⟩
  have hUcoordinates : ∀ x : E,
      letI := C.charts (Quotient.mk A.F.unstablePartition (p x))
      ∃ coordinate : Diffeomorph (complexModel 1) 𝓘(ℂ) (A.F.ULeaf (p x)) ℂ ∞,
        ∀ z, coordinate z = D (UL x z) := by
    intro x
    let := C.charts (Quotient.mk A.F.unstablePartition (p x))
    let := CB.charts (Quotient.mk B.F.unstablePartition (p x))
    let : PreconnectedSpace (A.F.ULeaf (p x)) := (A.F.unstable_connected _).toPreconnectedSpace
    obtain ⟨H, hH⟩ := hleafComplex (p x)
    obtain ⟨l, hl, hi, hx, hpL, hr, o, e, hes, het, he, hehol, heinv⟩ := hUlifts x
    have htarget : e.target = {pole e0}ᶜ := by
      rw [← e.image_source_eq_target, hes, Set.image_univ]
      rw [show (e : B.F.ULeaf (p x) → ComplexProjectiveLine) = D₀ ∘ l from funext he,
        Set.range_comp, hr, hpole x, hpole_all x]
    obtain ⟨K, hK⟩ := projective_pole_coordinate (pole e0) e q hes htarget hqs hqt
      hehol heinv hqhol hqinv
    have hULeq : l ∘ H = UL x := hp.eq_of_comp_eq
      (hl.continuous.comp H.continuous) (hULhol x).continuous
      (by funext z; exact ((hpL (H z)).trans (hH z)).trans (hULproj x z).symm)
      (A.F.uPoint (p x)) (by
        have hHH : H (A.F.uPoint (p x)) = B.F.uPoint (p x) := Subtype.ext (hH _)
        simpa only [Function.comp_apply, hHH, hx] using (hULpoint x).symm)
    refine ⟨H.trans K, fun z ↦ ?_⟩
    change K (H z) = q (D₀ (UL x z))
    rw [hK, he, ← congrFun hULeq z]
    rfl
  choose UC hUC using hUcoordinates
  have hULcont (x : E) : Continuous (UL x) := by
    let := C.charts (Quotient.mk A.F.unstablePartition (p x))
    exact (hULhol x).continuous
  have hDsurj : Function.Surjective D := by
    let := C.charts (Quotient.mk A.F.unstablePartition (p e0))
    intro z
    exact ⟨UL e0 ((UC e0).symm z), (hUC e0 _).symm.trans ((UC e0).apply_symm_apply z)⟩
  let : ∀ x : E, PathConnectedSpace (A.F.ULeaf (p x)) := fun x ↦ by
    let := C.charts (Quotient.mk A.F.unstablePartition (p x))
    exact (UC x).toHomeomorph.symm.pathConnectedSpace
  have hDbox' : ∀ (i : A.F.boxIndex)
      (L : C(FoliationCoordinateDisk s × FoliationCoordinateDisk 2, E)),
      (∀ z, p (L z) = ((A.F.box i).chart z).val) →
      ∀ z z' w, D (L (z, w)) = D (L (z', w)) := by
    intro i L hL z z' w
    exact congrArg q (hDbox i L hL z z' w)
  have hboxes := covering_developing_product_charts A.F p hp D hDbox' unstableLinkB
    UL hULcont hULproj hULpoint hULrange (fun x ↦ by
      let := C.charts (Quotient.mk A.F.unstablePartition (p x))
      exact (UC x).toHomeomorph) hUC
  choose O W H hxO hxW hHcoord hHleaf hHstable using hboxes
  obtain ⟨ProdH, hProdH⟩ := product_homeomorph_of_intrinsic_leaf_coordinates
    D D.continuous unstableLinkB (D e0) (fun x ↦ (O x : Set E))
    (fun x ↦ (W x : Set ℂ)) H (fun x ↦ (O x).isOpen) (fun x ↦ (W x).isOpen)
    (fun x ↦ ⟨x, hxO x⟩) hHcoord hHleaf (fun x ↦ A.F.ULeaf (p x))
    UL hULcont (fun x ↦ by
      let := C.charts (Quotient.mk A.F.unstablePartition (p x))
      exact (UC x).toEquiv) hULrange hUC
  have hUrel := covering_unstable_plaque_relation_eq A.F p hp unstableLinkB UL
    hULcont hULproj hULpoint hULrange

  have hSdata : ∀ x : E,
      ∃ l : IntrinsicFoliationLeaf A.F.stablePartition (Quotient.mk A.F.stablePartition (p x)) → E,
        Continuous l ∧ Function.Injective l ∧ l ⟨p x, rfl⟩ = x ∧
        (∀ z, p (l z) = z.val) ∧
        Set.range l = {y | Relation.EqvGen stableLinkB x y} ∧
        Set.range l = connectedComponentIn (D ⁻¹' {D x}) x := by
    intro x
    obtain ⟨H, hH⟩ := native_stable_point_homeomorph A B (p x)
    obtain ⟨l, hl, hi, hx, hpL, hr, hc⟩ := hSlifts x
    have hrH : Set.range (H : IntrinsicFoliationLeaf A.F.stablePartition
        (Quotient.mk A.F.stablePartition (p x)) →
        IntrinsicFoliationLeaf B.F.stablePartition (Quotient.mk B.F.stablePartition (p x))) =
        Set.univ := Set.range_eq_univ.mpr H.surjective
    have hrange : Set.range (l ∘ H) = Set.range l := by
      rw [Set.range_comp, hrH, Set.image_univ]
    refine ⟨l ∘ H, hl.comp H.continuous, hi.comp H.injective, ?_,
      fun z ↦ (hpL (H z)).trans (hH z), hrange.trans hr, ?_⟩
    · have hh : H ⟨p x, rfl⟩ = ⟨p x, rfl⟩ := Subtype.ext (hH _)
      simpa only [Function.comp_apply, hh] using hx
    · rw [hrange, hc]
      congr 1
      ext y
      exact hDinj.symm
  choose SL hSLcont hSLinj hSLpoint hSLproj hSLrange hSLcomponent using hSdata
  have hSrel := covering_stable_plaque_relation_eq A.F p hp stableLinkB SL
    hSLcont hSLproj hSLpoint hSLrange
  have hSLfibre (x : E) : Set.range (SL x) = {y | D y = D x} :=
    lifted_leaf_range_of_developing_product D (D e0) ProdH hProdH x (SL x) (hSLcomponent x)
  have hpfibre : ∀ z : ℂ, Set.InjOn p {x | D x = z} := by
    intro z
    obtain ⟨x, rfl⟩ := hDsurj z
    exact projection_injective_on_lifted_fibre p D (D x) Subtype.val Subtype.val_injective
      (SL x) (hSLproj x) (hSLfibre x)
  have hD0range : Set.range D₀ = {pole e0}ᶜ := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, rfl⟩
      rw [← hqs]
      exact hDsource x
    · intro z hz
      rw [← hULdevrange e0] at hz
      obtain ⟨a, ha⟩ := hz
      exact ⟨UL e0 a, ha⟩
  have haff : ∀ g : FundamentalGroup M (p e0), ∃ α β : ℂ,
      ∀ x : E, D ((δ g : E ≃ₜ E) x) = α * D x + β :=
    projective_common_pole_affine_formula D₀ (fun g ↦ (δ g : E ≃ₜ E).toEquiv)
      ρ (pole e0) hD0range (fun g x ↦ hρ g x) m hm q hqformula
  choose α β haffeq using haff
  obtain ⟨tau, htau, htranslation, hcomm, htf⟩ :=
    translations_of_affine_developing hp D hDsurj δ α β haffeq hpfibre

  have hStableCast (Q Q' : Quotient A.F.stablePartition) (h : Q = Q') :
      ∃ K : IntrinsicFoliationLeaf A.F.stablePartition Q ≃ₜ
          IntrinsicFoliationLeaf A.F.stablePartition Q', ∀ z, (K z).val = z.val := by
    subst Q'
    exact ⟨Homeomorph.refl _, fun _ ↦ rfl⟩
  have hSLembed (x : E) : IsEmbedding (SL x) := by
    apply fibre_lift_embedding_of_product_charts (V := FoliationCoordinateDisk s) p Subtype.val Subtype.val_injective
      D (D x) (SL x) (hSLcont x) (hSLproj x) (hSLfibre x)
    intro y
    obtain ⟨j, hj, hpj, hi⟩ := hHstable y.val
    have hyr : y.val ∈ Set.range (SL x) := by rw [hSLfibre]; exact y.property
    obtain ⟨a, ha⟩ := hyr
    have hQ : Quotient.mk A.F.stablePartition (p y.val) =
        Quotient.mk A.F.stablePartition (p x) := by
      rw [← ha, hSLproj]
      exact a.property
    obtain ⟨K, hK⟩ := hStableCast _ _ hQ
    refine ⟨O y.val, W y.val, H y.val, K ∘ j, hxO y.val,
      K.continuous.comp hj.continuous, hHcoord y.val, ?_⟩
    intro r z hz
    exact (hpj r z (hz.trans y.property.symm)).trans (hK (j r)).symm
  have hlocalProducts (x : E) :
      ∃ (V : TopologicalSpace.Opens (IntrinsicFoliationLeaf A.F.stablePartition
            (Quotient.mk A.F.stablePartition (p x))))
        (W : TopologicalSpace.Opens ℂ) (O : TopologicalSpace.Opens E)
        (h : (V × W) ≃ₜ O),
        x ∈ O ∧ D x ∈ W ∧
        (∀ r z, D (h (r, z)).val = z.val) ∧
        (∀ r z, z.val = D x → p (h (r, z)).val = r.val.val) ∧
        (∃ (i : A.F.boxIndex) (w : FoliationCoordinateDisk 2),
          ∀ r : V, ∃ z : FoliationCoordinateDisk s,
            r.val.val = ((A.F.box i).chart (z, w)).val) := by
    obtain ⟨j, hj, hpj, i, w, hij⟩ := hHstable x
    let V : TopologicalSpace.Opens (IntrinsicFoliationLeaf A.F.stablePartition
        (Quotient.mk A.F.stablePartition (p x))) := ⟨Set.range j, hj.isOpen_range⟩
    let J : FoliationCoordinateDisk s ≃ₜ V := hj.isEmbedding.toHomeomorph
    let K := (Homeomorph.prodCongr J.symm (Homeomorph.refl (W x))).trans (H x)
    refine ⟨V, W x, O x, K, hxO x, hxW x, ?_, ?_, i, w, ?_⟩
    · intro r z
      exact hHcoord x (J.symm r) z
    · intro r z hz
      exact (hpj (J.symm r) z hz).trans
        (congrArg (fun a : V ↦ a.val.val) (J.apply_symm_apply r))
    · intro r
      exact ⟨J.symm r, (congrArg (fun a : V ↦ a.val.val) (J.apply_symm_apply r)).symm.trans
        (hij (J.symm r))⟩

  have hEuclidean : Nonempty (E ≃ₜ (Fin (2*d) → ℝ)) := by
    obtain ⟨r, hdim, ⟨K⟩⟩ := native_stable_leaf_euclidean_of_anosov f a hu A (p e0)
    let FHome : (IntrinsicFoliationLeaf A.F.stablePartition
        (Quotient.mk A.F.stablePartition (p e0))) ≃ₜ {e : E // D e = D e0} :=
      (hSLembed e0).toHomeomorph.trans (Homeomorph.setCongr (hSLfibre e0))
    let model : ((Fin (2*r) → ℝ) × ℂ) ≃L[ℝ] (Fin (2*d) → ℝ) :=
      (LinearEquiv.ofFinrankEq (R := ℝ) _ _ (by simp [Module.finrank_prod, hdim])).toContinuousLinearEquiv
    exact ⟨ProdH.symm.trans ((Homeomorph.prodCongr (FHome.symm.trans K)
      (Homeomorph.refl ℂ)).trans model.toHomeomorph)⟩

  have hreverse := reverse_lift_endpoint_g10 p e0 δ hendpoint
  refine ⟨charts, smooth, hlocal, D, D e0, δ, tau, hlocalProducts, hDsurj, htau,
    hreverse, htranslation, ?_, ⟨ProdH, hProdH⟩, ?_, ?_, hEuclidean, hcomm, htf⟩
  · intro x y
    rw [hSrel x y]
    change D x = D y ↔ y ∈ {z | Relation.EqvGen stableLinkB x z}
    rw [← hSLrange x, hSLfibre x]
    exact eq_comm
  · intro x
    refine ⟨SL x, hSLcont x, hSLinj x, hSLproj x, ?_, ?_, hSLembed x⟩
    · intro z hz
      have heq : z = ⟨p x, rfl⟩ := Subtype.ext hz
      simpa only [heq] using hSLpoint x
    · rw [hSLrange]
      ext y
      exact (hSrel x y).symm
  · intro x
    let := C.charts (Quotient.mk A.F.unstablePartition (p x))
    refine ⟨UL x, UC x, hULhol x, hULinj x, hULproj x, ?_, ?_, hUC x⟩
    · intro z hz
      have heq : z = A.F.uPoint (p x) := Subtype.ext hz
      simpa only [heq] using hULpoint x
    · rw [hULrange]
      ext y
      exact (hUrel x y).symm




end HolomorphicAnosov.Ghys
