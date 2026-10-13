import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.ManifoldInverse
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Geometry.ContinuousStableLeafLiftG9
import HolomorphicAnosov.Geometry.Manifold.OpenSubsetInclusionTangentG9
import HolomorphicAnosov.Geometry.HPSNativePlaqueFamilyData
import HolomorphicAnosov.Topology.CompactPlaqueImagePersistence

/-! # Open intrinsic lifts of immersed plaques (HPS) (Ghys, Proposition 4.1) -/ 

noncomputable section
open Set Manifold TopologicalSpace _root_.Topology
open scoped ContDiff Manifold _root_.Topology
namespace HolomorphicAnosov

/-- A continuous lift through a receiving immersion is a local diffeomorphism when both original tangent images coincide and the source differential is injective.    The immersion local form makes the lift smooth. (HPS) -/
theorem immersed_leaf_lift_local_diffeomorph
    {r s : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X L M : Type*} [TopologicalSpace X] [TopologicalSpace L] [TopologicalSpace M]
    [ChartedSpace (Fin r → ℝ) X] [ChartedSpace (Fin s → ℝ) L] [ChartedSpace V M]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    [IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ L] [IsManifold 𝓘(ℝ,V) ∞ M]
    (j : X → M) (k : L → M) (g : X → L)
    (hj : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ,V) ∞ j)
    (hk : ContMDiff 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ,V) ∞ k)
    (hji : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ,V) j x))
    (hki : ∀ y, IsImmersionAt 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ,V) ∞ k y)
    (hc : Continuous g) (he : k ∘ g = j)
    (hr : ∀ x, (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ,V) j x).range =
      (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ,V) k (g x)).range) :
    IsLocalDiffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) ∞ g ∧
      (Function.Injective j → IsOpenEmbedding g) := by
  have hs : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) ∞ g := by
    intro x
    apply (ContMDiffAt.iff_comp_isImmersionAt (hki (g x))).mpr
    exact ⟨hc.continuousAt, he ▸ hj.contMDiffAt⟩
  have hb (x : X) : Function.Bijective
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g x) := by
    have hd := mfderiv_comp x ((hk (g x)).mdifferentiableAt (by simp))
      ((hs x).mdifferentiableAt (by simp))
    rw [he] at hd
    have hi := (hki (g x)).mfderiv_injective (by simp)
    constructor
    · intro v w h
      apply hji x
      rw [hd]
      exact congrArg (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ,V) k (g x)) h
    · intro w
      have hm : (mfderiv 𝓘(ℝ, Fin s → ℝ) 𝓘(ℝ,V) k (g x)) w ∈
          (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ,V) j x).range := by
        rw [hr x]
        exact ⟨w,rfl⟩
      obtain ⟨v,hv⟩ := hm
      refine ⟨v,hi ?_⟩
      rw [hd] at hv
      exact hv
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) ∞ g := by
    intro x
    let a := (LinearEquiv.ofBijective
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g x).toLinearMap (hb x)).toContinuousLinearEquiv
    have ha : mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) g x = a.toContinuousLinearMap := by
      ext v
      rfl
    obtain ⟨q,hx,_,heq⟩ := W07ManifoldInverseFunction.exists_partialDiffeomorph
      isOpen_univ (Set.mem_univ x) hs.contMDiffOn a ha
    exact ⟨q,hx,heq⟩
  refine ⟨hlocal, fun hinj ↦ ?_⟩
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨hc, ?_, hlocal.isOpenMap⟩
  intro x y hxy
  apply hinj
  rw [← he]
  exact congrArg k hxy


attribute [local instance] complex_isManifold_real

/-- A smooth injective plaque tangent to the original stable distribution, whose points belong to one stable class of the supplied presentation, lifts to an intrinsically open smooth plaque in that presentation.    Countable plaques prove continuity before the receiving immersion is used for smoothness. -/
theorem stable_tangent_plaque_open_lift
    {d r : ℕ} {M X : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace X] [ChartedSpace (Fin r → ℝ) X]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ X]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : Ghys.AnosovIntrinsicFoliationPresentation f a)
    (j : X → M) (hj : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ j)
    (hinj : Function.Injective j)
    (hji : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j x))
    (hT : ∀ x, (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j x).range =
      a.splitting.stable.toDistribution (j x)) :
    letI := P.realCharts
    ∀ q : Quotient P.foliations.stablePartition,
      (∀ x, Quotient.mk P.foliations.stablePartition (j x) = q) →
      letI := P.foliations.stableTopology q
      letI := P.foliations.stableCharts q
      ∃ g : X → IntrinsicFoliationLeaf P.foliations.stablePartition q,
        (∀ x, (g x).val = j x) ∧ IsOpenEmbedding g ∧
        IsLocalDiffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞ g := by
  let := P.realCharts
  intro q hq
  let := P.foliations.stableTopology q
  let := P.foliations.stableCharts q
  let := P.stableSmooth q
  let := (P.stableNative q).countable
  let : LocallyConnectedSpace X :=
    ChartedSpace.locallyConnectedSpace (Fin r → ℝ) X
  let g : X → IntrinsicFoliationLeaf P.foliations.stablePartition q :=
    fun x ↦ ⟨j x,hq x⟩
  have hc : Continuous g := continuous_stable_leaf_lift_g9 P.foliations q
    inferInstance g hj.continuous
  let N := P.stableNative q
  have he : N.inclusion ∘ g = j := by
    rw [show N.inclusion = Subtype.val from P.stable_inclusion_eq q]
    rfl
  have hr (x : X) : (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j x).range =
      (mfderiv 𝓘(ℝ, Fin (2*d-2) → ℝ) (realModel d) N.inclusion (g x)).range := by
    rw [hT x,N.tangent]
    rw [show N.inclusion (g x) = j x from congrFun he x]
  obtain ⟨hl,ho⟩ := immersed_leaf_lift_local_diffeomorph j N.inclusion g
    hj N.immersion.contMDiff hji (fun y ↦ N.immersion.isImmersionAt y) hc he hr
  exact ⟨g,fun _ ↦ rfl,ho hinj,hl⟩


/-- An actual native embedded stable plaque has an intrinsically open lift in any supplied stable class containing its points.    The open source inclusion has bijective derivative, so restricting the actual plaque preserves both injectivity and the exact original tangent image. -/
theorem native_stable_plaque_open_lift
    {d r : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (P : Ghys.AnosovIntrinsicFoliationPresentation f a) {center : M}
    (F : NativeEmbeddedPlaque (realModel d) (V := Fin r → ℝ)
      a.splitting.stable.toDistribution center) :
    letI := P.realCharts
    ∀ q : Quotient P.foliations.stablePartition,
      (∀ v ∈ F.domain, Quotient.mk P.foliations.stablePartition (F.param v) = q) →
      letI := P.foliations.stableTopology q
      letI := P.foliations.stableCharts q
      let U : Opens (Fin r → ℝ) := ⟨F.domain,F.domain_open⟩
      ∃ g : U → IntrinsicFoliationLeaf P.foliations.stablePartition q,
        (∀ v, (g v).val = F.param v) ∧ IsOpenEmbedding g ∧
        IsLocalDiffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin (2*d-2) → ℝ) ∞ g := by
  let := P.realCharts
  intro q hq
  let := P.foliations.stableTopology q
  let := P.foliations.stableCharts q
  let U : Opens (Fin r → ℝ) := ⟨F.domain,F.domain_open⟩
  let j : U → M := fun v ↦ F.param v
  have hj : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ j := by
    intro v
    exact contMDiffAt_subtype_iff.mpr
      ((F.smooth v.val v.property).contMDiffAt (F.domain_open.mem_nhds v.property))
  have hd (v : U) : mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j v =
      (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) F.param v.val).comp
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) (Subtype.val : U → (Fin r → ℝ)) v) :=
    mfderiv_comp v
      (((F.smooth v.val v.property).contMDiffAt
        (F.domain_open.mem_nhds v.property)).mdifferentiableAt (by simp))
      (contMDiff_subtype_val.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
  have hji (v : U) : Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j v) := by
    rw [hd]
    exact (F.immersed v.val v.property).comp
      (openSubsetInclusion_mfderiv_bijective 𝓘(ℝ, Fin r → ℝ) U v).injective
  have hT (v : U) : (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j v).range =
      a.splitting.stable.toDistribution (j v) := by
    rw [hd, ← F.tangent v.val v.property]
    apply LinearMap.range_comp_of_range_eq_top
    exact LinearMap.range_eq_top.mpr
      (openSubsetInclusion_mfderiv_bijective 𝓘(ℝ, Fin r → ℝ) U v).surjective
  exact stable_tangent_plaque_open_lift f a P j hj F.embedded.injective hji hT q
    (fun v ↦ hq v.val v.property)


/-- An intrinsically open plaque contained in one receiving plaque has an open stable-coordinate map in that receiving box.    Factor its literal lift through the receiving plaque's open embedding and cancel that embedding. -/
theorem stable_plaque_coordinate_open_embedding
    {s t : ℕ} {M X : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    [TopologicalSpace X] (F : TransverseContinuousFoliations s t M)
    (b : F.boxIndex) (w : FoliationCoordinateDisk t) :
    let q := F.stableLabel b w
    letI := F.stableTopology q
    ∀ (g : X → IntrinsicFoliationLeaf F.stablePartition q), IsOpenEmbedding g →
      ∀ (hbox : ∀ x, (g x).val ∈ (F.box b).image),
      (∀ x, ((F.box b).chart.symm ⟨(g x).val,hbox x⟩).2 = w) →
      IsOpenEmbedding (fun x ↦ ((F.box b).chart.symm ⟨(g x).val,hbox x⟩).1) := by
  let q := F.stableLabel b w
  let := F.stableTopology q
  dsimp only
  intro g hg hbox hw
  let j : FoliationCoordinateDisk s → IntrinsicFoliationLeaf F.stablePartition q :=
    fun v ↦ ⟨((F.box b).chart (v,w)).val,F.stable_label b v w⟩
  have hj : IsOpenEmbedding j := F.stable_plaque b w
  let c : X → FoliationCoordinateDisk s :=
    fun x ↦ ((F.box b).chart.symm ⟨(g x).val,hbox x⟩).1
  have hcomp : j ∘ c = g := by
    funext x
    apply Subtype.ext
    change ((F.box b).chart (_,w)).val = (g x).val
    have hepair : (c x,w) = (F.box b).chart.symm ⟨(g x).val,hbox x⟩ :=
      Prod.ext rfl (hw x).symm
    exact (congrArg (fun p ↦ ((F.box b).chart p).val) hepair).trans
      (congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(g x).val,hbox x⟩))
  exact hj.of_comp c (hcomp ▸ hg)


/-- A continuous family of intrinsically open stable plaques, parametrized by an open part of a receiving unstable transversal, is an ambient open product embedding when it keeps that receiving transverse coordinate.    Pass to stable receiving coordinates and apply compact-core persistence to their open embeddings. -/
theorem stable_plaque_product_open_embedding
    {s t : ℕ} {M X : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s+t) → ℝ) M]
    [TopologicalSpace X] [LocallyCompactSpace X]
    (F : TransverseContinuousFoliations s t M) (b : F.boxIndex)
    (T : Opens (FoliationCoordinateDisk t)) (J : X × T → M) (hJ : Continuous J)
    (hbox : ∀ p, J p ∈ (F.box b).image)
    (hcoord : ∀ p, ((F.box b).chart.symm ⟨J p,hbox p⟩).2 = p.2.val)
    (hlift : ∀ t : T,
      letI := F.stableTopology (F.stableLabel b t.val)
      ∃ g : X → IntrinsicFoliationLeaf F.stablePartition (F.stableLabel b t.val),
        IsOpenEmbedding g ∧ ∀ x, (g x).val = J (x,t)) :
    IsOpenEmbedding J := by
  let c : X × T → FoliationCoordinateDisk s × FoliationCoordinateDisk t :=
    fun p ↦ (F.box b).chart.symm ⟨J p,hbox p⟩
  have hc : Continuous c := (F.box b).chart.symm.continuous.comp (hJ.subtype_mk _)
  have hfirst (t : T) : IsOpenEmbedding (fun x ↦ (c (x,t)).1) := by
    let := F.stableTopology (F.stableLabel b t.val)
    obtain ⟨g,hg,hval⟩ := hlift t
    have hgb (x : X) : (g x).val ∈ (F.box b).image := by rw [hval]; exact hbox (x,t)
    have hgw (x : X) : ((F.box b).chart.symm ⟨(g x).val,hgb x⟩).2 = t.val := by
      simpa only [hval] using hcoord (x,t)
    have ho := stable_plaque_coordinate_open_embedding F b t.val g hg hgb hgw
    simpa only [hval] using ho
  have hval : IsOpenEmbedding (Subtype.val : FoliationCoordinateDisk s → (Fin s → ℝ)) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  have htotal := continuous_family_open_embedding_prod (fun p : X × T ↦ (c p).1.val)
    (continuous_subtype_val.comp hc.fst) (fun t ↦ hval.comp (hfirst t))
  have hinc : IsOpenEmbedding
      (Prod.map (Subtype.val : FoliationCoordinateDisk s → (Fin s → ℝ)) (id : T → T)) :=
    hval.prodMap (Homeomorph.refl T).isOpenEmbedding
  have hpair : IsOpenEmbedding (fun p : X × T ↦ ((c p).1,p.2)) :=
    hinc.of_comp _ htotal
  have hincT : IsOpenEmbedding
      (Prod.map (id : FoliationCoordinateDisk s → FoliationCoordinateDisk s)
        (Subtype.val : T → FoliationCoordinateDisk t)) :=
    (Homeomorph.refl (FoliationCoordinateDisk s)).isOpenEmbedding.prodMap
      T.isOpen.isOpenEmbedding_subtypeVal
  have hout := (F.box b).isOpen_image.isOpenEmbedding_subtypeVal.comp
    ((F.box b).chart.isOpenEmbedding.comp (hincT.comp hpair))
  convert hout using 1
  funext p
  change J p = ((F.box b).chart ((c p).1,p.2.val)).val
  rw [← hcoord p]
  exact (congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨J p,hbox p⟩)).symm

end HolomorphicAnosov
