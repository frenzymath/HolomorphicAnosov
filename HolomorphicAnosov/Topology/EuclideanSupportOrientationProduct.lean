import HolomorphicAnosov.Topology.EuclideanLocalHomologyProductNonzero
import HolomorphicAnosov.Topology.EuclideanConstantFixedPointIndexOneTranslation
import HolomorphicAnosov.Topology.Homology.IntegralCompactSupportOrientation

/-!
# The common coefficient of local and supported Euclidean products

Source: Dold (1965), §§1.3 and 1.6 pp.1–2; Hatcher, Lemma 3.27 pp.236–238
and §3.B pp.277–278. DAG: `topo.euclidean_support_orientation_product_g17`.

Let c be the coefficient of the local product of the two specified positive
generators. Integer bilinearity and cyclicity show every local product is the
product of the two coordinates times c. The nonvanishing theorem shows c is
nonzero. For each point of the product fixed support, translate the two domain
coordinates to zero. Support-enlargement naturality and constant-displacement
normalization send each supported orientation to its positive local generator.
The translation square commutes with ordered product coordinates, so naturality
sends the supported product to c times the positive generator. Point-neighborhood
excision makes this translation injective on point-relative homology; Hatcher's
compact-support detection theorem therefore gives the supported product as c
times the product support orientation. Finally the displacement square commutes
as well. Applying the positive coordinate yields c I(f×g)=c I(f)I(g), and c≠0
allows cancellation in the integers. All steps hold in degree zero and for
empty fixed supports as well.
-/

noncomputable section

namespace HolomorphicAnosov.EuclideanIndexProduct
open CategoryTheory TopologicalSpace

set_option backward.isDefEq.respectTransparency false
def centerMap {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (x : U) : C(U,EuclideanSpace ℝ (Fin n)) :=
  ⟨fun y => y.val - x.val,continuous_subtype_val.sub continuous_const⟩

def localizationPairMap {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : U) (hx : x.val ∈ K) :
    euclideanSupportPair n (U : Set (EuclideanSpace ℝ (Fin n))) K ⟶ singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {0}ᶜ :=
  singularSubspacePairMap (TopCat.ofHom (centerMap U x))
    (Set.ofPred (fun u : U => u.val ∉ K)) {0}ᶜ (by
      intro u hu hz
      apply hu
      exact (sub_eq_zero.mp hz).symm ▸ hx)

def localizationHomologyMap {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : U) (hx : x.val ∈ K) :
    (euclideanSupportPair n (U : Set (EuclideanSpace ℝ (Fin n))) K).homology (C := ModuleCat.{0} ℤ)
      reducedSingularIntegralCoefficients n ⟶
    EuclideanLocalIntegralHomology n :=
  SSetPair.homologyMap (localizationPairMap U K x hx) reducedSingularIntegralCoefficients n

def pointRestrictionPairMap {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : U) (hx : x.val ∈ K) :
    euclideanSupportPair n (U : Set (EuclideanSpace ℝ (Fin n))) K ⟶ euclideanSupportPair n (U : Set (EuclideanSpace ℝ (Fin n))) {x.val} :=
  singularSubspacePairMap (𝟙 (TopCat.of U))
    (Set.ofPred (fun u : U => u.val ∉ K)) (Set.ofPred (fun u : U => u.val ∉ ({x.val} : Set _)))
    (by intro u hu he; exact hu ((Set.mem_singleton_iff.mp he).symm ▸ hx))

theorem localization_factor {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : U) (hx : x.val ∈ K) :
    pointRestrictionPairMap (n := n) U K x hx ≫ localizationPairMap (n := n) U {x.val} x rfl =
      localizationPairMap (n := n) U K x hx := by
  apply MorphismProperty.Arrow.Hom.ext <;>
    change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _ <;>
    rw [← Functor.map_comp] <;> rfl

theorem singleton_localization_injective {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (x : U) :
    Function.Injective (localizationHomologyMap (n := n) U {x.val} x rfl).hom := by
  let J := singularExcisionInclusion (TopCat.of (EuclideanSpace ℝ (Fin n))) ({x.val}ᶜ) (U : Set (EuclideanSpace ℝ (Fin n)))
  let e := Homeomorph.subRight x.val
  let T := singularSubspacePairMap (TopCat.ofHom ⟨e,e.continuous⟩)
    ({x.val}ᶜ) ({0}ᶜ) (by intro u hu hz; exact hu (sub_eq_zero.mp hz))
  have he : ∀ u : EuclideanSpace ℝ (Fin n), e u ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) ↔ u ∈ ({x.val}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    intro u
    exact not_congr sub_eq_zero
  have hT := (singular_subspace_homeomorph_homology_bijective
    (X := TopCat.of (EuclideanSpace ℝ (Fin n))) (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e _ _ he
    reducedSingularIntegralCoefficients n).1
  have hJ :=
    point_neighborhood_excision_isIso (TopCat.of (EuclideanSpace ℝ (Fin n))) x.val (U : Set (EuclideanSpace ℝ (Fin n)))
      (by rw [U.isOpen.interior_eq]; exact x.property)
      reducedSingularIntegralCoefficients n
  have hcomp : J ≫ T = localizationPairMap (n := n) U {x.val} x rfl := by
    apply MorphismProperty.Arrow.Hom.ext <;>
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _ <;>
      rw [← Functor.map_comp] <;> rfl
  let : IsIso (SSetPair.homologyMap J reducedSingularIntegralCoefficients n) := hJ
  unfold localizationHomologyMap
  rw [← hcomp,SSetPair.homologyMap_comp]
  change Function.Injective (fun a =>
    (SSetPair.homologyMap (C := ModuleCat.{0} ℤ) T reducedSingularIntegralCoefficients n).hom
      ((SSetPair.homologyMap (C := ModuleCat.{0} ℤ) J reducedSingularIntegralCoefficients n).hom a))
  exact hT.comp ((ModuleCat.mono_iff_injective
    (SSetPair.homologyMap (C := ModuleCat.{0} ℤ) J reducedSingularIntegralCoefficients n)).mp inferInstance)

theorem ambient_constant {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (x : U) :
    euclideanAmbientFixedSet (ContinuousMap.const U x.val) = {x.val} := by
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact hu.symm
  · intro hy
    exact ⟨x,rfl,hy.symm⟩

theorem localization_orientation {n : ℕ} (U : Opens (EuclideanSpace ℝ (Fin n))) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (EuclideanSpace ℝ (Fin n)))) (x : U) (hx : x.val ∈ K) :
    let o : (euclideanSupportPair n (U : Set (EuclideanSpace ℝ (Fin n))) K).homology (C := ModuleCat.{0} ℤ)
      reducedSingularIntegralCoefficients n :=
      euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) K U.isOpen hK hKU
    (localizationHomologyMap (n := n) U K x hx).hom o =
    euclideanPositiveLocalClass n := by
  dsimp only
  have hsingle : ∀ (L : Set (EuclideanSpace ℝ (Fin n))) (hL : IsCompact L) (hLU : L ⊆ (U : Set (EuclideanSpace ℝ (Fin n))))
      (hxL : x.val ∈ L), L = euclideanAmbientFixedSet (ContinuousMap.const U x.val) →
      let o : (euclideanSupportPair n (U : Set (EuclideanSpace ℝ (Fin n))) L).homology (C := ModuleCat.{0} ℤ)
        reducedSingularIntegralCoefficients n :=
        euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) L U.isOpen hL hLU
      (localizationHomologyMap (n := n) U L x hxL).hom o =
      euclideanPositiveLocalClass n := by
    intro L hL hLU hxL heq
    subst L
    exact euclidean_constant_displacement_positive_class x.val x.property
  have hnorm := hsingle {x.val} isCompact_singleton
    (Set.singleton_subset_iff.mpr x.property) rfl (ambient_constant U x).symm
  unfold localizationHomologyMap
  rw [← localization_factor U K x hx,SSetPair.homologyMap_comp]
  change (SSetPair.homologyMap (C := ModuleCat.{0} ℤ) (localizationPairMap (n := n) U {x.val} x rfl)
    reducedSingularIntegralCoefficients n).hom
    ((SSetPair.homologyMap (C := ModuleCat.{0} ℤ) (pointRestrictionPairMap (n := n) U K x hx)
      reducedSingularIntegralCoefficients n).hom _) = _
  rw [show (SSetPair.homologyMap (C := ModuleCat.{0} ℤ) (pointRestrictionPairMap (n := n) U K x hx)
      reducedSingularIntegralCoefficients n).hom
      (euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) K U.isOpen hK hKU) =
    euclideanSupportOrientation n (U : Set (EuclideanSpace ℝ (Fin n))) {x.val} U.isOpen isCompact_singleton
      ((Set.singleton_subset_iff.mpr hx).trans hKU) from
    euclideanSupportOrientation_enlargement n (U : Set (EuclideanSpace ℝ (Fin n))) {x.val} K U.isOpen
      isCompact_singleton hK (Set.singleton_subset_iff.mpr hx) hKU]
  exact hnorm

theorem localizations_detect {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (f : C(U,EuclideanSpace ℝ (Fin n))) (hF : IsCompact (euclideanFixedSet f))
    (a : (euclideanSupportPair n (U : Set (EuclideanSpace ℝ (Fin n))) (euclideanAmbientFixedSet f)).homology
      (C := ModuleCat.{0} ℤ) reducedSingularIntegralCoefficients n)
    (ha : ∀ (x : U) (hx : x ∈ euclideanFixedSet f),
      (SSetPair.homologyMap (C := ModuleCat.{0} ℤ) (localizationPairMap (n := n) U (euclideanAmbientFixedSet f) x
        ((mem_ambientFixedSet f x).mpr hx)) reducedSingularIntegralCoefficients n).hom a = 0) :
    a = 0 := by
  let K : Set U := Subtype.val ⁻¹' euclideanAmbientFixedSet f
  have hKnative : K = euclideanFixedSet f := by
    ext x
    exact mem_ambientFixedSet f x
  have hcharts : ∀ x : U, ∃ e : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin n)), x ∈ e.source := by
    intro x
    exact ⟨U.openPartialHomeomorphSubtypeCoe ⟨x⟩,Set.mem_univ x⟩
  have hd := (hatcher_integral_compact_support_orientation n U hcharts K
    (hKnative.symm ▸ hF)).2.1
  apply hd
  intro x hx
  have hs : ({x} : Set U) = Subtype.val ⁻¹' ({x.val} : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    simp only [Set.mem_singleton_iff,Set.mem_preimage,Subtype.ext_iff]
  let rr (B : Set U) (hB : B ⊆ K) :
      singularSubspacePair (TopCat.of U) Kᶜ ⟶ singularSubspacePair (TopCat.of U) Bᶜ :=
    SSetPair.homMk
      (TopCat.toSSet.map (TopCat.ofHom
        ⟨fun z : ↥(Kᶜ) => (⟨z.val,fun hz => z.property (hB hz)⟩ : ↥(Bᶜ)),
          continuous_subtype_val.subtype_mk _⟩)) (𝟙 _) (by rfl)
  suffices hall : ∀ (B : Set U) (hB : B ⊆ K),
      B = Subtype.val ⁻¹' ({x.val} : Set (EuclideanSpace ℝ (Fin n))) →
      (SSetPair.homologyMap (C := ModuleCat.{0} ℤ) (rr B hB) reducedSingularIntegralCoefficients n).hom a = 0 by
    exact hall {x} (Set.singleton_subset_iff.mpr hx) hs
  intro B hB heB
  subst B
  have hrr : rr (Subtype.val ⁻¹' ({x.val} : Set (EuclideanSpace ℝ (Fin n)))) hB =
      pointRestrictionPairMap (n := n) U (euclideanAmbientFixedSet f) x hx := by
    apply MorphismProperty.Arrow.Hom.ext
    · rfl
    · exact (TopCat.toSSet.map_id _).symm
  rw [hrr]
  apply singleton_localization_injective U x
  rw [map_zero]
  change (SSetPair.homologyMap (C := ModuleCat.{0} ℤ) (pointRestrictionPairMap (n := n) U (euclideanAmbientFixedSet f) x hx)
    reducedSingularIntegralCoefficients n ≫
    SSetPair.homologyMap (C := ModuleCat.{0} ℤ) (localizationPairMap (n := n) U {x.val} x rfl)
      reducedSingularIntegralCoefficients n).hom a = 0
  rw [← SSetPair.homologyMap_comp,localization_factor]
  exact ha x (hKnative ▸ hx)

theorem localization_product {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) (z : domain U V)
    (hz : z ∈ euclideanFixedSet (map f g))
    (a : (euclideanSupportPair n (U : Set (E n)) (euclideanAmbientFixedSet f)).homology
      (C := ModuleCat.{0} ℤ) reducedSingularIntegralCoefficients n)
    (b : (euclideanSupportPair m (V : Set (E m)) (euclideanAmbientFixedSet g)).homology
      (C := ModuleCat.{0} ℤ) reducedSingularIntegralCoefficients m) :
    let x := (domainEquiv U V z).1
    let y := (domainEquiv U V z).2
    let hx := (mem_ambientFixedSet f x).mpr ((fixedSet_iff f g z).mp hz).1
    let hy := (mem_ambientFixedSet g y).mpr ((fixedSet_iff f g z).mp hz).2
    let c := supportProduct f g a b
    (localizationHomologyMap (n := n+m) (domain U V)
      (euclideanAmbientFixedSet (map f g)) z ((mem_ambientFixedSet (map f g) z).mpr hz)).hom c =
    localProduct n m ((localizationHomologyMap U (euclideanAmbientFixedSet f) x hx).hom a)
      ((localizationHomologyMap V (euclideanAmbientFixedSet g) y hy).hom b) := by
  let x := (domainEquiv U V z).1
  let y := (domainEquiv U V z).2
  have hx := (mem_ambientFixedSet f x).mpr ((fixedSet_iff f g z).mp hz).1
  have hy := (mem_ambientFixedSet g y).mpr ((fixedSet_iff f g z).mp hz).2
  have hf : Set.MapsTo (TopCat.ofHom (centerMap U x)) (complement f)
      ({0} : Set (E n))ᶜ := by
    intro u hu heq
    exact hu ((sub_eq_zero.mp heq).symm ▸ hx)
  have hg : Set.MapsTo (TopCat.ofHom (centerMap V y)) (complement g)
      ({0} : Set (E m))ᶜ := by
    intro u hu heq
    exact hu ((sub_eq_zero.mp heq).symm ▸ hy)
  let H := singularSubspacePairMap
    (Topology.productMap (TopCat.ofHom (centerMap U x)) (TopCat.ofHom (centerMap V y)))
    (Topology.ProductSubspace (complement f) (complement g))
    (Topology.ProductSubspace ({0} : Set (E n))ᶜ ({0} : Set (E m))ᶜ)
    (Topology.relativeProductSubspace_map _ _ _ _ _ _ hf hg)
  have hcenter (u : U × V) :
      centerMap (domain U V) z ((domainEquiv U V).symm u) =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm (centerMap U x u.1,centerMap V y u.2) := by
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    apply e.injective
    change e (e.symm (u.1.val,u.2.val) - z.val) = e (e.symm _)
    rw [map_sub,e.apply_symm_apply,e.apply_symm_apply]
    rfl
  have hsquare : supportPairMap f g ≫
      localizationPairMap (domain U V) (euclideanAmbientFixedSet (map f g)) z
        ((mem_ambientFixedSet (map f g) z).mpr hz) = H ≫ coordinatePairMap n m := by
    apply MorphismProperty.Arrow.Hom.ext
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp,← Functor.map_comp]
      apply congrArg (fun h => TopCat.toSSet.map h)
      ext u : 1
      apply Subtype.ext
      exact hcenter u.val
    · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
      rw [← Functor.map_comp,← Functor.map_comp]
      apply congrArg (fun h => TopCat.toSSet.map h)
      ext u : 1
      exact hcenter u
  have hhom := congrArg (fun h => SSetPair.homologyMap (C := ModuleCat.{0} ℤ) h
    reducedSingularIntegralCoefficients (n+m)) hsquare
  simp only [SSetPair.homologyMap_comp] at hhom
  change (SSetPair.homologyMap (supportPairMap f g) reducedSingularIntegralCoefficients (n+m) ≫
    SSetPair.homologyMap (localizationPairMap (domain U V) (euclideanAmbientFixedSet (map f g)) z
      ((mem_ambientFixedSet (map f g) z).mpr hz)) reducedSingularIntegralCoefficients (n+m))
    (cross (TopCat.of U) (TopCat.of V) (complement f) (complement g) n m a b) = _
  rw [hhom]
  have hn := Topology.integralRelativeHomologyProduct_naturality_of_representatives
    cross (Classical.choose_spec Topology.integral_relative_cross_product_homology_map_boundary_descent)
    (TopCat.of U) (TopCat.of V) (TopCat.of (E n)) (TopCat.of (E m))
    (TopCat.ofHom (centerMap U x)) (TopCat.ofHom (centerMap V y))
    (complement f) (complement g) ({0}ᶜ) ({0}ᶜ) hf hg n m a b
  exact congrArg (fun c => SSetPair.homologyMap (coordinatePairMap n m)
    reducedSingularIntegralCoefficients (n+m) c) hn

end HolomorphicAnosov.EuclideanIndexProduct

namespace HolomorphicAnosov.EuclideanIndexProduct
open CategoryTheory TopologicalSpace

/-- A bilinear map between cyclic local groups is determined by its value on generators. -/
theorem bilinear_generators {n m : ℕ}
    (P : EuclideanLocalIntegralHomology n →ₗ[ℤ]
      EuclideanLocalIntegralHomology m →ₗ[ℤ] EuclideanLocalIntegralHomology (n+m))
    (a : EuclideanLocalIntegralHomology n) (b : EuclideanLocalIntegralHomology m) :
    P a b = (euclideanPositiveLocalCoordinate n a * euclideanPositiveLocalCoordinate m b) •
      P (euclideanPositiveLocalClass n) (euclideanPositiveLocalClass m) := by
  have ha := (euclideanPositiveLocalCoordinate_characterization n).2.1 a
  have hb := (euclideanPositiveLocalCoordinate_characterization m).2.1 b
  let ev : (EuclideanLocalIntegralHomology m →ₗ[ℤ]
      EuclideanLocalIntegralHomology (n+m)) →+ EuclideanLocalIntegralHomology (n+m) :=
    { toFun := fun q => q b
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  calc
    P a b = P (euclideanPositiveLocalCoordinate n a • euclideanPositiveLocalClass n) b :=
      congrArg (fun x => P x b) ha.symm
    _ = euclideanPositiveLocalCoordinate n a • P (euclideanPositiveLocalClass n) b :=
      map_zsmul (ev.comp P.toAddMonoidHom) _ _
    _ = euclideanPositiveLocalCoordinate n a •
        P (euclideanPositiveLocalClass n)
          (euclideanPositiveLocalCoordinate m b • euclideanPositiveLocalClass m) := by rw [hb]
    _ = _ := by rw [map_zsmul,smul_smul]

def productCoefficient (n m : ℕ) : ℤ := euclideanPositiveLocalCoordinate (n+m)
  (localProduct n m (euclideanPositiveLocalClass n) (euclideanPositiveLocalClass m))

theorem productCoefficient_class (n m : ℕ) :
    productCoefficient n m • euclideanPositiveLocalClass (n+m) =
      localProduct n m (euclideanPositiveLocalClass n) (euclideanPositiveLocalClass m) :=
  (euclideanPositiveLocalCoordinate_characterization (n+m)).2.1 _

theorem productCoefficient_nonzero (n m : ℕ) : productCoefficient n m ≠ 0 := by
  intro hzero
  have hclass := productCoefficient_class n m
  rw [hzero,zero_smul] at hclass
  obtain ⟨a,b,hab⟩ := localProduct_exists_nonzero n m
  apply hab
  rw [bilinear_generators,hclass.symm]
  exact zsmul_zero _

theorem localization_fixedOrientation {n : ℕ} {U : Opens (E n)}
    (f : C(U,E n)) (hF : IsCompact (euclideanFixedSet f))
    (x : U) (hx : x ∈ euclideanFixedSet f) :
    let o := fixedOrientation f hF
    (localizationHomologyMap U (euclideanAmbientFixedSet f) x
      ((mem_ambientFixedSet f x).mpr hx)).hom o = euclideanPositiveLocalClass n :=
  localization_orientation U (euclideanAmbientFixedSet f) (hF.image continuous_subtype_val)
    (by rintro y ⟨u,hu,rfl⟩; exact u.property) x ((mem_ambientFixedSet f x).mpr hx)

/-- The same nonzero integer coefficient appears in the supported and local products. -/
theorem supportProduct_orientation {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m))
    (hF : IsCompact (euclideanFixedSet f)) (hG : IsCompact (euclideanFixedSet g))
    (hP : IsCompact (euclideanFixedSet (map f g))) :
    supportProduct f g (fixedOrientation f hF) (fixedOrientation g hG) =
      productCoefficient n m • fixedOrientation (map f g) hP := by
  apply sub_eq_zero.mp
  apply localizations_detect (map f g) hP
  intro z hz
  change (localizationHomologyMap (domain U V) (euclideanAmbientFixedSet (map f g)) z
    ((mem_ambientFixedSet (map f g) z).mpr hz)).hom
    (supportProduct f g (fixedOrientation f hF) (fixedOrientation g hG) -
      productCoefficient n m • fixedOrientation (map f g) hP) = 0
  rw [map_sub,map_zsmul]
  have hprod := localization_product f g z hz (fixedOrientation f hF) (fixedOrientation g hG)
  dsimp only at hprod
  rw [hprod,localization_fixedOrientation f hF _ ((fixedSet_iff f g z).mp hz).1,
    localization_fixedOrientation g hG _ ((fixedSet_iff f g z).mp hz).2,
    localization_fixedOrientation (map f g) hP z hz,productCoefficient_class,sub_self]

/-- Dold's multiplicativity, with the common product-orientation coefficient cancelled. -/
theorem index_mul {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m))
    (hF : IsCompact (euclideanFixedSet f)) (hG : IsCompact (euclideanFixedSet g))
    (hP : IsCompact (euclideanFixedSet (map f g))) :
    euclideanFixedPointIndex (map f g) hP = euclideanFixedPointIndex f hF *
      euclideanFixedPointIndex g hG := by
  have hprod := displacement_product f g (fixedOrientation f hF) (fixedOrientation g hG)
  dsimp only at hprod
  rw [supportProduct_orientation f g hF hG hP,map_zsmul] at hprod
  have hcoord := congrArg (euclideanPositiveLocalCoordinate (n+m)) hprod
  rw [map_zsmul,bilinear_generators,map_zsmul] at hcoord
  change productCoefficient n m * euclideanFixedPointIndex (map f g) hP =
    (euclideanFixedPointIndex f hF * euclideanFixedPointIndex g hG) * productCoefficient n m at hcoord
  rw [mul_comm _ (productCoefficient n m)] at hcoord
  exact mul_left_cancel₀ (productCoefficient_nonzero n m) hcoord

end HolomorphicAnosov.EuclideanIndexProduct

