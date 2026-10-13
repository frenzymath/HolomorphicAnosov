import HolomorphicAnosov.Topology.Homology.CompactSupportUnionGluing
import HolomorphicAnosov.Topology.Homology.CompactSupportClassOfLocalCompatibility
import HolomorphicAnosov.Topology.Homology.FiniteCompactChartCover
import HolomorphicAnosov.Topology.Homology.FiniteCompactConvexUnionInduction
import HolomorphicAnosov.Topology.Homology.SupportHomeomorphism
import HolomorphicAnosov.Topology.Homology.ConvexCompatibleSupportClass
import HolomorphicAnosov.Topology.Homology.EuclideanCompactConvexHomologyProfile
import HolomorphicAnosov.Topology.Homology.EuclideanLocalHomologyProfile
import HolomorphicAnosov.Topology.Homology.RelativeCycleRepresentative
import HolomorphicAnosov.Topology.Homology.RelativeCycleLift
import HolomorphicAnosov.Topology.Homology.CompactSupportBallHomologyLift
import HolomorphicAnosov.Topology.Homology.IntegralCompactSupportOrientationPositiveChart
import HolomorphicAnosov.Topology.Homology.SingularChainSupportFactorization
import HolomorphicAnosov.Topology.Homology.ConvexSupportRestrictionIso
import HolomorphicAnosov.Topology.Homology.RelativeHomologyMapIso
import HolomorphicAnosov.Topology.Homology.ConvexComplementPunctureEquiv
import HolomorphicAnosov.Topology.Homology.CompactSupportBallEnlargement
import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology
import HolomorphicAnosov.Topology.Homology.SingularChainCompactSupport
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.SingularHomologyExcision
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Compactness.Compact

/-!
Integral local homology sections supported on compact subsets. (Hatcher, Lemma 3.27)
-/

noncomputable section

namespace HolomorphicAnosov

open CategoryTheory

universe u

namespace IntegralCompactSupportOrientation

open CategoryTheory.Limits HolomorphicAnosov.Topology _root_.Topology

/-- The native excision API supplies the local relative homology isomorphism used in Hatcher's convex-chart step whenever the two interiors cover. -/
private theorem convex_chart_excision_homology_isIso
    (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ)
    (R : ModuleCat.{u} ℤ) (q : ℕ) :
    IsIso (SSetPair.homologyMap (singularExcisionInclusion X A B) R q) := by
  have h := singular_homology_excision_barycentric_subdivision.2.1 X A B hcover R
  exact h.2.2 q

/-- A neighborhood whose closure contains the support gives the interiors cover required by the native excision theorem. -/
private theorem support_neighborhood_excision_cover
    (X : TopCat.{u}) (K U : Set X) (hU : IsOpen U)
    (hKU : closure K ⊆ U) : interior Kᶜ ∪ interior U = Set.univ := by
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_univ x
  · intro x _
    by_cases hx : x ∈ closure K
    · exact Set.mem_union_right _ ((subset_interior_iff_isOpen.mpr hU) (hKU hx))
    · exact Set.mem_union_left _ (by
        rw [interior_compl]
        exact hx)

/-- Excision isomorphism for a support pair and a neighborhood with closure inside that neighborhood. -/
private theorem support_neighborhood_excision_homology_isIso
    (X : TopCat.{u}) (K U : Set X) (hU : IsOpen U)
    (hKU : closure K ⊆ U) (R : ModuleCat.{u} ℤ) (q : ℕ) :
    IsIso (SSetPair.homologyMap
      (singularExcisionInclusion X Kᶜ U) R q) := by
  apply convex_chart_excision_homology_isIso X Kᶜ U
  exact support_neighborhood_excision_cover X K U hU hKU

/-- Hatcher Lemma 3.27, empty-support case: the inclusion of the whole space is an isomorphism, so every degree of its relative cokernel is zero. (Hatcher, Lemma 3.27) -/
private theorem support_empty_subsingleton (X : TopCat.{u})
    (R : ModuleCat.{u} ℤ) (q : ℕ) :
    Subsingleton (supportSingularHomology X ∅ R q : Type u) := by
  let i : TopCat.of ↥((∅ : Set X)ᶜ) ⟶ X :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsIso i := TopCat.isIso_of_bijective_of_isOpenMap i
    ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, by simp⟩, rfl⟩⟩
    (by
      change IsOpenMap (Subtype.val : ↥((∅ : Set X)ᶜ) → X)
      exact (by simp : IsOpen ((∅ : Set X)ᶜ)).isOpenMap_subtype_val)
  have hi' : IsIso (TopCat.toSSet.map i) := inferInstance
  have : IsIso (supportSingularPair X ∅).hom := hi'
  have : IsIso (SSet.chainComplexMap (supportSingularPair X ∅).hom R) := inferInstance
  have hz : IsZero (((supportSingularPair X ∅).chainComplex R).X q) := by
    exact CokernelCofork.IsColimit.isZero_of_epi
      ((supportSingularPair X ∅).isColimitCokernelCoforkChainComplexX R q)
  exact ModuleCat.subsingleton_of_isZero
    (ShortComplex.isZero_homology_of_isZero_X₂ _ hz)

/-- Vanishing of the next intersection homology makes the signed union restriction injective. (Hatcher, Lemma 3.27) -/
private theorem union_restriction_injective (D : CompactSupportMVData.{u}) (q : ℕ)
    (hnext : Subsingleton
      (supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (q + 1) : Type u)) :
    Function.Injective
      (supportMayerVietorisPhi D.space D.coefficients D.left D.right q) := by
  obtain ⟨δ, hδ, _⟩ := hatcher_compact_support_mayer_vietoris
  have he := (hδ D).1 q |>.1
  have hz : δ D q = 0 := by
    ext x
    have hx := hnext.elim x 0
    rw [hx, map_zero]
    rfl
  rw [hz] at he
  intro x y hxy
  have hker : supportMayerVietorisPhi D.space D.coefficients D.left D.right q (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := he (x - y) |>.mp hker
  exact sub_eq_zero.mp (by simpa using hz.symm)

/-- A union class restricting to zero on both supports is zero whenever the next intersection group vanishes. (Hatcher, Lemma 3.27) -/
private theorem union_zero_of_restrictions (D : CompactSupportMVData.{u}) (q : ℕ)
    (hnext : Subsingleton
      (supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (q + 1) : Type u))
    (c : supportSingularHomology D.space (D.left ∪ D.right) D.coefficients q)
    (hleft : supportSingularHomologyRestrict D.space D.coefficients
      Set.subset_union_left q c = 0)
    (hright : supportSingularHomologyRestrict D.space D.coefficients
      Set.subset_union_right q c = 0) : c = 0 := by
  apply union_restriction_injective D q hnext
  change (supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_left q c,
    -supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_right q c) = _
  rw [hleft, hright]
  simp

/-- Vanishing on both pieces and one degree higher on the intersection forces vanishing on their union. (Hatcher, Lemma 3.27) -/
private theorem union_homology_subsingleton (D : CompactSupportMVData.{u}) (q : ℕ)
    (hleft : Subsingleton
      (supportSingularHomology D.space D.left D.coefficients q : Type u))
    (hright : Subsingleton
      (supportSingularHomology D.space D.right D.coefficients q : Type u))
    (hnext : Subsingleton
      (supportSingularHomology D.space (D.left ∩ D.right) D.coefficients (q + 1) : Type u)) :
    Subsingleton
      (supportSingularHomology D.space (D.left ∪ D.right) D.coefficients q : Type u) := by
  refine ⟨fun x y ↦ ?_⟩
  apply union_restriction_injective D q hnext
  apply Prod.ext
  · exact hleft.elim _ _
  · exact congrArg Neg.neg (hright.elim _ _)


private theorem union_above_dimension_subsingleton
    (D : CompactSupportMVData.{u}) (n : ℕ)
    (hleft : ∀ i : ℕ, n < i →
      Subsingleton
        (supportSingularHomology D.space D.left D.coefficients i : Type u))
    (hright : ∀ i : ℕ, n < i →
      Subsingleton
        (supportSingularHomology D.space D.right D.coefficients i : Type u))
    (hinter : ∀ i : ℕ, n < i →
      Subsingleton
        (supportSingularHomology D.space (D.left ∩ D.right)
          D.coefficients i : Type u)) :
    ∀ i : ℕ, n < i →
      Subsingleton
        (supportSingularHomology D.space (D.left ∪ D.right)
          D.coefficients i : Type u) := by
  intro i hi
  apply union_homology_subsingleton D i (hleft i hi) (hright i hi)
  exact hinter (i + 1) (lt_trans hi (Nat.lt_succ_self i))

/-- In dimension zero, every local chart source is a singleton, so the topology is discrete. (Hatcher, Lemma 3.27) -/
private theorem discrete_of_zero_dimensional_charts (M : Type u) [TopologicalSpace M]
    (hM : ∀ x : M, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 0)),
      x ∈ e.source) : DiscreteTopology M := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  obtain ⟨e, hx⟩ := hM x
  have hs : e.source = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      apply Set.mem_singleton_iff.mpr
      apply e.injOn hy hx
      exact Subsingleton.elim _ _
    · exact Set.singleton_subset_iff.mpr hx
  rw [← hs]
  exact e.open_source

/-- In dimension zero, every compact support is finite. (Hatcher, Lemma 3.27) -/
private theorem finite_support_of_zero_dimensional_charts (M : Type u)
    [TopologicalSpace M]
    (hM : ∀ x : M, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 0)),
      x ∈ e.source) (K : Set M) (hK : IsCompact K) : K.Finite := by
  have : DiscreteTopology M := discrete_of_zero_dimensional_charts M hM
  exact hK.finite_of_discrete


private theorem support_subsingleton_of_totally_disconnected (X : TopCat.{u})
    [TotallyDisconnectedSpace X] (K : Set X)
    (R : ModuleCat.{u} ℤ) (q : ℕ) (hq : 0 < q) :
    Subsingleton (supportSingularHomology X K R (q + 1) : Type u) := by
  let P := supportSingularPair X K
  have hX : CategoryTheory.Limits.IsZero
      (((TopCat.toSSet.obj X).chainComplex R).homology (q + 1)) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} ℤ) (q + 1) R X (by omega)
  have hXq : CategoryTheory.Limits.IsZero
      (((TopCat.toSSet.obj X).chainComplex R).homology q) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} ℤ) q R X (Nat.ne_of_gt hq)
  let Xc : TopCat.{u} := TopCat.of (Kᶜ : Set X)
  have hXc : CategoryTheory.Limits.IsZero
      (((TopCat.toSSet.obj Xc).chainComplex R).homology q) :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} ℤ) q R Xc (Nat.ne_of_gt hq)
  have hz : CategoryTheory.Limits.IsZero
      (P.homology R (q + 1)) := hXc.of_iso
    ((P.shortExact_chainComplexShortComplex R).δIso (q + 1) q rfl hX hXq)
  exact ModuleCat.subsingleton_of_isZero hz

/-- In degree zero, the relative degree-one edge is controlled by injectivity of the complement-to-ambient H₀ map. -/
private theorem support_degree_one_subsingleton_of_h0_mono
    (X : TopCat.{u}) (K : Set X) (R : ModuleCat.{u} ℤ)
    (hX1 : CategoryTheory.Limits.IsZero
      (((TopCat.toSSet.obj X).chainComplex R).homology 1))
    (hmono : CategoryTheory.Mono
      (SSet.homologyMap (supportSingularPair X K).hom
        R 0)) :
    Subsingleton (supportSingularHomology X K R 1 : Type u) := by
  let P := supportSingularPair X K
  let δ := P.homologyδ R 1 0
  let g := SSet.homologyMap P.hom R 0
  have hg : Function.Injective g.hom := (ModuleCat.mono_iff_injective g).mp hmono
  have hδinj : Function.Injective δ.hom := by
    intro x y hxy
    have hz : δ.hom (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    let S₃ := ShortComplex.mk _ _ (P.comp_homologyδ R 1 0)
    obtain ⟨z, hz'⟩ :=
      (ShortComplex.moduleCat_exact_iff S₃).mp
        (P.homology_exact₃ R 1 0) (x - y) hz
    have hπzero : P.homologyπ R 1 = 0 := hX1.eq_zero_of_src _
    change P.homologyπ R 1 z = x - y at hz'
    rw [hπzero] at hz'
    exact sub_eq_zero.mp (by simpa using hz'.symm)
  refine ⟨fun x y ↦ ?_⟩
  have hxzero : x = 0 := by
    have hδzero : δ.hom x = 0 := by
      apply hg
      have hc := congrArg (fun k ↦ k.hom x) (P.homologyδ_comp R 1 0)
      change g.hom (δ.hom x) = 0 at hc
      simpa only [map_zero] using hc
    exact hδinj (by simpa using hδzero)
  have hyzero : y = 0 := by
    have hδzero : δ.hom y = 0 := by
      apply hg
      have hc := congrArg (fun k ↦ k.hom y) (P.homologyδ_comp R 1 0)
      change g.hom (δ.hom y) = 0 at hc
      simpa only [map_zero] using hc
    exact hδinj (by simpa using hδzero)
  exact hxzero.trans hyzero.symm

/-- A nonempty subspace of a discrete space is a retract: send every outside point to one chosen subspace point. (Hatcher, Lemma 3.27) -/
theorem discrete_subspace_homology_injective
    {R₀ : Type*} [Ring R₀]
    (X : TopCat.{u}) [DiscreteTopology X] (A : Set X) (hA : A.Nonempty)
    (R : ModuleCat.{u} R₀) (n : ℕ) :
    Function.Injective (SSet.homologyMap
      (TopCat.toSSet.map (TopCat.ofHom
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X)))) R n) := by
  classical
  let i : TopCat.of A ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let r : X ⟶ TopCat.of A := TopCat.ofHom
    ⟨fun x ↦ if hx : x ∈ A then ⟨x, hx⟩ else ⟨hA.choose, hA.choose_spec⟩,
      continuous_of_discreteTopology⟩
  have hir : i ≫ r = 𝟙 _ := by
    ext x
    simp [i, r, x.property]
  have hcomp : SSet.homologyMap (TopCat.toSSet.map i) R n ≫
      SSet.homologyMap (TopCat.toSSet.map r) R n = 𝟙 _ := by
    rw [← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp, hir,
      TopCat.toSSet.map_id, SSet.homologyMap_id]
  intro a b hab
  have ha := congrArg (fun f ↦ f a) hcomp
  have hb := congrArg (fun f ↦ f b) hcomp
  change SSet.homologyMap (TopCat.toSSet.map r) R n
    (SSet.homologyMap (TopCat.toSSet.map i) R n a) = a at ha
  change SSet.homologyMap (TopCat.toSSet.map r) R n
    (SSet.homologyMap (TopCat.toSSet.map i) R n b) = b at hb
  exact ha.symm.trans ((congrArg (SSet.homologyMap (TopCat.toSSet.map r) R n) hab).trans hb)


/-- An empty space has no singular simplices, so every chain module and every ordinary singular homology module is zero, including degree zero. -/
private theorem singular_homology_isZero_of_isEmpty (X : TopCat.{u}) [IsEmpty X]
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    IsZero (((TopCat.toSSet.obj X).chainComplex R).homology n) := by
  have hz : IsZero (((TopCat.toSSet.obj X).chainComplex R).X n) := by
    rw [IsZero.iff_id_eq_zero]
    apply SSet.chainComplex_hom_ext
    intro s
    exact isEmptyElim ((TopCat.toSSetObjEquiv X _) s (Classical.arbitrary _))
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hz

/-- The empty-complement case of H₀ injectivity follows from its zero source; the nonempty case follows from the discrete subspace retraction. -/
private theorem discrete_support_h0_mono (X : TopCat.{u}) [DiscreteTopology X]
    (K : Set X) (R : ModuleCat.{u} ℤ) :
    Mono (SSet.homologyMap (supportSingularPair X K).hom R 0) := by
  classical
  apply (ModuleCat.mono_iff_injective _).mpr
  by_cases h : (Kᶜ).Nonempty
  · exact discrete_subspace_homology_injective (R₀ := ℤ) X Kᶜ h R 0
  · have : IsEmpty (Kᶜ : Set X) := ⟨fun x ↦ h ⟨x.val, x.property⟩⟩
    have hs := ModuleCat.subsingleton_of_isZero
      (singular_homology_isZero_of_isEmpty (TopCat.of (Kᶜ : Set X)) R 0)
    intro x y hxy
    exact hs.elim x y

/-- Every positive relative singular homology group of a discrete space vanishes, including degree one and the empty-complement case. -/
private theorem support_positive_subsingleton_of_discrete (X : TopCat.{u})
    [DiscreteTopology X] (K : Set X) (R : ModuleCat.{u} ℤ) (n : ℕ) (hn : 0 < n) :
    Subsingleton (supportSingularHomology X K R n : Type u) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  by_cases hq : q = 0
  · subst q
    exact support_degree_one_subsingleton_of_h0_mono X K R
      (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat.{u} ℤ) 1 R X (by decide))
      (discrete_support_h0_mono X K R)
  · exact support_subsingleton_of_totally_disconnected X K R q (Nat.pos_of_ne_zero hq)

/-- Zero-dimensional charts give the above-dimension vanishing conclusion of Hatcher Lemma 3.27 for every support, without a nonempty-complement hypothesis. (Hatcher, Lemma 3.27) -/
private theorem support_positive_subsingleton_of_zero_dimensional_charts
    (M : Type u) [TopologicalSpace M]
    (hM : ∀ x : M, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 0)),
      x ∈ e.source) (K : Set M) (R : ModuleCat.{u} ℤ) (i : ℕ) (hi : 0 < i) :
    Subsingleton (supportSingularHomology (TopCat.of M) K R i : Type u) := by
  have : DiscreteTopology M := discrete_of_zero_dimensional_charts M hM
  exact support_positive_subsingleton_of_discrete (TopCat.of M) K R i hi

/-- Hatcher's union argument, p.237, for disjoint compact supports. -/
private theorem disjoint_union_classes_glue_unique (D : CompactSupportMVData.{u})
    (hdisj : Disjoint D.left D.right) (q : ℕ)
    (a : supportSingularHomology D.space D.left D.coefficients q)
    (b : supportSingularHomology D.space D.right D.coefficients q) :
    ∃! c : supportSingularHomology D.space (D.left ∪ D.right) D.coefficients q,
      supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_left q c = a ∧
      supportSingularHomologyRestrict D.space D.coefficients Set.subset_union_right q c = b := by
  have hinter : D.left ∩ D.right = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  have hz (i : ℕ) : Subsingleton
      (supportSingularHomology D.space (D.left ∩ D.right) D.coefficients i : Type u) := by
    rw [hinter]
    exact support_empty_subsingleton D.space D.coefficients i
  obtain ⟨c, hc⟩ := compact_support_union_classes_glue D q a b ((hz q).elim _ _)
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply union_restriction_injective D q (hz (q + 1))
  change (_, -_) = (_, -_)
  rw [hc.1, hc.2, hc'.1, hc'.2]

private theorem support_restrict_refl (X : TopCat.{u}) (R : ModuleCat.{u} ℤ)
    (K : Set X) (q : ℕ) (a : supportSingularHomology X K R q) :
    supportSingularHomologyRestrict X R (Set.Subset.refl K) q a = a := by
  have hid : supportSingularPairMap K K (𝟙 X)
      (fun _ hx hK ↦ hx hK) = 𝟙 (supportSingularPair X K) := by
    ext <;> rfl
  simp [supportSingularHomologyRestrict, supportSingularHomologyMap, hid]

private theorem support_restrict_comp (X : TopCat.{u}) (R : ModuleCat.{u} ℤ)
    {K L A : Set X} (hLK : L ⊆ K) (hAL : A ⊆ L) (q : ℕ)
    (a : supportSingularHomology X K R q) :
    supportSingularHomologyRestrict X R hAL q
      (supportSingularHomologyRestrict X R hLK q a) =
        supportSingularHomologyRestrict X R (hAL.trans hLK) q a := by
  have hcomp : supportSingularPairMap K L (𝟙 X) (fun _ hx hL ↦ hx (hLK hL)) ≫
      supportSingularPairMap L A (𝟙 X) (fun _ hx hA ↦ hx (hAL hA)) =
      supportSingularPairMap K A (𝟙 X) (fun _ hx hA ↦ hx (hLK (hAL hA))) := by
    ext <;> rfl
  have hnorm {B C : Set X} (h : C ⊆ B) : supportSingularHomologyRestrict X R h q =
      (SSetPair.homologyMap
        (supportSingularPairMap B C (𝟙 X) (fun _ hx hC ↦ hx (h hC))) R q).hom.toAddMonoidHom := by
    simp [supportSingularHomologyRestrict, supportSingularHomologyMap]
  rw [hnorm, hnorm, hnorm]
  change (SSetPair.homologyMap _ R q ≫ SSetPair.homologyMap _ R q) a = _
  rw [← SSetPair.homologyMap_comp, hcomp]
  rfl

/-- Restriction of a neighborhood class to a point factors through any compact subsupport containing that point. -/
private theorem support_neighborhood_restrict_point_factorization
    (X : TopCat.{u}) (R : ModuleCat.{u} ℤ) (K U : Set X)
    (_hK : IsCompact K) (_hU : IsOpen U) (hKU : K ⊆ U)
    (x : X) (hx : x ∈ K) (q : ℕ)
    (aU : supportSingularHomology X U R q) :
    supportSingularHomologyRestrict X R (Set.singleton_subset_iff.mpr (hKU hx)) q aU =
      supportSingularHomologyRestrict X R (Set.singleton_subset_iff.mpr hx) q
        (supportSingularHomologyRestrict X R hKU q aU) := by
  exact (support_restrict_comp X R hKU (Set.singleton_subset_iff.mpr hx) q aU).symm

/-- A locally compatible chart class transports to the exact parent support restriction. -/
private theorem support_neighborhood_class_transports_family
    (X : TopCat.{u}) (R : ModuleCat.{u} ℤ) (K U : Set X)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (q : ℕ) (aU : supportSingularHomology X U R q)
    (α : ∀ x : X, supportSingularHomology X {x} R q)
    (haU : ∀ (y : X) (hy : y ∈ U),
      supportSingularHomologyRestrict X R
        (Set.singleton_subset_iff.mpr hy) q aU = α y) :
    ∀ (x : X) (hx : x ∈ K),
      supportSingularHomologyRestrict X R (Set.singleton_subset_iff.mpr hx) q
        (supportSingularHomologyRestrict X R hKU q aU) = α x := by
  intro x hx
  rw [← support_neighborhood_restrict_point_factorization X R K U hK hU hKU x hx q aU]
  exact haU x (hKU hx)

/-- The integral sphere profile supplies a nonzero local orientation class on every positive-radius sphere. -/
private theorem radius_sphere_has_nonzero_orientation_class (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ a : integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = r}) n, a ≠ 0 := by
  have hs := (HolomorphicAnosov.Topology.Homology.reduced_sphere_homology n).2.2 r hr
  obtain ⟨e⟩ := hs.1
  refine ⟨e.inv (1 : reducedSingularIntegralCoefficients), ?_⟩
  intro hz
  have h1 := congrArg (fun f ↦ f (1 : reducedSingularIntegralCoefficients)) e.inv_hom_id
  change e.hom (e.inv (1 : reducedSingularIntegralCoefficients)) = 1 at h1
  rw [hz, map_zero] at h1
  exact one_ne_zero h1.symm

private theorem radius_sphere_has_nonzero_orientation_class_ulift
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ a : ULift.{u} (integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = r}) n), a ≠ 0 := by
  obtain ⟨a, ha⟩ := radius_sphere_has_nonzero_orientation_class n r hr
  refine ⟨ULift.up a, ?_⟩
  intro h
  apply ha
  exact congrArg ULift.down h

/-- The dedicated ModuleCat ULift functor transports the actual reduced sphere homology isomorphism into any requested coefficient universe. -/
private theorem radius_sphere_orientation_iso_ulift (n : ℕ) (r : ℝ) (hr : 0 < r) :
    Nonempty ((ModuleCat.uliftFunctor.{u} ℤ).obj
      (integralReducedSingularHomology
        (TopCat.of {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = r}) n) ≅
      (ModuleCat.uliftFunctor.{u, 0} ℤ).obj
        (show ModuleCat.{0} ℤ from reducedSingularIntegralCoefficients)) := by
  obtain ⟨e⟩ := (HolomorphicAnosov.Topology.Homology.reduced_sphere_homology n).2.2 r hr |>.1
  exact ⟨(ModuleCat.uliftFunctor.{u} ℤ).mapIso e⟩

/-- An excision isomorphism transports nonvanishing in the reverse direction: the target class has a uniquely determined nonzero source preimage. -/
private theorem isIso_homology_preimage_nonzero
    {A B : ModuleCat.{u} ℤ} (f : A ⟶ B) [IsIso f]
    (b : B) (hb : b ≠ 0) :
    ∃ a : A, f.hom a = b ∧ a ≠ 0 := by
  refine ⟨inv f b, ?_, ?_⟩
  · simp
  · intro ha
    apply hb
    rw [← (show f.hom (inv f b) = b by
      simp)]
    rw [ha, map_zero]

/-- In the support-neighborhood excision square, every nonzero target class has a nonzero class on the excision source pair. -/
private theorem support_neighborhood_excision_preimage_nonzero
    (X : TopCat.{u}) (K U : Set X) (hU : IsOpen U)
    (hKU : closure K ⊆ U) (R : ModuleCat.{u} ℤ) (q : ℕ)
    (b : ((singularSubspacePair X Kᶜ).chainComplex R).homology q) (hb : b ≠ 0) :
    ∃ a : ((singularExcisionSource X Kᶜ U).chainComplex R).homology q,
      SSetPair.homologyMap (singularExcisionInclusion X Kᶜ U) R q a = b ∧ a ≠ 0 := by
  let f := SSetPair.homologyMap (singularExcisionInclusion X Kᶜ U) R q
  have : IsIso f := support_neighborhood_excision_homology_isIso X K U hU hKU R q
  exact isIso_homology_preimage_nonzero f b hb

/-- Once the chart/radial comparison identifies the positive-radius sphere group with the target support group, the sphere orientation class yields a nonzero class on the excision source pair. -/
private theorem chart_source_has_nonzero_orientation_class
    (n : ℕ) (r : ℝ) (hr : 0 < r) (X : TopCat) (K U : Set X)
    (_hK : IsCompact K) (hU : IsOpen U) (hKU : closure K ⊆ U)
    (R : ModuleCat ℤ)
    (e : integralReducedSingularHomology
      (TopCat.of {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = r}) n ≅
      ((singularSubspacePair X Kᶜ).chainComplex R).homology n) :
    ∃ a : ((singularExcisionSource X Kᶜ U).chainComplex R).homology n, a ≠ 0 := by
  obtain ⟨s, hs⟩ := radius_sphere_has_nonzero_orientation_class n r hr
  let b := e.hom s
  have hb : b ≠ 0 := by
    intro hb
    change e.hom s = 0 at hb
    have hs' := congrArg (fun f ↦ f s) e.hom_inv_id
    change e.inv (e.hom s) = s at hs'
    rw [hb, map_zero] at hs'
    exact hs hs'.symm
  obtain ⟨a, _, ha⟩ := support_neighborhood_excision_preimage_nonzero
    X K U hU hKU R n b hb
  exact ⟨a, ha⟩

/-- Hatcher's finite union argument specialized to finite supports. -/
theorem finite_support_classes_unique (X : TopCat.{u}) [T2Space X]
    (R : ModuleCat.{u} ℤ) (q : ℕ) (K : Set X) (hK : K.Finite)
    (α : ∀ x : X, supportSingularHomology X {x} R q) :
    ∃! a : supportSingularHomology X K R q, ∀ (x : X) (hx : x ∈ K),
      supportSingularHomologyRestrict X R (Set.singleton_subset_iff.mpr hx) q a = α x := by
  classical
  induction K, hK using Set.Finite.induction_on with
  | empty =>
    refine ⟨0, ?_, ?_⟩
    · intro x hx
      exact False.elim hx
    · intro a ha
      exact (support_empty_subsingleton X R q).elim _ _
  | @insert x K hx hK ih =>
    rw [Set.insert_eq]
    let D : CompactSupportMVData.{u} :=
      ⟨X, inferInstance, {x}, K, isCompact_singleton, hK.isCompact, R⟩
    have hd : Disjoint D.left D.right := by
      exact Set.disjoint_singleton_left.mpr hx
    obtain ⟨b, hb, hbu⟩ := ih
    obtain ⟨c, hc, hcu⟩ := disjoint_union_classes_glue_unique D hd q (α x) b
    refine ⟨c, ?_, ?_⟩
    · intro y hy
      rcases hy with hy | hy
      · have hyx : y = x := hy
        subst y
        exact hc.1
      · rw [← support_restrict_comp X R (K := {x} ∪ K) Set.subset_union_right
          (Set.singleton_subset_iff.mpr hy) q c, hc.2]
        exact hb y hy
    · intro d hd
      apply hcu d
      refine ⟨hd x (Or.inl rfl), ?_⟩
      apply hbu
      intro y hy
      rw [support_restrict_comp]
      exact hd y (Or.inr hy)

/-- Point restrictions detect classes on finite supports. -/
theorem finite_support_zero_of_point_restrictions
    (X : TopCat.{u}) [T2Space X] (R : ModuleCat.{u} ℤ) (q : ℕ)
    (K : Set X) (hK : K.Finite) (a : supportSingularHomology X K R q)
    (ha : ∀ (x : X) (hx : x ∈ K),
      supportSingularHomologyRestrict X R (Set.singleton_subset_iff.mpr hx) q a = 0) :
    a = 0 := by
  obtain ⟨c, hc, huniq⟩ := finite_support_classes_unique X R q K hK (fun _ ↦ 0)
  exact (huniq a ha).trans (huniq 0 (fun x hx ↦ map_zero _)).symm

private theorem support_restrict_native_apply (X : TopCat.{u}) (R : ModuleCat.{u} ℤ)
    {A B : Set X} (h : B ⊆ A) (q : ℕ) (a : supportSingularHomology X A R q) :
    supportSingularHomologyRestrict X R h q a =
      SSetPair.homologyMap
        (SSetPair.homMk (X := supportSingularPair X A) (Y := supportSingularPair X B)
          (TopCat.toSSet.map (TopCat.ofHom
            ⟨fun z : ↥(Aᶜ) ↦ (⟨z.val, fun hz ↦ z.property (h hz)⟩ : ↥(Bᶜ)),
              continuous_subtype_val.subtype_mk _⟩))
          (𝟙 _) (by rfl)) R q a := by
  simp [supportSingularHomologyRestrict, supportSingularHomologyMap,
    supportSingularPairMap]
  congr 3

end IntegralCompactSupportOrientation

/-- A locally compatible integral local-homology family has a unique supported class on every compact subset of a Hausdorff boundaryless topological manifold. (Hatcher) -/
theorem hatcher_integral_compact_support_orientation
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    (hM : ∀ x : M, ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), x ∈ e.source)
    (K : Set M) (hK : IsCompact K) :
    let pair : Set M → SSetPair.{u} := fun A ↦
      let i : TopCat.of ↥(Aᶜ) ⟶ TopCat.of M :=
        TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
      letI : Mono i := (TopCat.mono_iff_injective i).mpr Subtype.val_injective
      SSetPair.of (TopCat.toSSet.map i)
    let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
    let H : Set M → ℕ → ModuleCat.{u} ℤ := fun A i ↦ (pair A).homology R i
    let restrict : ∀ (A B : Set M), B ⊆ A → ∀ i : ℕ, H A i ⟶ H B i :=
      fun A B h i ↦ SSetPair.homologyMap
        (SSetPair.homMk (X := pair A) (Y := pair B)
          (TopCat.toSSet.map (TopCat.ofHom
            ⟨fun z : ↥(Aᶜ) ↦ (⟨z.val, fun hz ↦ z.property (h hz)⟩ : ↥(Bᶜ)),
              continuous_subtype_val.subtype_mk _⟩))
          (𝟙 _) (by rfl)) R i
    (∀ α : ∀ x : M, (H {x} n : Type u),
      (∀ x : M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
        ∃ aW : (H W n : Type u), ∀ (y : M) (hy : y ∈ W),
          restrict W {y} (by simpa only [Set.singleton_subset_iff] using hy) n aW = α y) →
      ∃! aK : (H K n : Type u), ∀ (x : M) (hx : x ∈ K),
        restrict K {x} (by simpa only [Set.singleton_subset_iff] using hx) n aK = α x) ∧
    (∀ aK : (H K n : Type u),
      (∀ (x : M) (hx : x ∈ K),
        restrict K {x} (by simpa only [Set.singleton_subset_iff] using hx) n aK = 0) →
      aK = 0) ∧
    ∀ i : ℕ, n < i → Subsingleton (H K i : Type u) := by
  classical
  dsimp only
  by_cases hKempty : K = ∅
  · subst K
    have hempty (q : ℕ) : Subsingleton
        (Topology.supportSingularHomology (TopCat.of M) ∅
          (ModuleCat.of ℤ (ULift.{u} ℤ)) q : Type u) :=
      IntegralCompactSupportOrientation.support_empty_subsingleton
        (TopCat.of M) (ModuleCat.of ℤ (ULift.{u} ℤ)) q
    let hzero := hempty n
    refine ⟨?_, ?_, ?_⟩
    · intro α hα
      refine ⟨0, ?_, ?_⟩
      · intro x hx
        exact False.elim hx
      · intro a ha
        exact hzero.elim _ _
    · intro a ha
      exact hzero.elim _ _
    · intro i hi
      exact hempty i
  · by_cases hn : n = 0
    · subst n
      have hfin : K.Finite :=
        IntegralCompactSupportOrientation.finite_support_of_zero_dimensional_charts M hM K hK
      refine ⟨?_, ?_, ?_⟩
      · intro α hα
        have ht :=
          IntegralCompactSupportOrientation.finite_support_classes_unique
            (TopCat.of M) (ModuleCat.of ℤ (ULift.{u} ℤ)) 0 K hfin α
        simp only [IntegralCompactSupportOrientation.support_restrict_native_apply] at ht
        convert ht using 1 <;> rfl
      · intro a ha
        change Topology.supportSingularHomology (TopCat.of M) K
          (ModuleCat.of ℤ (ULift.{u} ℤ)) 0 at a
        apply IntegralCompactSupportOrientation.finite_support_zero_of_point_restrictions
          (TopCat.of M) (ModuleCat.of ℤ (ULift.{u} ℤ)) 0 K hfin a
        intro x hx
        rw [IntegralCompactSupportOrientation.support_restrict_native_apply]
        exact ha x hx
      · intro i hi
        exact IntegralCompactSupportOrientation.support_positive_subsingleton_of_zero_dimensional_charts
          M hM K (ModuleCat.of ℤ (ULift.{u} ℤ)) i hi
    · let X := TopCat.of M
      let R : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)
      let H (A : Set M) (q : ℕ) := Topology.supportSingularHomology X A R q
      let res {A B : Set M} (h : B ⊆ A) (q : ℕ) :=
        Topology.supportSingularHomologyRestrict X R h q
      let compatible (α : ∀ x : M, H {x} n) : Prop :=
        ∀ x : M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
          ∃ aW : H W n, ∀ (y : M) (hy : y ∈ W),
            res (Set.singleton_subset_iff.mpr hy) n aW = α y
      let P (A : Set M) : Prop :=
        (∀ α : ∀ x : M, H {x} n, compatible α →
          ∃! aA : H A n, ∀ (x : M) (hx : x ∈ A),
            res (Set.singleton_subset_iff.mpr hx) n aA = α x) ∧
        (∀ aA : H A n, (∀ (x : M) (hx : x ∈ A),
          res (Set.singleton_subset_iff.mpr hx) n aA = 0) → aA = 0) ∧
        ∀ q : ℕ, n < q → Subsingleton (H A q)
      suffices hPK : P K by
        simp only [P, compatible, H, res,
          IntegralCompactSupportOrientation.support_restrict_native_apply] at hPK
        convert hPK using 1 <;> rfl
      
      
      have hunion (A B : Set M) (hA : IsCompact A) (hB : IsCompact B)
          (hPA : P A) (hPB : P B) (hPAB : P (A ∩ B)) : P (A ∪ B) := by
        let D : Topology.CompactSupportMVData.{u} :=
          ⟨X, inferInstance, A, B, hA, hB, R⟩
        have hnext := hPAB.2.2 (n + 1) (Nat.lt_succ_self n)
        refine ⟨?_, ?_, ?_⟩
        · intro α hα
          obtain ⟨a, ha, hau⟩ := hPA.1 α hα
          obtain ⟨b, hb, hbu⟩ := hPB.1 α hα
          have hab : res (A := A) Set.inter_subset_left n a =
              res (A := B) Set.inter_subset_right n b := by
            apply sub_eq_zero.mp
            apply hPAB.2.1
            intro x hx
            rw [map_sub]
            rw [IntegralCompactSupportOrientation.support_restrict_comp,
              IntegralCompactSupportOrientation.support_restrict_comp]
            exact sub_eq_zero.mpr ((ha x hx.1).trans (hb x hx.2).symm)
          obtain ⟨c, hcA, hcB⟩ :=
            compact_support_union_classes_glue D n a b hab
          refine ⟨c, ?_, ?_⟩
          · intro x hx
            rcases hx with hx | hx
            · rw [← IntegralCompactSupportOrientation.support_restrict_comp X R
                (K := A ∪ B) Set.subset_union_left
                (Set.singleton_subset_iff.mpr hx) n c, hcA]
              exact ha x hx
            · rw [← IntegralCompactSupportOrientation.support_restrict_comp X R
                (K := A ∪ B) Set.subset_union_right
                (Set.singleton_subset_iff.mpr hx) n c, hcB]
              exact hb x hx
          · intro d hd
            have hdA : res (A := A ∪ B) Set.subset_union_left n d = a := by
              apply hau
              intro x hx
              rw [IntegralCompactSupportOrientation.support_restrict_comp]
              exact hd x (Or.inl hx)
            have hdB : res (A := A ∪ B) Set.subset_union_right n d = b := by
              apply hbu
              intro x hx
              rw [IntegralCompactSupportOrientation.support_restrict_comp]
              exact hd x (Or.inr hx)
            apply IntegralCompactSupportOrientation.union_restriction_injective D n hnext
            change (res Set.subset_union_left n d, -res Set.subset_union_right n d) =
              (res Set.subset_union_left n c, -res Set.subset_union_right n c)
            rw [hdA, hdB, hcA, hcB]
        · intro c hc
          apply IntegralCompactSupportOrientation.union_zero_of_restrictions D n hnext c
          · apply hPA.2.1
            intro x hx
            rw [IntegralCompactSupportOrientation.support_restrict_comp]
            exact hc x (Or.inl hx)
          · apply hPB.2.1
            intro x hx
            rw [IntegralCompactSupportOrientation.support_restrict_comp]
            exact hc x (Or.inr hx)
        · exact IntegralCompactSupportOrientation.union_above_dimension_subsingleton
            D n hPA.2.2 hPB.2.2 hPAB.2.2
      have hPempty : P ∅ := by
        have hz (q : ℕ) : Subsingleton (H ∅ q) :=
          IntegralCompactSupportOrientation.support_empty_subsingleton X R q
        refine ⟨?_, ?_, fun q _ ↦ hz q⟩
        · intro α hα
          exact ⟨0, fun x hx ↦ hx.elim, fun a _ ↦ (hz n).elim _ _⟩
        · intro a ha
          exact (hz n).elim _ _
      
      
      suffices hchart : ∀ A : Set M, IsCompact A →
          (∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), A ⊆ e.source) →
          P A by
        obtain ⟨s, F, hF, hcover⟩ := finite_compact_chart_cover hM K hK
        have hind (s : Finset K) : ∀ F : K → Set M,
            (∀ i ∈ s, IsCompact (F i) ∧
              ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), F i ⊆ e.source) →
            P (⋃ i ∈ s, F i) := by
          induction s using Finset.induction_on with
          | empty =>
            intro F hF
            simpa using hPempty
          | @insert a s ha ih =>
            intro F hF
            obtain ⟨hcA, heA⟩ := hF a (Finset.mem_insert_self a s)
            have hFs (i) (hi : i ∈ s) := hF i (Finset.mem_insert_of_mem hi)
            have hrest := ih F hFs
            have hinter : P (F a ∩ ⋃ i ∈ s, F i) := by
              have ht := ih (fun i ↦ F a ∩ F i) (by
                intro i hi
                obtain ⟨hc, e, he⟩ := hFs i hi
                exact ⟨hcA.inter_right hc.isClosed, e, Set.inter_subset_right.trans he⟩)
              simpa only [Set.inter_iUnion] using ht
            have hcRest : IsCompact (⋃ i ∈ s, F i) :=
              s.isCompact_biUnion (fun i hi ↦ (hFs i hi).1)
            simpa only [Finset.set_biUnion_insert] using
              hunion (F a) (⋃ i ∈ s, F i) hcA hcRest
                (hchart (F a) hcA heA) hrest hinter
        rw [hcover]
        exact hind s F (fun i hi ↦ ⟨(hF i hi).1, (hF i hi).2.2⟩)
      
      
      
      
      suffices hchartDV : ∀ A : Set M, IsCompact A →
          (∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), A ⊆ e.source) →
          (∀ aA : H A n, (∀ (x : M) (hx : x ∈ A),
            res (Set.singleton_subset_iff.mpr hx) n aA = 0) → aA = 0) ∧
          (∀ q : ℕ, n < q → Subsingleton (H A q)) by
        intro A hA ⟨e, hAe⟩
        have hDV := hchartDV A hA ⟨e, hAe⟩
        refine ⟨?_, hDV.1, hDV.2⟩
        intro α hα
        exact compact_support_class_of_local_compatibility X R n A hA
          (fun B hBA hB ↦ (hchartDV B hB ⟨e, hBA.trans hAe⟩).1)
          α (fun x _ ↦ hα x)
      intro A hA ⟨e, hAe⟩
      have hprovider := positive_dimensional_chart_support_detection n hn M hM A hA e hAe
      simpa only [H, res] using hprovider

end HolomorphicAnosov


