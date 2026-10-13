import HolomorphicAnosov.Topology.EuclideanDisplacementPairHomotopy
import HolomorphicAnosov.Topology.EuclideanSupportOrientationEnlargement
import HolomorphicAnosov.Topology.EuclideanProductFixedSetEmpty
import HolomorphicAnosov.Topology.EuclideanProductFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanHomotopySliceFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanDisjointRestrictedFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanRestrictedMap
import HolomorphicAnosov.Topology.EuclideanRestrictedFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanFixedPointIndexEmpty
import HolomorphicAnosov.Topology.EuclideanConstantFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanZeroIdentityFixedSetCompact
import HolomorphicAnosov.Topology.EuclideanFixedPointIndexRestriction
import HolomorphicAnosov.Topology.Homology.IntegralCompactSupportOrientation
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.EuclideanSupportOrientationNaturality
import HolomorphicAnosov.Topology.EuclideanConstantFixedPointIndexOne
import HolomorphicAnosov.Topology.EuclideanProductFixedPointIndexMul

/-!
# Basic laws of the canonical Euclidean fixed-point index

Source: Albrecht Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood
retracts*, Topology 4 (1965), §§1.1–1.7, printed pp.1–2; Hatcher, *Algebraic Topology*,
pp.115–124,233–238,269,277–278; Bredon, *Topology and Geometry*, IV§16 pp.220–222,
VI§1 pp.317–318 and VI§2 p.320.
DAG node: `topo.euclidean_fixed_point_index_basic_laws_g9`.

The index is the published canonical integral construction from the original displacement
and the compactification/excision-supported positive orientation. It is imported unchanged.
The theorem-local expressions form the actual restricted maps, ordered-coordinate product maps,
and time slices needed to state the laws. Their data are native continuous maps and the
standard Euclidean coordinate equivalence. The full source proof is documented below and the seven laws are proved from the imported
orientation, homotopy, product, and normalization results.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace HolomorphicAnosov


/-- Dold's exact restriction, empty-support, finite disjoint additivity, compact-total-support
homotopy, oriented product, constant-map and dimension-zero laws for the constructed index.

Source: Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood retracts*,
Topology 4 (1965), §§1.1–1.7 pp.1–2; Hatcher pp.115–124,233–238,269,277–278;
Bredon *Topology and Geometry*, IV§16 pp.220–222 and VI§1 pp.317–318, VI§2 p.320.
Current DAG node: `topo.euclidean_fixed_point_index_basic_laws_g9`, clauses D1–D7.

The local restriction expression composes the original map with the actual domain inclusion
(Dold §1.3 p.1). The local product domain is the inverse image of U×V under the standard
`EuclideanSpace.finAddEquivProd`; the product map applies f and g in those first-factor-then-
second-factor coordinates and maps back (Dold §1.6 p.2, Hatcher p.269). The local time slice
composes the given continuous homotopy with x↦(x,t), using the native unit-interval topology
(Dold §1.7 p.2). These expressions contain actual maps and continuity proofs, and add no
inputs or hypotheses.

Complete natural-language proof:

The definition uses ordinary integral singular homology. For positive n, normalize the
compactification sphere class by the explicit ordered positive affine-simplex local generator;
the sphere-pair projection is an isomorphism, so the normalization is unique. For n=0 choose
the finite-point ordinary H₀ class in the two-point compactification. For compact K⊆U, excision
removes the closed compactification complement of U, whose closure is inside the open complement
of K. Invert exactly that inclusion-induced map and project the compactification class to get
o(U,K). The continuous displacement vanishes exactly on the fixed set, hence induces the specified
map of relative pairs. Reading its image of o(U,Fix(f)) in the explicit positive target gives I.

For restriction, inclusions of supports and domains commute with compactification projection and
excision. If all fixed points lie in V, their inclusion lifts the same compact support to V,
so the restricted fixed set is compact and its orientation maps to the original orientation.
The displacement square commutes, giving equal coefficients. If the fixed set is empty, the
relative pair is (U,U), whose literal quotient complex is zero, so the index is zero.

For finitely many pairwise disjoint open Vᵢ covering Fix(f), each fixed piece is closed in the
compact fixed set: its complement is the union of the other pieces, relatively open. Thus its
lift into Vᵢ is compact. The inclusions of the relative pairs commute with displacement.
The global orientation equals the sum of their images: apply Hatcher's compact-support
point detection on the native open domain U, with support the preimage in U of the ambient
fixed set. At any fixed point exactly one Vᵢ contains it. Support restriction and domain
naturality give its local orientation from that summand; every other summand factors through
the empty-support relative group and is zero. The difference thus has zero point restrictions,
so detection makes it zero. Displacement and the integral coordinate map preserve the finite
sum, proving index additivity. For an empty family
the covering condition forces an empty fixed set, giving the empty sum zero.

For a homotopy, project its compact total fixed locus in U×[0,1] to obtain one compact J⊆U
containing every time-slice fixed set. Each fixed slice is compact, since it is the closed
time-slice intersection of that compact locus, projected to U. The displacement homotopy never
vanishes on U minus J, so it is a homotopy of the single fixed pair (U,U minus J) to
(ℝⁿ,ℝⁿ minus zero). Support enlargement replaces both endpoint classes by o(U,J). Relative
homotopy invariance gives equality of the induced maps and hence of the endpoint indices.

For products, the fixed set is the actual product of the two compact fixed sets, carried by the
coordinate homeomorphism. The complement pair is (U×V,(U minus F)×V ∪ U×(V minus G)); both
complements are open, so the Bredon relative product equals Hatcher's simplex triangulation.
At a support point choose positive affine factor simplices with interior parameter coordinates
all distinct. The point belongs to exactly one top simplex of the grid-path triangulation.
Replacing cumulative edges by successive edges has determinant +1; interleaving the factor
edges contributes precisely the grid-path parity, cancelled by the coefficient sign in the
product formula. Thus the product of the positive point classes is the positive concatenated
coordinate point class. The simplex model's factor signs are corrected to their actual positive
edge determinants. Naturality gives this equality at every point of arbitrary compact supports;
Hatcher's integral compact-support detection theorem makes the supported product equal to the
product support orientation. Naturality and integral bilinearity of the product displacement
then give I(f×g)=I(f)I(g). Empty supports give zero on both sides. A zero-dimensional factor
inserts the positive H₀ point class and is a product unit, including when both dimensions vanish.

For a constant value c∈U, the support is the singleton c. Its displacement is the translation
x↦x−c, which carries the ordered-coordinate local class to the prescribed positive zero class;
therefore its coefficient is 1. Finally ℝ⁰ is a singleton: on the full domain the identity and
displacement are the unique point map. The chosen finite-point compactification class projects
to the ordinary coefficient-one point class, so its index is 1. Empty domains have index zero.
Ordinary H₀(S⁰)=ℤ⊕ℤ is never mistaken for ℤ, and reduced H₀(S⁰) is used only in the positive-
dimensional sphere-pair computation. No compactness of separate slices substitutes for compactness
of the total fixed locus, and no regularity of maps or fixed sets is assumed.

The existential compactness witnesses in conclusions prove admissibility of derived maps;
they add no hypotheses to the source laws. All coefficients refer to the actual constructed
index, rather than to an arbitrary function satisfying an axiomatized list of laws.
-/

theorem euclidean_fixed_point_index_basic_laws :
    let euclideanRestrictMap :
      ∀ {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))},
        C(U, EuclideanSpace ℝ (Fin n)) →
          ∀ V : Opens (EuclideanSpace ℝ (Fin n)), V ≤ U → C(V, EuclideanSpace ℝ (Fin n)) :=
      fun {n} {U} f V hVU ↦
        ⟨fun x ↦ f ⟨x.1, hVU x.2⟩,
          f.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
    let euclideanProductDomain :
      ∀ {n m : ℕ}, Opens (EuclideanSpace ℝ (Fin n)) →
        Opens (EuclideanSpace ℝ (Fin m)) → Opens (EuclideanSpace ℝ (Fin (n + m))) :=
      fun {n} {m} U V ↦
        ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ)) ⁻¹' (U ×ˢ V),
          (U.isOpen.prod V.isOpen).preimage EuclideanSpace.finAddEquivProd.continuous⟩
    let euclideanProductMap :
      ∀ {n m : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
        {V : Opens (EuclideanSpace ℝ (Fin m))},
        C(U, EuclideanSpace ℝ (Fin n)) → C(V, EuclideanSpace ℝ (Fin m)) →
          C(euclideanProductDomain U V, EuclideanSpace ℝ (Fin (n + m))) :=
      fun {n} {m} {U} {V} f g ↦ by
        let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
        let a : C(euclideanProductDomain U V, U) :=
          ⟨fun x ↦ ⟨(e x.1).1, x.2.1⟩,
            (e.continuous.comp continuous_subtype_val).fst.subtype_mk _⟩
        let b : C(euclideanProductDomain U V, V) :=
          ⟨fun x ↦ ⟨(e x.1).2, x.2.2⟩,
            (e.continuous.comp continuous_subtype_val).snd.subtype_mk _⟩
        exact ⟨fun x ↦ e.symm (f (a x), g (b x)),
          e.symm.continuous.comp ((f.continuous.comp a.continuous).prodMk
            (g.continuous.comp b.continuous))⟩
    let euclideanHomotopySlice :
      ∀ {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))},
        C(U × unitInterval, EuclideanSpace ℝ (Fin n)) →
          unitInterval → C(U, EuclideanSpace ℝ (Fin n)) :=
      fun {n} {U} H t ↦
        H.comp ⟨fun x ↦ (x, t), continuous_id.prodMk continuous_const⟩
    (∀ (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
      (f : C(U, EuclideanSpace ℝ (Fin n))) (hK : IsCompact (euclideanFixedSet f)),
      (∀ (V : Opens (EuclideanSpace ℝ (Fin n))) (hVU : V ≤ U),
        (∀ x ∈ euclideanFixedSet f, x.1 ∈ V) →
        ∃ hV : IsCompact (euclideanFixedSet (euclideanRestrictMap f V hVU)),
          euclideanFixedPointIndex (euclideanRestrictMap f V hVU) hV =
            euclideanFixedPointIndex f hK) ∧
      (euclideanFixedSet f = ∅ → euclideanFixedPointIndex f hK = 0) ∧
      (∀ (k : ℕ) (V : Fin k → Opens (EuclideanSpace ℝ (Fin n)))
        (hVU : ∀ i, V i ≤ U),
      (∀ i j, i ≠ j → Disjoint (V i : Set (EuclideanSpace ℝ (Fin n)))
        (V j : Set (EuclideanSpace ℝ (Fin n)))) →
        (∀ x ∈ euclideanFixedSet f, ∃ i, x.1 ∈ V i) →
        ∃ hV : ∀ i, IsCompact (euclideanFixedSet (euclideanRestrictMap f (V i) (hVU i))),
          euclideanFixedPointIndex f hK =
            ∑ i, euclideanFixedPointIndex (euclideanRestrictMap f (V i) (hVU i)) (hV i))) ∧
    (∀ (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
      (H : C(U × unitInterval, EuclideanSpace ℝ (Fin n))),
      IsCompact (Set.ofPred (fun p : U × unitInterval ↦ H p = p.1.1)) →
      ∃ (h0 : IsCompact (euclideanFixedSet (euclideanHomotopySlice H 0)))
        (h1 : IsCompact (euclideanFixedSet (euclideanHomotopySlice H 1))),
        euclideanFixedPointIndex (euclideanHomotopySlice H 0) h0 =
          euclideanFixedPointIndex (euclideanHomotopySlice H 1) h1) ∧
    (∀ (n m : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
      (V : Opens (EuclideanSpace ℝ (Fin m)))
      (f : C(U, EuclideanSpace ℝ (Fin n))) (g : C(V, EuclideanSpace ℝ (Fin m)))
      (hF : IsCompact (euclideanFixedSet f)) (hG : IsCompact (euclideanFixedSet g)),
      ∃ hP : IsCompact (euclideanFixedSet (euclideanProductMap f g)),
        euclideanFixedPointIndex (euclideanProductMap f g) hP =
          euclideanFixedPointIndex f hF * euclideanFixedPointIndex g hG) ∧
    (∀ (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n)),
      c ∈ U → ∃ hC : IsCompact (euclideanFixedSet (ContinuousMap.const U c)),
        euclideanFixedPointIndex (ContinuousMap.const U c) hC = 1) ∧
    (∃ h0 : IsCompact (euclideanFixedSet
        (⟨Subtype.val, continuous_subtype_val⟩ : C((⊤ : Opens (EuclideanSpace ℝ (Fin 0))),
          EuclideanSpace ℝ (Fin 0)))),
      euclideanFixedPointIndex (⟨Subtype.val, continuous_subtype_val⟩ :
        C((⊤ : Opens (EuclideanSpace ℝ (Fin 0))), EuclideanSpace ℝ (Fin 0))) h0 = 1)  := by
  dsimp only
  constructor
  · intro n U f hK
    constructor
    · intro V hVU hV
      refine ⟨restricted_fixedSet_compact f hK V hVU hV, ?_⟩
      exact restriction_index f hK V hVU hV _
    constructor
    · intro hEmpty
      exact fixed_index_zero_of_empty f hK hEmpty
    · intro k V hVU hdisj hcover
      classical
      have hc := disjoint_restricted_fixedSet_compact f hK V hVU hdisj hcover
      refine ⟨hc, ?_⟩
      let g (i : Fin k) := restrictedMap f (V i) (hVU i)
      let j (i : Fin k) :
          euclideanSupportPair n (V i : Set _) (euclideanAmbientFixedSet (g i)) ⟶
            euclideanSupportPair n (U : Set _) (euclideanAmbientFixedSet f) :=
        singularSubspacePairMap
          (TopCat.ofHom (⟨fun x : V i ↦ (⟨x.val, hVU i x.property⟩ : U),
            continuous_subtype_val.subtype_mk _⟩ : C(V i, U)))
          {x : V i | x.val ∉ euclideanAmbientFixedSet (g i)}
          {x : U | x.val ∉ euclideanAmbientFixedSet f} (by
            intro x hx hfixed
            obtain ⟨u, hu, he⟩ := hfixed
            have heq : u = (⟨x.val, hVU i x.property⟩ : U) := Subtype.ext he
            subst u
            exact hx ⟨x, hu, rfl⟩)
      have hj (i : Fin k) : j i ≫ euclideanDisplacementPairMap f =
          euclideanDisplacementPairMap (g i) := by
        apply MorphismProperty.Arrow.Hom.ext
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
          rw [← Functor.map_comp]
          rfl
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
          rw [← Functor.map_comp]
          rfl
      have hcomp (i : Fin k) :
          SSetPair.homologyMap (j i) reducedSingularIntegralCoefficients n ≫
            euclideanDisplacementHomologyMap f =
              euclideanDisplacementHomologyMap (g i) := by
        unfold euclideanDisplacementHomologyMap
        rw [← SSetPair.homologyMap_comp, hj]
      let o := euclideanSupportOrientation n (U : Set _) (euclideanAmbientFixedSet f)
        U.isOpen (hK.image continuous_subtype_val)
        (by rintro x ⟨u, hu, rfl⟩; exact u.property)
      let oi (i : Fin k) := euclideanSupportOrientation n (V i : Set _)
        (euclideanAmbientFixedSet (g i)) (V i).isOpen
        ((hc i).image continuous_subtype_val)
        (by rintro x ⟨u, hu, rfl⟩; exact u.property)
      suffices hOrientation : o = ∑ i,
          (SSetPair.homologyMap (j i) reducedSingularIntegralCoefficients n).hom
            (oi i) by
        change euclideanPositiveLocalCoordinate n
          ((euclideanDisplacementHomologyMap f).hom o) =
            ∑ i, euclideanPositiveLocalCoordinate n
              ((euclideanDisplacementHomologyMap (g i)).hom (oi i))
        rw [hOrientation, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (euclideanPositiveLocalCoordinate n)
          (congrArg (fun q ↦ q.hom (oi i)) (hcomp i))
      -- Hatcher's detection theorem uses supports in the native domain U.
      -- Its support is the preimage of the ambient fixed set, not that
      -- ambient set itself; these carriers are related explicitly here.
      let K : Set U := Subtype.val ⁻¹' euclideanAmbientFixedSet f
      have hKnative : K = euclideanFixedSet f := by
        ext x
        constructor
        · rintro ⟨y, hy, hyx⟩
          have hxy : y = x := Subtype.ext hyx
          simpa only [hxy] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      have hcharts : ∀ x : U, ∃ e : OpenPartialHomeomorph U
          (EuclideanSpace ℝ (Fin n)), x ∈ e.source := by
        intro x
        exact ⟨U.openPartialHomeomorphSubtypeCoe ⟨x⟩, Set.mem_univ x⟩
      have hdetect := (hatcher_integral_compact_support_orientation n U
        hcharts K (hKnative.symm ▸ hK)).2.1
      apply sub_eq_zero.mp
      apply hdetect
      intro x hx
      have hsingleton : ({x} : Set U) =
          Subtype.val ⁻¹' ({x.val} : Set (EuclideanSpace ℝ (Fin n))) := by
        ext y
        simp only [Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
      let rr (B : Set U) (hB : B ⊆ K) :
          singularSubspacePair (TopCat.of U) Kᶜ ⟶
            singularSubspacePair (TopCat.of U) Bᶜ :=
        SSetPair.homMk
          (TopCat.toSSet.map (TopCat.ofHom
            ⟨fun z : ↥(Kᶜ) ↦ (⟨z.val, fun hz ↦ z.property (hB hz)⟩ : ↥(Bᶜ)),
              continuous_subtype_val.subtype_mk _⟩))
          (𝟙 _) (by rfl)
      suffices hall : ∀ (B : Set U) (hB : B ⊆ K),
          B = Subtype.val ⁻¹' ({x.val} : Set (EuclideanSpace ℝ (Fin n))) →
          (SSetPair.homologyMap (rr B hB) reducedSingularIntegralCoefficients n).hom
            (o - ∑ l, (SSetPair.homologyMap (j l)
              reducedSingularIntegralCoefficients n).hom (oi l)) = 0 by
        exact hall {x} (Set.singleton_subset_iff.mpr hx) hsingleton
      intro B hB heB
      subst B
      have hxF : x.val ∈ euclideanAmbientFixedSet f := hx
      let r : euclideanSupportPair n (U : Set _) (euclideanAmbientFixedSet f) ⟶
          euclideanSupportPair n (U : Set _) {x.val} :=
        singularSubspacePairMap (𝟙 (TopCat.of U))
          {u : U | u.val ∉ euclideanAmbientFixedSet f}
          {u : U | u.val ∉ ({x.val} : Set _)}
          (by intro u hu hu'; exact hu ((Set.mem_singleton_iff.mp hu').symm ▸ hxF))
      have hrr : rr (Subtype.val ⁻¹' ({x.val} : Set _)) hB = r := by
        apply MorphismProperty.Arrow.Hom.ext
        · rfl
        · exact (TopCat.toSSet.map_id _).symm
      rw [hrr]
      change (SSetPair.homologyMap r reducedSingularIntegralCoefficients n).hom
        (o - ∑ l, (SSetPair.homologyMap (j l)
          reducedSingularIntegralCoefficients n).hom (oi l)) = 0
      rw [map_sub, map_sum]
      apply sub_eq_zero.mpr
      obtain ⟨i, hi⟩ := hcover x (hKnative ▸ hx)
      have hoff (l : Fin k) (hli : l ≠ i) : x.val ∉ V l := by
        intro hxl
        exact Set.disjoint_left.mp (hdisj l i hli) hxl hi
      have hzero (l : Fin k) (hli : l ≠ i) :
          (SSetPair.homologyMap r reducedSingularIntegralCoefficients n).hom
            ((SSetPair.homologyMap (j l) reducedSingularIntegralCoefficients n).hom
              (oi l)) = 0 := by
        let a : euclideanSupportPair n (V l : Set _) (euclideanAmbientFixedSet (g l)) ⟶
            euclideanSupportPair n (V l : Set _) ∅ :=
          singularSubspacePairMap (𝟙 (TopCat.of (V l)))
            {u : V l | u.val ∉ euclideanAmbientFixedSet (g l)}
            {u : V l | u.val ∉ (∅ : Set (EuclideanSpace ℝ (Fin n)))}
            (by simp)
        let b : euclideanSupportPair n (V l : Set _) ∅ ⟶
            euclideanSupportPair n (U : Set _) {x.val} :=
          singularSubspacePairMap
            (TopCat.ofHom (⟨fun u : V l ↦ (⟨u.val, hVU l u.property⟩ : U),
              continuous_subtype_val.subtype_mk _⟩ : C(V l, U)))
            {u : V l | u.val ∉ (∅ : Set (EuclideanSpace ℝ (Fin n)))}
            {u : U | u.val ∉ ({x.val} : Set _)}
            (by
              intro u hu he
              exact hoff l hli (Set.mem_singleton_iff.mp he ▸ u.property))
        have hab : j l ≫ r = a ≫ b := by
          apply MorphismProperty.Arrow.Hom.ext <;>
            change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
              TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ <;>
            rw [← Functor.map_comp, ← Functor.map_comp] <;> rfl
        have ha : (SSetPair.homologyMap a reducedSingularIntegralCoefficients n).hom
            (oi l) = 0 := by
          have he := euclideanSupportOrientation_enlargement n (V l : Set _) ∅
            (euclideanAmbientFixedSet (g l)) (V l).isOpen isCompact_empty
            ((hc l).image continuous_subtype_val) (Set.empty_subset _)
            (by rintro y ⟨u, hu, rfl⟩; exact u.property)
          rw [euclideanSupportOrientation_empty] at he
          exact he
        change (SSetPair.homologyMap (j l) reducedSingularIntegralCoefficients n ≫
          SSetPair.homologyMap r reducedSingularIntegralCoefficients n).hom (oi l) = 0
        rw [← SSetPair.homologyMap_comp, hab, SSetPair.homologyMap_comp]
        change (SSetPair.homologyMap b reducedSingularIntegralCoefficients n).hom
          ((SSetPair.homologyMap a reducedSingularIntegralCoefficients n).hom (oi l)) = 0
        rw [ha, map_zero]
      rw [Finset.sum_eq_single i (fun l _ hli ↦ hzero l hli) (by simp)]
      let a : euclideanSupportPair n (V i : Set _) (euclideanAmbientFixedSet (g i)) ⟶
          euclideanSupportPair n (V i : Set _) {x.val} :=
        singularSubspacePairMap (𝟙 (TopCat.of (V i)))
          {u : V i | u.val ∉ euclideanAmbientFixedSet (g i)}
          {u : V i | u.val ∉ ({x.val} : Set _)}
          (by
            intro u hu he
            apply hu
            refine ⟨⟨x.val, hi⟩, ?_, Set.mem_singleton_iff.mp he |>.symm⟩
            exact (show x ∈ euclideanFixedSet f from hKnative ▸ hx))
      let b : euclideanSupportPair n (V i : Set _) {x.val} ⟶
          euclideanSupportPair n (U : Set _) {x.val} :=
        singularSubspacePairMap
          (TopCat.ofHom (⟨fun u : V i ↦ (⟨u.val, hVU i u.property⟩ : U),
            continuous_subtype_val.subtype_mk _⟩ : C(V i, U)))
          {u : V i | u.val ∉ ({x.val} : Set _)}
          {u : U | u.val ∉ ({x.val} : Set _)} (by intro u hu; exact hu)
      have hab : j i ≫ r = a ≫ b := by
        apply MorphismProperty.Arrow.Hom.ext <;>
          change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
            TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ <;>
          rw [← Functor.map_comp, ← Functor.map_comp] <;> rfl
      have hxFi : ({x.val} : Set (EuclideanSpace ℝ (Fin n))) ⊆
          euclideanAmbientFixedSet (g i) := by
        rintro y rfl
        exact ⟨⟨x.val, hi⟩, (show x ∈ euclideanFixedSet f from hKnative ▸ hx), rfl⟩
      have ha := euclideanSupportOrientation_enlargement n (V i : Set _) {x.val}
        (euclideanAmbientFixedSet (g i)) (V i).isOpen isCompact_singleton
        ((hc i).image continuous_subtype_val) hxFi
        (by rintro y ⟨u, hu, rfl⟩; exact u.property)
      have hb := euclideanSupportOrientation_subset_naturality n (V i : Set _)
        (U : Set _) {x.val} (V i).isOpen U.isOpen isCompact_singleton
        (Set.singleton_subset_iff.mpr hi) (hVU i)
      have hr := euclideanSupportOrientation_enlargement n (U : Set _) {x.val}
        (euclideanAmbientFixedSet f) U.isOpen isCompact_singleton
        (hK.image continuous_subtype_val) (Set.singleton_subset_iff.mpr hxF)
        (by rintro y ⟨u, hu, rfl⟩; exact u.property)
      change (SSetPair.homologyMap r reducedSingularIntegralCoefficients n).hom o =
        (SSetPair.homologyMap (j i) reducedSingularIntegralCoefficients n ≫
          SSetPair.homologyMap r reducedSingularIntegralCoefficients n).hom (oi i)
      rw [← SSetPair.homologyMap_comp, hab, SSetPair.homologyMap_comp]
      change (SSetPair.homologyMap r reducedSingularIntegralCoefficients n).hom o =
        (SSetPair.homologyMap b reducedSingularIntegralCoefficients n).hom
          ((SSetPair.homologyMap a reducedSingularIntegralCoefficients n).hom (oi i))
      rw [show (SSetPair.homologyMap a reducedSingularIntegralCoefficients n).hom
        (oi i) = _ from ha]
      exact hr.trans hb.symm
  · constructor
    · intro n U H hH
      have hs := homotopy_slice_fixedSet_compact H hH
      refine ⟨hs 0, hs 1, ?_⟩
      obtain ⟨L, hL, hLU, hfixed, d, hd, ⟨DH⟩⟩ :=
        euclidean_displacement_pair_homotopy H hH
      have hmaps := (relative_singular_homotopy_invariance (ModuleCat ℤ) DH
        reducedSingularIntegralCoefficients).2 n
      let F (t : unitInterval) : C(U, EuclideanSpace ℝ (Fin n)) :=
        H.comp ⟨fun x ↦ (x, t), continuous_id.prodMk continuous_const⟩
      have hKL (t : unitInterval) : euclideanAmbientFixedSet (F t) ⊆ L := by
        rintro _ ⟨x, hx, rfl⟩
        exact hfixed t x hx
      let r (t : unitInterval) : euclideanSupportPair n (U : Set _) L ⟶
          euclideanSupportPair n (U : Set _) (euclideanAmbientFixedSet (F t)) :=
        singularSubspacePairMap (𝟙 (TopCat.of U))
          {x : U | x.val ∉ L} {x : U | x.val ∉ euclideanAmbientFixedSet (F t)}
          (by intro x hx hk; exact hx (hKL t hk))
      have hp (t : unitInterval) : r t ≫ euclideanDisplacementPairMap (F t) =
          singularPairFunctor.map (d t) := by
        apply MorphismProperty.Arrow.Hom.ext
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
          rw [← Functor.map_comp]
          congr 1
          apply TopCat.hom_ext
          apply ContinuousMap.ext
          intro x
          apply Subtype.ext
          exact ((ConcreteCategory.congr_hom (TopPair.Hom.w (d t)) x).trans
            (hd t x.val)).symm
        · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _
          rw [← Functor.map_comp]
          congr 1
          apply TopCat.hom_ext
          apply ContinuousMap.ext
          intro x
          exact (hd t x).symm
      have hcomp (t : unitInterval) :
          SSetPair.homologyMap (r t) reducedSingularIntegralCoefficients n ≫
              euclideanDisplacementHomologyMap (F t) =
            SSetPair.homologyMap (singularPairFunctor.map (d t))
              reducedSingularIntegralCoefficients n := by
        unfold euclideanDisplacementHomologyMap
        rw [← SSetPair.homologyMap_comp, hp]
        rfl
      let o := euclideanSupportOrientation n (U : Set _) L U.isOpen hL hLU
      have hindex (t : unitInterval) :
          euclideanFixedPointIndex (F t) (hs t) =
            euclideanPositiveLocalCoordinate n
              ((SSetPair.homologyMap (singularPairFunctor.map (d t))
                reducedSingularIntegralCoefficients n).hom o) := by
        have hc : IsCompact (euclideanAmbientFixedSet (F t)) :=
          (hs t).image continuous_subtype_val
        have ho := euclideanSupportOrientation_enlargement n (U : Set _)
          (euclideanAmbientFixedSet (F t)) L U.isOpen hc hL (hKL t) hLU
        have he := congrArg (fun q ↦ q.hom o) (hcomp t)
        have hor := congrArg (fun x ↦ (euclideanDisplacementHomologyMap (F t)).hom x) ho
        exact congrArg (euclideanPositiveLocalCoordinate n) (hor.symm.trans he)
      have hcoordinate :
          euclideanPositiveLocalCoordinate n
              ((SSetPair.homologyMap (singularPairFunctor.map (d 0))
                reducedSingularIntegralCoefficients n).hom o) =
            euclideanPositiveLocalCoordinate n
              ((SSetPair.homologyMap (singularPairFunctor.map (d 1))
                reducedSingularIntegralCoefficients n).hom o) :=
        congrArg (fun q ↦ euclideanPositiveLocalCoordinate n (q.hom o)) hmaps
      exact (hindex 0).trans (hcoordinate.trans (hindex 1).symm)
    constructor
    · intro n m U V f g hF hG
      refine ⟨euclidean_product_fixedSet_compact n m U V f g hF hG, ?_⟩
      by_cases hf : euclideanFixedSet f = ∅
      · have hp := euclidean_product_fixedSet_eq_empty n m U V f g (Or.inl hf)
        rw [fixed_index_zero_of_empty _ _ hp, fixed_index_zero_of_empty f hF hf,
          zero_mul]
      · by_cases hg : euclideanFixedSet g = ∅
        · have hp := euclidean_product_fixedSet_eq_empty n m U V f g (Or.inr hg)
          rw [fixed_index_zero_of_empty _ _ hp, fixed_index_zero_of_empty g hG hg,
            mul_zero]
        · exact euclidean_product_fixed_point_index_mul n m U V f g hF hG
            (euclidean_product_fixedSet_compact n m U V f g hF hG)
    have hconstant : ∀ (n : ℕ) (U : Opens (EuclideanSpace ℝ (Fin n)))
        (c : EuclideanSpace ℝ (Fin n)), c ∈ U →
        ∃ hC : IsCompact (euclideanFixedSet (ContinuousMap.const U c)),
          euclideanFixedPointIndex (ContinuousMap.const U c) hC = 1 := by
      intro n U c hc
      refine ⟨constant_fixedSet_compact c hc, ?_⟩
      exact euclidean_constant_fixed_point_index_one c hc
    refine ⟨hconstant, zero_identity_fixedSet_compact, ?_⟩
    -- In dimension zero the actual identity map is the constant map at zero;
    -- the same normalization therefore proves the ordinary H₀ coefficient-one law.
    obtain ⟨hC, hindex⟩ := hconstant 0 ⊤ 0 (by trivial)
    have hmap : (⟨Subtype.val, continuous_subtype_val⟩ :
        C((⊤ : Opens (EuclideanSpace ℝ (Fin 0))), EuclideanSpace ℝ (Fin 0))) =
        ContinuousMap.const (⊤ : Opens (EuclideanSpace ℝ (Fin 0))) 0 := by
      apply ContinuousMap.ext
      intro x
      exact Subsingleton.elim _ _
    simpa only [hmap] using hindex



end HolomorphicAnosov

