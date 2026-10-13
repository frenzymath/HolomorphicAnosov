import HolomorphicAnosov.Topology.EuclideanProductStaircaseIsolation
import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.Homology.IntegralRelativeHomologyProductNaturality
import HolomorphicAnosov.Topology.Homology.IntegralRelativeCrossProductHomologyMap
import HolomorphicAnosov.Topology.EuclideanPositiveLocalClassZeroFreeGenerator
import HolomorphicAnosov.Topology.EmbeddedSimplexLocalClassGenerator
import HolomorphicAnosov.Topology.SignedCrossProductUnitGenerators

/-!
# Nonvanishing of the native Euclidean local homology product

Source: Hatcher §3.B pp.277–278, Example 2.23 p.125 and Theorem 2.20
pp.119–124; Bredon, Topology and Geometry, IV §16.3 pp.221–222.
DAG: `topo.euclidean_local_homology_product_nonzero_g17`.

Take the translated factor simplexes supplied by staircase isolation. Each face
misses zero, hence their coefficient-one chains are relative cycles. The literal
signed chain product, transported to concatenated Euclidean coordinates, is its
finite staircase sum. Every term but the selected one factors through the
punctured space and therefore vanishes in the relative chain quotient. The
remaining coefficient is (-1) to an integer power, hence a unit. The embedded
selected simplex contains zero in its interior, so its local relative class is
primitive and nonzero. The native cycle representative equation for the cross
product identifies its value on the two factor classes with this signed nonzero
class. In dimension zero the coefficient-one point is the specified positive
class, which is also a free generator. No sign normalization is assumed.
-/


noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov
namespace EuclideanIndexProduct

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ordered-coordinate product domain; Dold §1.6, p.2. -/
def domain {n m : ℕ} (U : Opens (E n)) (V : Opens (E m)) : Opens (E (n+m)) :=
  ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ)) ⁻¹' (U ×ˢ V),
    (U.isOpen.prod V.isOpen).preimage EuclideanSpace.finAddEquivProd.continuous⟩

/-- The domain equivalence to the literal product of the factor domains. -/
def domainEquiv {n m : ℕ} (U : Opens (E n)) (V : Opens (E m)) :
    domain U V ≃ₜ U × V where
  toFun x := (⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) x.1).1, x.2.1⟩,
    ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) x.1).2, x.2.2⟩)
  invFun x := ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm (x.1.1,x.2.1), by
    change EuclideanSpace.finAddEquivProd
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm (x.1.1,x.2.1)) ∈ (U : Set (E n)) ×ˢ (V : Set (E m))
    simp⟩
  left_inv x := by
    apply Subtype.ext
    exact (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm_apply_apply x.1
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).apply_symm_apply _)
    · exact congrArg Prod.snd ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).apply_symm_apply _)
  continuous_toFun :=
    (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).continuous.comp
      continuous_subtype_val).fst.subtype_mk _).prodMk
    (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).continuous.comp
      continuous_subtype_val).snd.subtype_mk _)
  continuous_invFun :=
    ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- The product map in the same ordered coordinates. -/
def map {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) : C(domain U V,E (n+m)) :=
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let a : C(domain U V, U) :=
    ⟨fun x ↦ ⟨(e x.1).1,x.2.1⟩,
      (e.continuous.comp continuous_subtype_val).fst.subtype_mk _⟩
  let b : C(domain U V, V) :=
    ⟨fun x ↦ ⟨(e x.1).2,x.2.2⟩,
      (e.continuous.comp continuous_subtype_val).snd.subtype_mk _⟩
  ⟨fun x ↦ e.symm (f (a x),g (b x)),
    e.symm.continuous.comp ((f.continuous.comp a.continuous).prodMk
      (g.continuous.comp b.continuous))⟩

/-- Fixed points correspond under the domain equivalence. -/
theorem fixedSet_iff {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) (x : domain U V) :
    x ∈ euclideanFixedSet (map f g) ↔
      (domainEquiv U V x).1 ∈ euclideanFixedSet f ∧
      (domainEquiv U V x).2 ∈ euclideanFixedSet g := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  change e.symm (f (domainEquiv U V x).1, g (domainEquiv U V x).2) = x.1 ↔ _
  rw [e.symm_apply_eq]
  exact Prod.ext_iff

/-- Displacement commutes with the coordinate equivalence. -/
theorem displacement {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) (x : domain U V) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (euclideanDisplacement (map f g) x) =
      (euclideanDisplacement f (domainEquiv U V x).1,
        euclideanDisplacement g (domainEquiv U V x).2) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  change e (x.1 - e.symm (f (domainEquiv U V x).1, g (domainEquiv U V x).2)) = _
  rw [map_sub, e.apply_symm_apply]
  rfl

/-- Ambient fixed support membership recovers native fixed support membership. -/
theorem mem_ambientFixedSet {n : ℕ} {U : Opens (E n)}
    (f : C(U,E n)) (u : U) :
    u.1 ∈ euclideanAmbientFixedSet f ↔ u ∈ euclideanFixedSet f := by
  constructor
  · rintro ⟨v,hv,hvu⟩
    exact (Subtype.ext hvu : v = u) ▸ hv
  · intro hu
    exact ⟨u,hu,rfl⟩

/-- The support complement in its native open domain. -/
abbrev complement {n : ℕ} {U : Opens (E n)} (f : C(U,E n)) : Set U :=
  {u | u.1 ∉ euclideanAmbientFixedSet f}

/-- Coordinate identification as a map from the product relative support pair. -/
def supportPairMap {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) :
    singularSubspacePair (TopCat.of (U × V))
        (Topology.ProductSubspace (X := TopCat.of U) (Y := TopCat.of V)
          (complement f) (complement g)) ⟶
      euclideanSupportPair (n+m) (domain U V : Set _) (euclideanAmbientFixedSet (map f g)) :=
  singularSubspacePairMap
    (TopCat.ofHom ⟨(domainEquiv U V).symm, (domainEquiv U V).symm.continuous⟩)
    _ _ (by
      intro z hz hfixed
      have h := (fixedSet_iff f g ((domainEquiv U V).symm z)).mp
        ((mem_ambientFixedSet (map f g) _).mp hfixed)
      rw [(domainEquiv U V).apply_symm_apply] at h
      rcases hz with hz | hz
      · exact hz.1 ((mem_ambientFixedSet f _).mpr h.1)
      · exact hz.2 ((mem_ambientFixedSet g _).mpr h.2))

/-- Inverse ordered-coordinate equivalence on the punctured product pair. -/
def coordinatePairMap (n m : ℕ) :
    singularSubspacePair (TopCat.of (E n × E m))
        (Topology.ProductSubspace (X := TopCat.of (E n)) (Y := TopCat.of (E m))
          (({0} : Set (E n))ᶜ) (({0} : Set (E m))ᶜ)) ⟶
      singularSubspacePair (TopCat.of (E (n+m))) (({0} : Set (E (n+m)))ᶜ) :=
  singularSubspacePairMap
    (TopCat.ofHom ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.continuous⟩)
    _ _ (by
      intro z hz heq
      have heq' : (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm z = 0 := heq
      have hz0 : z = 0 := by
        apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.injective
        simpa using heq'
      subst z
      rcases hz with hz | hz
      · exact hz.1 rfl
      · exact hz.2 rfl)

/-- The product of the actual factor displacements on their relative pairs. -/
def productDisplacementPairMap {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) :
    singularSubspacePair (TopCat.of (U × V))
        (Topology.ProductSubspace (X := TopCat.of U) (Y := TopCat.of V)
          (complement f) (complement g)) ⟶
      singularSubspacePair (TopCat.of (E n × E m))
        (Topology.ProductSubspace (X := TopCat.of (E n)) (Y := TopCat.of (E m))
          (({0} : Set (E n))ᶜ) (({0} : Set (E m))ᶜ)) :=
  singularSubspacePairMap
    (Topology.productMap (TopCat.ofHom (euclideanDisplacement f))
      (TopCat.ofHom (euclideanDisplacement g))) _ _ (by
      intro z hz
      rcases hz with hz | hz
      · refine Or.inl ⟨?_,Set.mem_univ _⟩
        intro heq
        apply hz.1
        exact (mem_ambientFixedSet f _).mpr (sub_eq_zero.mp heq).symm
      · refine Or.inr ⟨Set.mem_univ _,?_⟩
        intro heq
        apply hz.2
        exact (mem_ambientFixedSet g _).mpr (sub_eq_zero.mp heq).symm)

/-- Displacement identity in the inverse direction of the domain equivalence. -/
theorem displacement_symm {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) (z : U × V) :
    euclideanDisplacement (map f g) ((domainEquiv U V).symm z) =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm
        (euclideanDisplacement f z.1,euclideanDisplacement g z.2) := by
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).injective
  rw [displacement, (domainEquiv U V).apply_symm_apply]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The displacement square commutes on the literal native singular pairs. -/
theorem displacement_pair_square {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) :
    supportPairMap f g ≫ euclideanDisplacementPairMap (map f g) =
      productDisplacementPairMap f g ≫ coordinatePairMap n m := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (fun h ↦ TopCat.toSSet.map h)
    ext z : 1
    apply Subtype.ext
    exact displacement_symm f g z.1
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg (fun h ↦ TopCat.toSSet.map h)
    ext z : 1
    exact displacement_symm f g z

/-- The existing signed relative chain product descended to relative homology. -/
abbrev cross := Classical.choose Topology.integral_relative_cross_product_homology_map_boundary_descent

/-- Composition on the output of an integral bilinear homology map. -/
def postcompose {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] (L : C →ₗ[ℤ] D) (P : A →ₗ[ℤ] B →ₗ[ℤ] C) :
    A →ₗ[ℤ] B →ₗ[ℤ] D :=
  let q : A →+ (B →ₗ[ℤ] D) :=
    { toFun := fun a ↦ L.comp (P a)
      map_zero' := by ext b; simp
      map_add' := by intro a a'; ext b; simp }
  { toFun := q
    map_add' := q.map_add
    map_smul' := by
      intro k a
      simpa using map_intCast_smul q ℤ ℤ k a }

/-- The signed relative homology cross product, transported into the ordered-coordinate
punctured Euclidean space. -/
def localProduct (n m : ℕ) :
    EuclideanLocalIntegralHomology n →ₗ[ℤ]
      EuclideanLocalIntegralHomology m →ₗ[ℤ] EuclideanLocalIntegralHomology (n+m) :=
  postcompose (SSetPair.homologyMap (coordinatePairMap n m)
    reducedSingularIntegralCoefficients (n+m)).hom
      (cross (TopCat.of (E n)) (TopCat.of (E m)) ({0}ᶜ) ({0}ᶜ) n m)

/-- The signed relative homology product on supported classes, transported to the actual
product open domain. -/
def supportProduct {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m)) :
    (euclideanSupportPair n (U : Set _) (euclideanAmbientFixedSet f)).homology (C := ModuleCat ℤ)
        reducedSingularIntegralCoefficients n →ₗ[ℤ]
      (euclideanSupportPair m (V : Set _) (euclideanAmbientFixedSet g)).homology (C := ModuleCat ℤ)
        reducedSingularIntegralCoefficients m →ₗ[ℤ]
      (euclideanSupportPair (n+m) (domain U V : Set _)
        (euclideanAmbientFixedSet (map f g))).homology (C := ModuleCat ℤ)
        reducedSingularIntegralCoefficients (n+m) :=
  postcompose (SSetPair.homologyMap (supportPairMap f g)
    reducedSingularIntegralCoefficients (n+m)).hom
      (cross (TopCat.of U) (TopCat.of V) (complement f) (complement g) n m)

/-- Naturality identifies the product displacement applied to a product class with the
product of the two displacement images. -/
theorem displacement_product {n m : ℕ} {U : Opens (E n)} {V : Opens (E m)}
    (f : C(U,E n)) (g : C(V,E m))
    (a : (euclideanSupportPair n (U : Set _) (euclideanAmbientFixedSet f)).homology (C := ModuleCat ℤ)
      reducedSingularIntegralCoefficients n)
    (b : (euclideanSupportPair m (V : Set _) (euclideanAmbientFixedSet g)).homology (C := ModuleCat ℤ)
      reducedSingularIntegralCoefficients m) :
    let c := supportProduct f g a b
    (euclideanDisplacementHomologyMap (n := n+m) (U := domain U V) (map f g)).hom c =
      localProduct n m ((euclideanDisplacementHomologyMap (n := n) (U := U) f).hom a)
        ((euclideanDisplacementHomologyMap (n := m) (U := V) g).hom b) := by
  have hsquare := congrArg (fun h ↦ SSetPair.homologyMap h
    reducedSingularIntegralCoefficients (n+m)) (displacement_pair_square f g)
  simp only [SSetPair.homologyMap_comp] at hsquare
  change (SSetPair.homologyMap (supportPairMap f g) reducedSingularIntegralCoefficients (n+m) ≫
    SSetPair.homologyMap (euclideanDisplacementPairMap (map f g))
      reducedSingularIntegralCoefficients (n+m))
    (cross (TopCat.of U) (TopCat.of V) (complement f) (complement g) n m a b) = _
  rw [hsquare]
  have hf : Set.MapsTo (TopCat.ofHom (euclideanDisplacement f)) (complement f)
      ({0} : Set (E n))ᶜ := by
    intro u hu heq
    exact hu ((mem_ambientFixedSet f u).mpr (sub_eq_zero.mp heq).symm)
  have hg : Set.MapsTo (TopCat.ofHom (euclideanDisplacement g)) (complement g)
      ({0} : Set (E m))ᶜ := by
    intro v hv heq
    exact hv ((mem_ambientFixedSet g v).mpr (sub_eq_zero.mp heq).symm)
  have hn := Topology.integralRelativeHomologyProduct_naturality_of_representatives
    cross (Classical.choose_spec Topology.integral_relative_cross_product_homology_map_boundary_descent)
    (TopCat.of U) (TopCat.of V) (TopCat.of (E n)) (TopCat.of (E m))
    (TopCat.ofHom (euclideanDisplacement f)) (TopCat.ofHom (euclideanDisplacement g))
    (complement f) (complement g) ({0}ᶜ) ({0}ᶜ) hf hg n m a b
  exact congrArg (fun c ↦ SSetPair.homologyMap (coordinatePairMap n m)
    reducedSingularIntegralCoefficients (n+m) c) hn

/-- The supported class used in the definition of the index, with the same
compactness and containment witnesses. -/
abbrev fixedOrientation {n : ℕ} {U : Opens (E n)} (f : C(U,E n))
    (hF : IsCompact (euclideanFixedSet f)) :=
  euclideanSupportOrientation n (U : Set _) (euclideanAmbientFixedSet f)
    U.isOpen (hF.image continuous_subtype_val)
    (by rintro x ⟨u,hu,rfl⟩; exact u.property)

end EuclideanIndexProduct
end HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.EuclideanIndexProduct
open HolomorphicAnosov.Topology HolomorphicAnosov.SignedSingularCrossProduct
abbrev localComplex (n : ℕ) := RelativeComplex (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ

theorem simplex_cycle (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (hf : ∀ (i : Fin (n+1)) (a : Convexity.StdSimplex ℝ (Fin n)),
      s (Convexity.StdSimplex.map i.succAbove a) ≠ 0) :
    ((localComplex n).sc n).g.hom (simplexLocalRelativeChain n s) = 0 := by
  cases n with
  | zero =>
    simp [HomologicalComplex.sc, HomologicalComplex.shape]
  | succ n => exact simplexLocalRelativeChain_cycle n s hf

def simplexCycle (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (hf : ∀ (i : Fin (n+1)) (a : Convexity.StdSimplex ℝ (Fin n)),
      s (Convexity.StdSimplex.map i.succAbove a) ≠ 0) : (localComplex n).cycles n :=
  ((localComplex n).sc n).cyclesMk (simplexLocalRelativeChain n s) (simplex_cycle n s hf)

@[simp] theorem i_simplexCycle (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (hf : ∀ (i : Fin (n+1)) (a : Convexity.StdSimplex ℝ (Fin n)),
      s (Convexity.StdSimplex.map i.succAbove a) ≠ 0) :
    (localComplex n).iCycles n (simplexCycle n s hf) = simplexLocalRelativeChain n s :=
  ShortComplex.i_cyclesMk ((localComplex n).sc n) (simplexLocalRelativeChain n s) (simplex_cycle n s hf)

theorem simplexCycle_class (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+2)),EuclideanSpace ℝ (Fin (n+1))))
    (hf : ∀ (i : Fin (n+2)) (a : Convexity.StdSimplex ℝ (Fin (n+1))),
      s (Convexity.StdSimplex.map i.succAbove a) ≠ 0) :
    (localComplex (n+1)).homologyπ (n+1) (simplexCycle (n+1) s hf) =
      simplexLocalRelativeClass n s hf := by
  let S := (localComplex (n+1)).sc (n+1)
  have hc : simplexCycle (n+1) s hf = S.moduleCatCyclesIso.inv
      ⟨simplexLocalRelativeChain (n+1) s,simplex_cycle (n+1) s hf⟩ := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    change (localComplex (n+1)).iCycles (n+1) (simplexCycle (n+1) s hf) = _
    rw [i_simplexCycle]
    exact (congrArg (fun f => f ⟨simplexLocalRelativeChain (n+1) s,
      simplex_cycle (n+1) s hf⟩) S.moduleCatCyclesIso_inv_iCycles).symm
  rw [hc]
  exact congrArg (fun f => f ⟨simplexLocalRelativeChain (n+1) s,
    simplex_cycle (n+1) s hf⟩) S.moduleCatCyclesIso_inv_π

theorem simplexCycle_class_zero
    (s : C(Convexity.StdSimplex ℝ (Fin 1),EuclideanSpace ℝ (Fin 0)))
    (hf : ∀ (i : Fin 1) (a : Convexity.StdSimplex ℝ (Fin 0)),
      s (Convexity.StdSimplex.map i.succAbove a) ≠ 0) :
    (localComplex 0).homologyπ 0 (simplexCycle 0 s hf) = euclideanPositiveLocalClass 0 := by
  let S := (localComplex 0).sc 0
  have hs : s = euclideanPositiveSimplex 0 := Subsingleton.elim _ _
  have hc : simplexCycle 0 s hf = S.moduleCatCyclesIso.inv
      ⟨euclideanPositiveLocalChain 0,euclideanPositiveLocalChain_cycle 0⟩ := by
    apply (ModuleCat.mono_iff_injective S.iCycles).mp inferInstance
    change (localComplex 0).iCycles 0 (simplexCycle 0 s hf) = _
    rw [i_simplexCycle]
    have h := congrArg (fun f => f ⟨euclideanPositiveLocalChain 0,
      euclideanPositiveLocalChain_cycle 0⟩) S.moduleCatCyclesIso_inv_iCycles
    rw [hs]
    exact h.symm
  rw [hc]
  exact congrArg (fun f => f ⟨euclideanPositiveLocalChain 0,
    euclideanPositiveLocalChain_cycle 0⟩) S.moduleCatCyclesIso_inv_π

theorem embedded_simplexCycle_nonzero (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (hemb : _root_.Topology.IsClosedEmbedding s)
    (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior (Set.range s))
    (hf : ∀ (i : Fin (n+1)) (a : Convexity.StdSimplex ℝ (Fin n)),
      s (Convexity.StdSimplex.map i.succAbove a) ≠ 0) :
    (localComplex n).homologyπ n (simplexCycle n s hf) ≠ 0 := by
  cases n with
  | zero =>
    rw [simplexCycle_class_zero]
    intro h
    have hgen := euclideanPositiveLocalClass_zero_free_generator.1
    have heq : (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveLocalClass 0)) 1 =
        (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveLocalClass 0)) 0 := by simp [h]
    exact one_ne_zero (hgen heq)
  | succ n =>
    rw [simplexCycle_class]
    obtain ⟨e,he⟩ := embeddedSimplex_localClass_equiv_provider n s hemb hzero hf
    rw [← he]
    exact fun h => one_ne_zero (e.injective (h.trans e.map_zero.symm))

/-- The native unit chain of a continuous simplex. -/
def unitChain {X : TopCat} (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),X)) : Chain X n :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := singularIntegralCoefficients)
    ((X.toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s)) (ULift.up 1)

theorem unitChain_relative_zero {X : TopCat} (A : Set X) (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),X))
    (hs : ∀ t, s t ∈ A) : relativeProjection X A n (unitChain n s) = 0 := by
  let P := singularSubspacePair X A
  let R := singularIntegralCoefficients
  let t : C(Convexity.StdSimplex ℝ (Fin (n+1)),A) :=
    ⟨fun u => ⟨s u,hs u⟩,s.continuous.subtype_mk _⟩
  let α := ((TopCat.of A).toSSetObjEquiv (Opposite.op ⦋n⦌)).symm t
  have ha : (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ α =
      (X.toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s := by
    apply (X.toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
    ext u
    rfl
  have h : (TopCat.toSSet.obj X).ιChainComplex (R := R)
      ((X.toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s) ≫ (P.chainComplexπ R).f n = 0 := by
    rw [← ha, ← SSet.ι_chainComplexMap_f, Category.assoc]
    change _ ≫ (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0
    rw [P.chainComplex_condition_f]
    simp
  exact congrArg (fun f => f.hom (ULift.up 1)) h

theorem unitChain_map {X Y : TopCat} (f : X ⟶ Y) (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),X)) :
    chainMap f n (unitChain n s) = unitChain n (f.hom.comp s) := by
  have h : (TopCat.toSSet.obj X).ιChainComplex (R := singularIntegralCoefficients)
      ((X.toSSetObjEquiv (Opposite.op ⦋n⦌)).symm s) ≫ chainMap f n =
      (TopCat.toSSet.obj Y).ιChainComplex (R := singularIntegralCoefficients)
        ((Y.toSSetObjEquiv (Opposite.op ⦋n⦌)).symm (f.hom.comp s)) := by
    rw [SSet.ι_chainComplexMap_f]
    rfl
  exact congrArg (fun k => k.hom (ULift.up 1)) h

end HolomorphicAnosov.EuclideanIndexProduct
namespace HolomorphicAnosov.EuclideanIndexProduct
open HolomorphicAnosov.Topology HolomorphicAnosov.SignedSingularCrossProduct
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

/-- The transported relative chain product is the literal signed staircase sum. -/
theorem coordinate_chain_product (p q : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (p+1)),E p))
    (t : C(Convexity.StdSimplex ℝ (Fin (q+1)),E q)) :
    let F := SSetPair.chainComplexMap (coordinatePairMap p q) singularIntegralCoefficients
    F.f (p+q) (integralRelativeChainProduct (TopCat.of (E p)) (TopCat.of (E q))
      ({0}ᶜ) ({0}ᶜ) p q (simplexLocalRelativeChain p s) (simplexLocalRelativeChain q t)) =
    ∑ w ∈ staircases p q, orientation w •
      simplexLocalRelativeChain (p+q) (pairedCoordinateSimplex s t w) := by
  classical
  dsimp only
  let X := TopCat.of (E p)
  let Y := TopCat.of (E q)
  let Z := TopCat.of (E (p+q))
  let A : Set X := {0}ᶜ
  let B : Set Y := {0}ᶜ
  let P := singularSubspacePair (TopCat.of (X × Y)) (ProductSubspace A B)
  let Q := singularSubspacePair Z ({0}ᶜ)
  let R := singularIntegralCoefficients
  let F := coordinatePairMap p q
  have hp : (P.chainComplexπ R).f (p+q) ≫ (SSetPair.chainComplexMap F R).f (p+q) =
      (SSet.chainComplexMap F.hom.right R).f (p+q) ≫ (Q.chainComplexπ R).f (p+q) := by
    simpa [SSetPair.chainComplexFunctorRight,SSetPair.chainComplexπ,
      SSetPair.chainComplexMap,SSet.chainComplexMap,HomologicalComplex.comp_f] using
      (congrArg (fun k => k.f (p+q))
        ((((SSetPair.chainComplexFunctorπ (ModuleCat ℤ)).app R).naturality F))).symm
  change (SSetPair.chainComplexMap F R).f (p+q)
    (integralRelativeChainProduct X Y A B p q
      (relativeProjection X A p (unitChain p s))
      (relativeProjection Y B q (unitChain q t))) = _
  rw [integralRelativeChainProduct_projection]
  change ((P.chainComplexπ R).f (p+q) ≫ (SSetPair.chainComplexMap F R).f (p+q))
    (signedSingularCrossProduct X Y p q (unitChain p s) (unitChain q t)) = _
  rw [hp]
  have hprod : signedSingularCrossProduct X Y p q (unitChain p s) (unitChain q t) =
      simplexProduct X Y ((X.toSSetObjEquiv _).symm s) ((Y.toSSetObjEquiv _).symm t) :=
    signedSingularCrossProduct_unit_generators X Y p q _ _
  rw [hprod]
  change ((SSet.chainComplexMap F.hom.right R).f (p+q) ≫ (Q.chainComplexπ R).f (p+q)).hom
      (∑ w ∈ staircases p q, orientation w •
        ((TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex (R := R)
          (productSimplex X Y w ((X.toSSetObjEquiv _).symm s)
            ((Y.toSSetObjEquiv _).symm t))) (ULift.up 1)) = _
  simp only [map_sum,map_zsmul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  have hunit := unitChain_map
    (TopCat.ofHom ⟨(EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)).symm,
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.continuous⟩) (p+q)
    ((s.comp (firstSimplexMap w)).prodMk (t.comp (secondSimplexMap w)))
  simp only [productSimplex,Equiv.apply_symm_apply]
  convert congrArg ((Q.chainComplexπ R).f (p+q)) hunit using 1 <;> rfl

/-- With the isolated factor simplexes, the relative product has just its selected term. -/
theorem coordinate_chain_product_isolated (p q : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (p+1)),E p))
    (t : C(Convexity.StdSimplex ℝ (Fin (q+1)),E q))
    (hother : ∀ w ∈ staircases p q, w ≠ bottomRight p q →
      ∀ a, pairedCoordinateSimplex s t w a ≠ 0) :
    let F := SSetPair.chainComplexMap (coordinatePairMap p q) singularIntegralCoefficients
    F.f (p+q) (integralRelativeChainProduct (TopCat.of (E p)) (TopCat.of (E q))
      ({0}ᶜ) ({0}ᶜ) p q (simplexLocalRelativeChain p s) (simplexLocalRelativeChain q t)) =
    orientation (bottomRight p q) •
      simplexLocalRelativeChain (p+q) (pairedCoordinateSimplex s t (bottomRight p q)) := by
  dsimp only
  rw [coordinate_chain_product]
  apply Finset.sum_eq_single (bottomRight p q)
  · intro w hw hne
    have h := unitChain_relative_zero (X := TopCat.of (E (p+q))) ({0}ᶜ) (p+q) (pairedCoordinateSimplex s t w)
      (hother w hw hne)
    change simplexLocalRelativeChain (p+q) (pairedCoordinateSimplex s t w) = 0 at h
    rw [h]
    exact zsmul_zero _
  · exact fun h => (h (bottomRight_mem p q)).elim

/-- The local product is nonzero in every pair of dimensions, including zero. -/
theorem localProduct_exists_nonzero (p q : ℕ) :
    ∃ (a : EuclideanLocalIntegralHomology p) (b : EuclideanLocalIntegralHomology q),
      localProduct p q a b ≠ 0 := by
  obtain ⟨s,t,hs,ht,hemb,hzero,hfaces,hother⟩ := exists_isolated_product_simplexes p q
  let ca := simplexCycle p s hs
  let cb := simplexCycle q t ht
  let v := pairedCoordinateSimplex s t (bottomRight p q)
  let cv := simplexCycle (p+q) v hfaces
  let X := TopCat.of (E p)
  let Y := TopCat.of (E q)
  let A : Set X := {0}ᶜ
  let B : Set Y := {0}ᶜ
  let T := RelativeComplex (TopCat.of (X × Y)) (ProductSubspace A B)
  let L := localComplex (p+q)
  let F := SSetPair.chainComplexMap (coordinatePairMap p q) singularIntegralCoefficients
  let r := orientation (bottomRight p q)
  obtain ⟨cc,hcc,hclass⟩ := Classical.choose_spec
    integral_relative_cross_product_homology_map_boundary_descent X Y A B p q ca cb
  have hcycle : HomologicalComplex.cyclesMap F (p+q) cc = r • cv := by
    apply (ModuleCat.mono_iff_injective (L.iCycles (p+q))).mp inferInstance
    have hn := congrArg (fun k => k cc) (HomologicalComplex.cyclesMap_i F (p+q))
    change L.iCycles (p+q) (HomologicalComplex.cyclesMap F (p+q) cc) =
      F.f (p+q) (T.iCycles (p+q) cc) at hn
    rw [hn,hcc]
    change F.f (p+q) (integralRelativeChainProduct X Y A B p q
      ((localComplex p).iCycles p (simplexCycle p s hs))
      ((localComplex q).iCycles q (simplexCycle q t ht))) = _
    rw [i_simplexCycle,i_simplexCycle]
    rw [map_zsmul]
    change _ = r • ((localComplex (p+q)).iCycles (p+q) (simplexCycle (p+q) v hfaces))
    rw [i_simplexCycle]
    exact coordinate_chain_product_isolated p q s t hother
  refine ⟨(localComplex p).homologyπ p ca,(localComplex q).homologyπ q cb,?_⟩
  change (HomologicalComplex.homologyMap F (p+q))
    (cross X Y A B p q ((localComplex p).homologyπ p ca)
      ((localComplex q).homologyπ q cb)) ≠ 0
  rw [hclass]
  have hn := congrArg (fun k => k cc) (HomologicalComplex.homologyπ_naturality F (p+q))
  change (HomologicalComplex.homologyMap F (p+q)) (T.homologyπ (p+q) cc) =
    L.homologyπ (p+q) (HomologicalComplex.cyclesMap F (p+q) cc) at hn
  rw [hn,hcycle,map_zsmul]
  intro h
  have hnonzero := embedded_simplexCycle_nonzero (p+q) v hemb hzero hfaces
  have hr : r * r = 1 := by
    dsimp [r,orientation]
    rw [← mul_pow]
    simp
  apply hnonzero
  have hh := congrArg (fun x => r • x) h
  rw [smul_smul,hr,one_smul] at hh
  exact hh.trans (zsmul_zero _)

end HolomorphicAnosov.EuclideanIndexProduct

