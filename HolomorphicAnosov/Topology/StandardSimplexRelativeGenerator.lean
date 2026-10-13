import HolomorphicAnosov.Topology.ContractibleSubspaceHomologyProjection
import HolomorphicAnosov.Topology.RelativeHomologyCollapseComparison
import HolomorphicAnosov.Topology.StandardSimplexFaceUnionCollar
import HolomorphicAnosov.Topology.StdSimplexOneBoundaryEndpoints
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.Disconnected_first_boundary_zero
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

/-!
# The standard simplex relative generator provider

DAG node: `topo.standard_simplex_relative_generator_g20`.
Source: Hatcher, *Algebraic Topology*, Example 2.23 p.125. The identity
simplex is the coefficient-one generator of the relative pair `(Δ^d,∂Δ^d)`.
The proof starts with the interval endpoint difference and inducts by the
connecting map and the omitted facet. Explicit radial collars justify the
good-pair comparison; the alternating chain formula fixes the sign.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- The coefficient-one identity simplex projected to the relative chain pair.
Source: Hatcher pp.108 and 115. -/
def standardSimplexIdentityChain (n : ℕ) :
    ((singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      (standardSimplexBoundary n)).chainComplex reducedSingularIntegralCoefficients).X (n + 1) :=
  ((singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      (standardSimplexBoundary n)).chainComplexπ reducedSingularIntegralCoefficients).f (n + 1)
    (((TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))).ιChainComplex
      (R := reducedSingularIntegralCoefficients)
      (((TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))).toSSetObjEquiv _).symm
        (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 2)))))) (ULift.up 1))

/-- Every face of the identity simplex lies in the standard boundary. -/
theorem standardSimplexIdentityChain_cycle (n : ℕ) :
    let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
    let P := singularSubspacePair X (standardSimplexBoundary n)
    let K := P.chainComplex reducedSingularIntegralCoefficients
    (K.sc (n + 1)).g.hom (standardSimplexIdentityChain n) = 0 := by
  classical
  dsimp only
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let A : Set X := standardSimplexBoundary n
  let P := singularSubspacePair X A
  let R := reducedSingularIntegralCoefficients
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm
    (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 2))))
  have hface (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
      X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t ∈ A := by
    refine ⟨i, ?_⟩
    change (Convexity.StdSimplex.map i.succAbove t).weights i = 0
    rw [Convexity.StdSimplex.weights_map]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  have hkill (i : Fin (n + 2)) :
      (TopCat.toSSet.obj X).ιChainComplex (R := R) ((TopCat.toSSet.obj X).δ i σ) ≫
        (P.chainComplexπ R).f n = 0 := by
    let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
      ⟨fun t ↦ ⟨X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t, hface i t⟩,
        (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)).continuous.subtype_mk _⟩
    let α := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm τ
    have hα : (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ α =
        (TopCat.toSSet.obj X).δ i σ := by
      apply (X.toSSetObjEquiv _).injective
      ext t
      rfl
    rw [← hα, ← SSet.ι_chainComplexMap_f, Category.assoc]
    change _ ≫ (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0
    rw [P.chainComplex_condition_f]
    simp
  change (P.chainComplex R).d (n + 1) ((ComplexShape.down ℕ).next (n + 1))
    ((P.chainComplexπ R).f (n + 1)
      (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) (ULift.up 1))) = 0
  rw [ChainComplex.next_nat_succ]
  have hm : (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      (P.chainComplexπ R).f (n + 1) ≫ (P.chainComplex R).d (n + 1) n = 0 := by
    rw [(P.chainComplexπ R).comm]
    change (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ (P.chainComplexπ R).f n = 0
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hkill, smul_zero,
      Finset.sum_const_zero]
  exact congrArg (fun f ↦ f.hom (ULift.up 1)) hm

/-- The native cycle class of the coefficient-one identity simplex. -/
def standardSimplexIdentityClass (n : ℕ) :
    (singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      (standardSimplexBoundary n)).homology (C := ModuleCat ℤ)
        reducedSingularIntegralCoefficients (n + 1) :=
  let K := (singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      (standardSimplexBoundary n)).chainComplex reducedSingularIntegralCoefficients
  (K.sc (n + 1)).moduleCatHomologyIso.inv
    ((K.sc (n + 1)).moduleCatLeftHomologyData.π
      ⟨standardSimplexIdentityChain n, standardSimplexIdentityChain_cycle n⟩)

/-- The boundary with the interior of the zeroth facet omitted. -/
def standardSimplexHorn (n : ℕ) : Set (Convexity.StdSimplex ℝ (Fin (n + 2))) :=
  {t | ∃ i, i ≠ 0 ∧ t.weights i = 0}

/-- Linear interpolation with a vertex, continuous jointly in time and point. -/
def standardSimplexVertexHomotopy (n : ℕ) :
    (ContinuousMap.id (Convexity.StdSimplex ℝ (Fin (n + 2)))).Homotopy
      (ContinuousMap.const _ (Convexity.StdSimplex.single 0)) where
  toFun p := Convexity.convexCombPair (R := ℝ) (1 - (p.1 : ℝ)) (p.1 : ℝ)
    (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring) p.2
    (Convexity.StdSimplex.single 0)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 2))).continuous_iff]
    apply continuous_pi
    intro i
    simp only [Function.comp_def, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((Convexity.StdSimplex.continuous_weights_apply ℝ i).comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
  map_zero_left := by intro x; simp
  map_one_left := by intro x; simp

/-- The straight-line contraction to vertex zero preserves the horn: a zero
coordinate with nonzero index stays zero throughout the segment. -/
theorem standardSimplexVertexHomotopy_mem_horn (n : ℕ) (t : unitInterval)
    (x : Convexity.StdSimplex ℝ (Fin (n + 2))) (hx : x ∈ standardSimplexHorn n) :
    standardSimplexVertexHomotopy n (t, x) ∈ standardSimplexHorn n := by
  obtain ⟨i, hi, hx⟩ := hx
  refine ⟨i, hi, ?_⟩
  change (Convexity.convexCombPair (R := ℝ) (1 - (t : ℝ)) (t : ℝ) _ _ _ x
    (Convexity.StdSimplex.single 0)).weights i = 0
  simp [Convexity.StdSimplex.weights_convexCombPair,
    Convexity.StdSimplex.weights_single, hi, hx]

/-- The standard simplex contracts by its straight segments. -/
theorem standardSimplex_contractible (n : ℕ) :
    ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n + 2))) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨_, ⟨standardSimplexVertexHomotopy n⟩⟩

/-- The horn contracts to vertex zero by the same straight segments. -/
theorem standardSimplexHorn_contractible (n : ℕ) :
    ContractibleSpace (standardSimplexHorn n) := by
  let v : standardSimplexHorn n := ⟨Convexity.StdSimplex.single 0,
    ⟨1, by simp, by simp [Convexity.StdSimplex.weights_single]⟩⟩
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨v, ⟨{
    toFun := fun p ↦ ⟨standardSimplexVertexHomotopy n (p.1, p.2.1),
      standardSimplexVertexHomotopy_mem_horn n p.1 p.2.1 p.2.2⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · exact ((standardSimplexVertexHomotopy n).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · intro x; apply Subtype.ext; exact (standardSimplexVertexHomotopy n).map_zero_left x.val
  · intro x; apply Subtype.ext; exact (standardSimplexVertexHomotopy n).map_one_left x.val

/-- The omitted-facet horn is contained in the boundary. -/
theorem standardSimplexHorn_subset_boundary (n : ℕ) :
    standardSimplexHorn n ⊆ standardSimplexBoundary n := by
  rintro x ⟨i, _, hi⟩
  exact ⟨i, hi⟩

/-- The same horn viewed as a subspace of the boundary. -/
def standardSimplexBoundaryHorn (n : ℕ) : Set (standardSimplexBoundary n) :=
  {x | x.val ∈ standardSimplexHorn n}

/-- Removing an extra subtype layer identifies the intrinsic and ambient horns. -/
def standardSimplexBoundaryHornHomeomorph (n : ℕ) :
    standardSimplexBoundaryHorn n ≃ₜ standardSimplexHorn n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, standardSimplexHorn_subset_boundary n x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The boundary-to-horn projection is invertible in positive homological
 degrees, because the horn is contractible. -/
theorem standardSimplexBoundary_horn_projection_isIso (n k : ℕ) (hk : 0 < k) :
    IsIso ((singularSubspacePair (TopCat.of (standardSimplexBoundary n))
      (standardSimplexBoundaryHorn n)).homologyπ reducedSingularIntegralCoefficients k) := by
  have := standardSimplexHorn_contractible n
  have := (standardSimplexBoundaryHornHomeomorph n).contractibleSpace
  exact contractible_subspace_homology_projection_isIso _ _ _ k hk

/-- In dimensions at least two, the connecting map of the simplex-boundary
pair is invertible: both adjacent positive homology groups of the simplex
vanish by the explicit contraction. -/
theorem standardSimplexBoundary_connecting_isIso (n : ℕ) :
    IsIso ((singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 3))))
      (standardSimplexBoundary (n + 1))).homologyδ
        reducedSingularIntegralCoefficients (n + 2) (n + 1)) := by
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 3)))
  let P := singularSubspacePair X (standardSimplexBoundary (n + 1))
  have : ContractibleSpace X := standardSimplex_contractible (n + 1)
  have hz (k : ℕ) (hk : k ≠ 0) :
      IsZero ((TopCat.toSSet.obj X).homology reducedSingularIntegralCoefficients k) :=
    singular_homology_isZero_of_contractible X reducedSingularIntegralCoefficients k hk
  change IsIso ((P.shortExact_chainComplexShortComplex _).δ (n + 2) (n + 1) _)
  exact (P.shortExact_chainComplexShortComplex _).isIso_δ
    (n + 2) (n + 1) (by simp) (hz _ (by omega)) (hz _ (by omega))

/-- Each affine face, with its codomain restricted to the boundary. -/
def standardSimplexBoundaryFace (n : ℕ) (i : Fin (n + 2)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), standardSimplexBoundary n) where
  toFun t := ⟨Convexity.StdSimplex.map i.succAbove t, i, by
    rw [Convexity.StdSimplex.weights_map]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)⟩
  continuous_toFun := (Convexity.StdSimplex.continuous_map ℝ _).subtype_mk _

/-- The singular simplex of an affine boundary face. -/
def standardSimplexBoundaryFaceSSet (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary n))) _⦋n⦌ :=
  ((TopCat.of (standardSimplexBoundary n)).toSSetObjEquiv _).symm
    (standardSimplexBoundaryFace n i)

/-- The alternating boundary of the identity, now an actual chain in the
boundary subspace. -/
def standardSimplexBoundaryChain (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary n))).chainComplex
      reducedSingularIntegralCoefficients).X n :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary n))).ιChainComplex
      (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet n i))
        (ULift.up 1)

/-- Inclusion takes each boundary face to the corresponding face of the
identity singular simplex. -/
theorem standardSimplexBoundaryFaceSSet_inclusion (n : ℕ) (i : Fin (n + 2)) :
    (TopCat.toSSet.map (singularSubspaceInclusion
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      (standardSimplexBoundary n))).app _ (standardSimplexBoundaryFaceSSet n i) =
    (TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))).δ i
      (((TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))).toSSetObjEquiv _).symm
        (ContinuousMap.id _)) := by
  apply (TopCat.toSSetObjEquiv _ _).injective
  ext t
  rfl

/-- Every face other than the zeroth face lies in the horn, so its relative
chain projection vanishes. -/
theorem standardSimplexBoundaryFace_horn_zero (n : ℕ) (i : Fin (n + 2)) (hi : i ≠ 0) :
    (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary n))).ιChainComplex
      (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet n i) ≫
    ((singularSubspacePair (TopCat.of (standardSimplexBoundary n))
      (standardSimplexBoundaryHorn n)).chainComplexπ reducedSingularIntegralCoefficients).f n = 0 := by
  let X := TopCat.of (standardSimplexBoundary n)
  let A := standardSimplexBoundaryHorn n
  let P := singularSubspacePair X A
  let R := reducedSingularIntegralCoefficients
  let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun t ↦ ⟨standardSimplexBoundaryFace n i t, i, hi, by
      change (Convexity.StdSimplex.map i.succAbove t).weights i = 0
      rw [Convexity.StdSimplex.weights_map]
      exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)⟩,
      (standardSimplexBoundaryFace n i).continuous.subtype_mk _⟩
  let α := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm τ
  have hα : (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ α =
      standardSimplexBoundaryFaceSSet n i := by
    apply (X.toSSetObjEquiv _).injective
    ext t
    rfl
  rw [← hα, ← SSet.ι_chainComplexMap_f, Category.assoc]
  change _ ≫ (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0
  rw [P.chainComplex_condition_f]
  simp

/-- Modulo the horn, the alternating boundary is exactly the coefficient-one
zeroth facet. Its sign is positive because its index is zero. -/
theorem standardSimplexBoundaryChain_horn_projection (n : ℕ) :
    ((singularSubspacePair (TopCat.of (standardSimplexBoundary n))
      (standardSimplexBoundaryHorn n)).chainComplexπ reducedSingularIntegralCoefficients).f n
        (standardSimplexBoundaryChain n) =
    ((singularSubspacePair (TopCat.of (standardSimplexBoundary n))
      (standardSimplexBoundaryHorn n)).chainComplexπ reducedSingularIntegralCoefficients).f n
      (((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary n))).ιChainComplex
        (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet n 0))
          (ULift.up 1)) := by
  classical
  unfold standardSimplexBoundaryChain
  simp only [map_sum, map_zsmul]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    have h := congrArg (fun f ↦ f.hom (ULift.up 1))
      (standardSimplexBoundaryFace_horn_zero n i hi)
    change _ = 0 at h
    exact (congrArg (fun z ↦ (-1 : ℤ) ^ i.val • z) h).trans (zsmul_zero _)
  · simp

/-- The simplex-boundary pair is a good pair, with the explicit radial collar. -/
theorem standardSimplexBoundary_collapse_isIso (n k : ℕ) (R : ModuleCat ℤ) :
    IsIso (SSetPair.homologyMap
      (GoodPair.collapseSingularPairMap
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))) (standardSimplexBoundary n)) R k) := by
  let s : Finset (Fin (n + 2)) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have hA : standardSimplexFaceUnion n s = standardSimplexBoundary n := by
    ext x
    simp [standardSimplexFaceUnion, standardSimplexBoundary, s]
  rw [← hA]
  apply GoodPair.collapse_homology_isIso_of_good_pair
    _ _ (standardSimplexFaceUnionCollar n s hs)
    (hA.symm ▸ standardSimplexBoundary_nonempty n)
    (standardSimplexFaceUnion_closed n s) (standardSimplexFaceUnion_subset_collar n s hs)
    _ (standardSimplexFaceUnionRetract n s hs) R k
  rw [(standardSimplexFaceUnionCollar_open n s hs).interior_eq]
  exact standardSimplexFaceUnion_subset_collar n s hs

lemma standardSimplexHorn_closed (n : ℕ) : IsClosed (standardSimplexHorn n) := by
  have he : standardSimplexFaceUnion n (Finset.univ.erase 0) = standardSimplexHorn n := by
    ext x
    simp [standardSimplexFaceUnion, standardSimplexHorn]
  rw [← he]
  exact standardSimplexFaceUnion_closed n _

lemma standardSimplexBoundaryHorn_closed (n : ℕ) : IsClosed (standardSimplexBoundaryHorn n) :=
  (standardSimplexHorn_closed n).preimage continuous_subtype_val

lemma standardSimplexBoundaryHorn_nonempty (n : ℕ) : (standardSimplexBoundaryHorn n).Nonempty := by
  have h : Convexity.StdSimplex.single (R := ℝ) (0 : Fin (n + 2)) ∈ standardSimplexHorn n :=
    ⟨1, by simp, by simp [Convexity.StdSimplex.weights_single]⟩
  exact ⟨⟨_, standardSimplexHorn_subset_boundary n h⟩, h⟩

/-- The horn is a good subspace of the boundary, using the restricted radial collar. -/
theorem standardSimplexBoundaryHorn_collapse_isIso (n k : ℕ) (R : ModuleCat ℤ) :
    IsIso (SSetPair.homologyMap
      (GoodPair.collapseSingularPairMap (TopCat.of (standardSimplexBoundary n))
        (standardSimplexBoundaryHorn n)) R k) := by
  let s : Finset (Fin (n + 2)) := Finset.univ.erase 0
  have hs : s.Nonempty := ⟨1, by simp [s]⟩
  let A : Set (standardSimplexBoundary n) :=
    fun x ↦ x.val ∈ standardSimplexFaceUnion n s
  let V : Set (standardSimplexBoundary n) :=
    fun x ↦ x.val ∈ standardSimplexFaceUnionCollar n s hs
  have hA : A = standardSimplexBoundaryHorn n := by
    ext x
    change (∃ i ∈ s, x.val.weights i = 0) ↔ ∃ i, i ≠ 0 ∧ x.val.weights i = 0
    simp [s]
  have hAV : A ⊆ V := fun _ hx ↦ standardSimplexFaceUnion_subset_collar n s hs hx
  have hV : IsOpen V :=
    (standardSimplexFaceUnionCollar_open n s hs).preimage continuous_subtype_val
  rw [← hA]
  apply GoodPair.collapse_homology_isIso_of_good_pair _ _ V
    (hA.symm ▸ standardSimplexBoundaryHorn_nonempty n)
    (hA.symm ▸ standardSimplexBoundaryHorn_closed n) hAV _
    (standardSimplexBoundaryFaceUnionRetract n s hs) R k
  rw [hV.interior_eq]
  exact hAV

lemma standardSimplexBoundaryFace_zero_weights (n : ℕ)
    (x : Convexity.StdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    (standardSimplexBoundaryFace n 0 x).val.weights i.succ = x.weights i := by
  change (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2))) x).weights i.succ = _
  simp only [Convexity.StdSimplex.weights_map, Fin.succAbove_zero]
  exact Finsupp.mapDomain_apply_of_injective (Fin.succ_injective _) _ _

lemma standardSimplexBoundaryFace_zero_injective (n : ℕ) :
    Function.Injective (standardSimplexBoundaryFace n 0) := by
  intro x y h
  ext i
  have hw := congrArg (fun z ↦ z.val.weights i.succ) h
  simpa only [standardSimplexBoundaryFace_zero_weights] using hw

lemma standardSimplexBoundaryFace_zero_mem_horn_iff (n : ℕ)
    (x : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    standardSimplexBoundaryFace (n + 1) 0 x ∈ standardSimplexBoundaryHorn (n + 1) ↔
      x ∈ standardSimplexBoundary n := by
  constructor
  · rintro ⟨i, hi, hw⟩
    obtain ⟨j, rfl⟩ := (Fin.eq_zero_or_eq_succ i).resolve_left hi
    exact ⟨j, (standardSimplexBoundaryFace_zero_weights (n + 1) x j).symm.trans hw⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.succ, Fin.succ_ne_zero i,
      (standardSimplexBoundaryFace_zero_weights (n + 1) x i).trans hi⟩

lemma standardSimplexBoundaryFace_zero_cover (n : ℕ) (y : standardSimplexBoundary n) :
    y ∈ standardSimplexBoundaryHorn n ∨ y ∈ Set.range (standardSimplexBoundaryFace n 0) := by
  obtain ⟨i, hi⟩ := y.property
  by_cases hi0 : i = 0
  · right
    subst i
    have hyr : y.val ∈ Set.range (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2)))) := by
      apply (Convexity.StdSimplex.mem_range_map_iff _ _).mpr
      intro j hj
      have hj0 : j = 0 := by
        by_contra hne
        obtain ⟨k, rfl⟩ := (Fin.eq_zero_or_eq_succ j).resolve_left hne
        exact hj ⟨k, by simp⟩
      simpa [hj0] using hi
    obtain ⟨x, hx⟩ := hyr
    exact ⟨x, Subtype.ext hx⟩
  · exact Or.inl ⟨i, hi0, hi⟩

/-- Inclusion of the omitted facet is the induction comparison on relative
homology. Both source and target collapse maps are isomorphisms, and after
collapse the facet is a homeomorphism by the closed-embedding comparison. -/
theorem standardSimplexBoundaryFace_zero_homology_isIso (n k : ℕ) (R : ModuleCat ℤ) :
    IsIso (SSetPair.homologyMap
      (singularSubspacePairMap (TopCat.ofHom (standardSimplexBoundaryFace (n + 1) 0))
        (standardSimplexBoundary n) (standardSimplexBoundaryHorn (n + 1))
        (fun x hx ↦ (standardSimplexBoundaryFace_zero_mem_horn_iff n x).mpr hx)) R k) := by
  have : T2Space (Convexity.StdSimplex ℝ (Fin (n + 3))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  have := standardSimplexBoundary_collapse_isIso n k R
  have := standardSimplexBoundaryHorn_collapse_isIso (n + 1) k R
  apply relative_homology_isIso_of_collapse_comparison
    (standardSimplexBoundaryFace (n + 1) 0) (standardSimplexBoundary n)
    (standardSimplexBoundaryHorn (n + 1)) _
    ((standardSimplexBoundaryFace (n + 1) 0).continuous.isClosedEmbedding
      (standardSimplexBoundaryFace_zero_injective (n + 1)))
    (standardSimplexBoundary_nonempty n) (standardSimplexBoundaryHorn_closed (n + 1))
    (fun x hx ↦ (standardSimplexBoundaryFace_zero_mem_horn_iff n x).mp hx)
    (standardSimplexBoundaryFace_zero_cover (n + 1)) R k

/-- The coefficient-one identity chain before the relative quotient. -/
def standardSimplexAbsoluteChain (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))).chainComplex
      reducedSingularIntegralCoefficients).X (n + 1) :=
  ((TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))).ιChainComplex
      (R := reducedSingularIntegralCoefficients)
      (((TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))).toSSetObjEquiv _).symm
        (ContinuousMap.id _))) (ULift.up 1)

attribute [-instance] AddCommGroup.toIntModule in
/-- The alternating face chain lifts the literal boundary of the identity
chain to the boundary subspace. -/
theorem standardSimplexBoundaryChain_inclusion (n : ℕ) :
    (SSet.chainComplexMap (singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      (standardSimplexBoundary n)).hom reducedSingularIntegralCoefficients).f n
        (standardSimplexBoundaryChain n) =
    ((TopCat.toSSet.obj (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))).chainComplex
      reducedSingularIntegralCoefficients).d (n + 1) n (standardSimplexAbsoluteChain n) := by
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let Y := TopCat.of (standardSimplexBoundary n)
  let R := reducedSingularIntegralCoefficients
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (ContinuousMap.id _)
  let i := TopCat.toSSet.map (singularSubspaceInclusion X (standardSimplexBoundary n))
  have h : (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      (TopCat.toSSet.obj Y).ιChainComplex (R := R) (standardSimplexBoundaryFaceSSet n j)) ≫
      (SSet.chainComplexMap i R).f n =
      (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n := by
    rw [SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f]
    apply Finset.sum_congr rfl
    intro j _
    rw [standardSimplexBoundaryFaceSSet_inclusion]
  have hsmul (a : ℤ) (f : R →ₗ[ℤ] ((TopCat.toSSet.obj Y).chainComplex R).X n) :
      (a • f) (ULift.up 1) = a • f (ULift.up 1) :=
    (LinearMap.evalAddMonoidHom (ULift.up 1)).map_zsmul a f
  have hh := congrArg (fun f ↦ f.hom (ULift.up 1)) h
  change (SSet.chainComplexMap i R).f n
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      ((TopCat.toSSet.obj Y).ιChainComplex (R := R) (standardSimplexBoundaryFaceSSet n j)).hom
        (ULift.up 1)) =
    (((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ).hom (ULift.up 1))
  simpa only [hsmul, ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.comp_apply, LinearMap.sum_apply, map_sum, map_zsmul] using hh

/-- The lifted alternating boundary is a cycle because inclusion is injective
and its image is a boundary. -/
theorem standardSimplexBoundaryChain_cycle (n : ℕ) :
    ((((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary n))).chainComplex
      reducedSingularIntegralCoefficients).sc n).g).hom (standardSimplexBoundaryChain n) = 0 := by
  let P := singularSubspacePair
    (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))) (standardSimplexBoundary n)
  let R := reducedSingularIntegralCoefficients
  exact (P.shortExact_chainComplexShortComplex R).d_eq_zero_of_f_eq_d_apply
    (n + 1) n (standardSimplexAbsoluteChain n) (standardSimplexBoundaryChain n)
    (standardSimplexBoundaryChain_inclusion n) ((ComplexShape.down ℕ).next n)

/-- The relative connecting map sends the identity class to its alternating
boundary class, with the positive sign of the native exact sequence. -/
theorem standardSimplexIdentityClass_connecting (n : ℕ) :
    (singularSubspacePair
      (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))) (standardSimplexBoundary n)).homologyδ
      reducedSingularIntegralCoefficients (n + 1) n rfl (standardSimplexIdentityClass n) =
    GoodPair.integralChainCycleClass
      ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary n))).chainComplex
        reducedSingularIntegralCoefficients) n
      ⟨standardSimplexBoundaryChain n, standardSimplexBoundaryChain_cycle n⟩ := by
  let P := singularSubspacePair
    (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))) (standardSimplexBoundary n)
  let R := reducedSingularIntegralCoefficients
  change P.homologyδ R (n + 1) n rfl
    (GoodPair.integralChainCycleClass (P.chainComplex R) (n + 1)
      ⟨standardSimplexIdentityChain n, standardSimplexIdentityChain_cycle n⟩) = _
  rw [GoodPair.integralChainCycleClass_eq_cyclesMk, GoodPair.integralChainCycleClass_eq_cyclesMk]
  have hc : (P.chainComplex R).d (n + 1) n (standardSimplexIdentityChain n) = 0 := by
    have h := standardSimplexIdentityChain_cycle n
    change (P.chainComplex R).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) _ = 0 at h
    rw [ChainComplex.next_nat_succ] at h
    exact h
  exact (P.shortExact_chainComplexShortComplex R).δ_apply (n + 1) n (by simp)
    (standardSimplexIdentityChain n) hc (standardSimplexAbsoluteChain n) rfl
    (standardSimplexBoundaryChain n) (standardSimplexBoundaryChain_inclusion n)
    ((ComplexShape.down ℕ).next n) rfl

/-- The omitted facet as a map of native singular pairs. -/
def standardSimplexFacetPairMap (n : ℕ) :
    singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
      (standardSimplexBoundary n) ⟶
    singularSubspacePair (TopCat.of (standardSimplexBoundary (n + 1)))
      (standardSimplexBoundaryHorn (n + 1)) :=
  singularSubspacePairMap (TopCat.ofHom (standardSimplexBoundaryFace (n + 1) 0))
    (standardSimplexBoundary n) (standardSimplexBoundaryHorn (n + 1))
    (fun x hx ↦ (standardSimplexBoundaryFace_zero_mem_horn_iff n x).mpr hx)

/-- The facet pair map takes the identity chain to the surviving face of the
alternating boundary. This uses naturality of the actual quotient projection. -/
theorem standardSimplexFacetPairMap_identityChain (n : ℕ) :
    (SSetPair.chainComplexMap (standardSimplexFacetPairMap n)
      reducedSingularIntegralCoefficients).f (n + 1) (standardSimplexIdentityChain n) =
    ((singularSubspacePair (TopCat.of (standardSimplexBoundary (n + 1)))
      (standardSimplexBoundaryHorn (n + 1))).chainComplexπ reducedSingularIntegralCoefficients).f (n + 1)
        (standardSimplexBoundaryChain (n + 1)) := by
  let f := standardSimplexFacetPairMap n
  let R := reducedSingularIntegralCoefficients
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2)))
  let Y := TopCat.of (standardSimplexBoundary (n + 1))
  let P := singularSubspacePair X (standardSimplexBoundary n)
  let Q := singularSubspacePair Y (standardSimplexBoundaryHorn (n + 1))
  rw [standardSimplexBoundaryChain_horn_projection]
  change ((P.chainComplexπ R).f (n + 1) ≫ (SSetPair.chainComplexMap f R).f (n + 1))
    (standardSimplexAbsoluteChain n) = _
  rw [pair_projection_naturality]
  change (Q.chainComplexπ R).f (n + 1)
      (((SSet.chainComplexMap f.right R).f (n + 1)) (standardSimplexAbsoluteChain n)) = _
  apply congrArg ((Q.chainComplexπ R).f (n + 1))
  change ((TopCat.toSSet.obj X).ιChainComplex (R := R)
      ((X.toSSetObjEquiv _).symm (ContinuousMap.id _)) ≫
      (SSet.chainComplexMap f.right R).f (n + 1)) (ULift.up 1) = _
  rw [SSet.ι_chainComplexMap_f]
  congr 2

/-- The connecting map followed by projection modulo the horn agrees on the
identity class with the actual homology map of the omitted facet. -/
theorem standardSimplexIdentityClass_facet_step (n : ℕ) :
    ((singularSubspacePair (TopCat.of (standardSimplexBoundary (n + 1)))
      (standardSimplexBoundaryHorn (n + 1))).homologyπ reducedSingularIntegralCoefficients (n + 1))
      (((singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 3))))
        (standardSimplexBoundary (n + 1))).homologyδ
        reducedSingularIntegralCoefficients (n + 2) (n + 1)) (standardSimplexIdentityClass (n + 1))) =
    SSetPair.homologyMap (standardSimplexFacetPairMap n)
      reducedSingularIntegralCoefficients (n + 1) (standardSimplexIdentityClass n) := by
  rw [standardSimplexIdentityClass_connecting]
  let R := reducedSingularIntegralCoefficients
  let Q := singularSubspacePair (TopCat.of (standardSimplexBoundary (n + 1)))
    (standardSimplexBoundaryHorn (n + 1))
  let c := standardSimplexBoundaryChain (n + 1)
  let w := (Q.chainComplexπ R).f (n + 1) c
  have hw : ((Q.chainComplex R).sc (n + 1)).g.hom w = 0 := by
    change (Q.chainComplex R).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) _ = 0
    have hc := standardSimplexBoundaryChain_cycle (n + 1)
    change (Q.right.chainComplex R).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c = 0 at hc
    change ((Q.chainComplexπ R).f (n + 1) ≫
      (Q.chainComplex R).d (n + 1) ((ComplexShape.down ℕ).next (n + 1))) c = 0
    rw [(Q.chainComplexπ R).comm]
    change (Q.chainComplexπ R).f _ ((Q.right.chainComplex R).d _ _ c) = 0
    rw [hc, map_zero]
  have hleft := GoodPair.shortComplex_homologyMap_cycle
    ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map (Q.chainComplexπ R))
    ⟨c, standardSimplexBoundaryChain_cycle (n + 1)⟩ ⟨w, hw⟩ rfl
  have hright := GoodPair.shortComplex_homologyMap_cycle
    ((HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map
      (SSetPair.chainComplexMap (standardSimplexFacetPairMap n) R))
    ⟨standardSimplexIdentityChain n, standardSimplexIdentityChain_cycle n⟩ ⟨w, hw⟩
    (standardSimplexFacetPairMap_identityChain n)
  exact hleft.trans hright.symm

/-- The boundary of the interval consists of its two vertices. -/
lemma standardSimplexBoundary_zero_vertices (x : standardSimplexBoundary 0) :
    x.val = Convexity.StdSimplex.single 0 ∨ x.val = Convexity.StdSimplex.single 1 := by
  apply HolomorphicAnosov.Topology.stdSimplexOne_boundary_endpoints
  intro h
  obtain ⟨i, hi⟩ := x.property
  exact (ne_of_gt (h i)) hi

lemma standardSimplexBoundary_zero_finite : Finite (standardSimplexBoundary 0) := by
  have hsub : standardSimplexBoundary 0 ⊆
      {Convexity.StdSimplex.single (R := ℝ) (0 : Fin 2), Convexity.StdSimplex.single 1} := by
    intro x hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      standardSimplexBoundary_zero_vertices ⟨x, hx⟩
  exact ((Set.finite_singleton _).insert _ |>.subset hsub).to_subtype

lemma standardSimplexBoundary_zero_totallyDisconnected :
    TotallyDisconnectedSpace (standardSimplexBoundary 0) := by
  have := standardSimplexBoundary_zero_finite
  have : T2Space (Convexity.StdSimplex ℝ (Fin 2)) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).t2Space
  infer_instance

/-- The only singular vertices of the interval boundary are its two affine faces. -/
lemma standardSimplexBoundary_zero_simplex_cases
    (σ : (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))) _⦋0⦌) :
    σ = standardSimplexBoundaryFaceSSet 0 0 ∨ σ = standardSimplexBoundaryFaceSSet 0 1 := by
  let τ := (TopCat.of (standardSimplexBoundary 0)).toSSetObjEquiv _ σ
  obtain h | h := standardSimplexBoundary_zero_vertices (τ (Convexity.StdSimplex.single 0))
  · right
    apply ((TopCat.of (standardSimplexBoundary 0)).toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    have ht : t = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
    subst t
    change (τ (Convexity.StdSimplex.single 0)).val =
      Convexity.StdSimplex.map (Fin.succAbove (1 : Fin 2)) (Convexity.StdSimplex.single 0)
    simpa using h
  · left
    apply ((TopCat.of (standardSimplexBoundary 0)).toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    have ht : t = Convexity.StdSimplex.single 0 := Subsingleton.elim _ _
    subst t
    change (τ (Convexity.StdSimplex.single 0)).val =
      Convexity.StdSimplex.map (Fin.succAbove (0 : Fin 2)) (Convexity.StdSimplex.single 0)
    simpa using h

lemma standardSimplexBoundary_zero_faces_ne :
    standardSimplexBoundaryFaceSSet 0 0 ≠ standardSimplexBoundaryFaceSSet 0 1 := by
  intro h
  have hw := congrArg (fun σ ↦
    (((TopCat.of (standardSimplexBoundary 0)).toSSetObjEquiv _ σ)
      (Convexity.StdSimplex.single 0)).val.weights 0) h
  norm_num [standardSimplexBoundaryFaceSSet, standardSimplexBoundaryFace,
    Convexity.StdSimplex.weights_map, Finsupp.mapDomain] at hw

/-- The i-th coefficient of an actual singular zero-chain of the interval boundary. -/
def standardSimplexBoundaryZeroCoeff (i : Fin 2) :
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).X 0 ⟶ reducedSingularIntegralCoefficients :=
  by
    classical
    exact Sigma.desc (fun σ ↦ if σ = standardSimplexBoundaryFaceSSet 0 i then 𝟙 _ else 0)

lemma standardSimplexBoundaryZeroCoeff_generator (i j : Fin 2) :
    (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
      (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet 0 j) ≫
      standardSimplexBoundaryZeroCoeff i = if j = i then 𝟙 _ else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [standardSimplexBoundaryZeroCoeff, SSet.ιChainComplex,
      standardSimplexBoundary_zero_faces_ne, Ne.symm standardSimplexBoundary_zero_faces_ne]

/-- These two coefficient maps decompose every boundary zero-chain. -/
lemma standardSimplexBoundaryZeroCoeff_decomposition :
    standardSimplexBoundaryZeroCoeff 0 ≫
      (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
        (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet 0 0) +
    standardSimplexBoundaryZeroCoeff 1 ≫
      (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
        (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet 0 1) = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  obtain rfl | rfl := standardSimplexBoundary_zero_simplex_cases σ <;>
    simp [Preadditive.comp_add, ← Category.assoc, standardSimplexBoundaryZeroCoeff_generator]

/-- With no nonzero first boundary in the discrete two-point space, its zeroth
homology is canonically its zero-chain module. -/
def standardSimplexBoundaryZeroHomologyChainIso :
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).homology 0 ≅
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).X 0 := by
  let K := (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
    reducedSingularIntegralCoefficients
  have := standardSimplexBoundary_zero_totallyDisconnected
  have hf : (K.sc 0).f = 0 := by
    change K.d ((ComplexShape.down ℕ).prev 0) 0 = 0
    rw [(ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
    exact HolomorphicAnosov.Topology.Homology.disconnected_first_boundary_zero
      (TopCat.of (standardSimplexBoundary 0))
  exact ((K.sc 0).asIsoHomologyπ hf).symm ≪≫ asIso (K.iCycles 0)

lemma standardSimplexBoundaryZeroHomologyChainIso_class
    (c : LinearMap.ker ((((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).sc 0).g.hom)) :
    standardSimplexBoundaryZeroHomologyChainIso.hom
      (GoodPair.integralChainCycleClass _ 0 c) = c.val := by
  let K := (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
    reducedSingularIntegralCoefficients
  rw [GoodPair.integralChainCycleClass_eq]
  have he : K.homologyπ 0 ≫ standardSimplexBoundaryZeroHomologyChainIso.hom = K.iCycles 0 := by
    simp only [standardSimplexBoundaryZeroHomologyChainIso, HomologicalComplex.homologyπ, K, Iso.trans_hom, Iso.symm_hom,
      ShortComplex.homologyπ_comp_asIsoHomologyπ_inv_assoc, asIso_hom]
  change (K.homologyπ 0 ≫ standardSimplexBoundaryZeroHomologyChainIso.hom)
    ((K.sc 0).moduleCatCyclesIso.inv c) = c.val
  rw [he]
  exact congrArg (fun f ↦ f c) ((K.sc 0).moduleCatCyclesIso_inv_iCycles)

lemma standardSimplexBoundaryZeroHomologyChainIso_projection :
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).homologyπ 0 ≫
      standardSimplexBoundaryZeroHomologyChainIso.hom =
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).iCycles 0 := by
  simp only [standardSimplexBoundaryZeroHomologyChainIso, HomologicalComplex.homologyπ,
    Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyπ_comp_asIsoHomologyπ_inv_assoc, asIso_hom]

lemma standardSimplexBoundaryZeroHomologyChainIso_inv_generator
    (σ : (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))) _⦋0⦌) :
    (TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
      (R := reducedSingularIntegralCoefficients) σ ≫ standardSimplexBoundaryZeroHomologyChainIso.inv =
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).liftCycles
      ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
        (R := reducedSingularIntegralCoefficients) σ) 0 (by simp) (by simp) ≫
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).homologyπ 0 := by
  apply (cancel_mono standardSimplexBoundaryZeroHomologyChainIso.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    standardSimplexBoundaryZeroHomologyChainIso_projection, HomologicalComplex.liftCycles_i]

/-- Adding the two endpoint coefficients agrees with inclusion into the
interval followed by its ordinary H₀ augmentation. -/
lemma standardSimplexBoundaryZeroCoeff_sum_homology :
    standardSimplexBoundaryZeroCoeff 0 + standardSimplexBoundaryZeroCoeff 1 =
    standardSimplexBoundaryZeroHomologyChainIso.inv ≫
      SSet.homologyMap (singularSubspacePair
        (TopCat.of (Convexity.StdSimplex ℝ (Fin 2))) (standardSimplexBoundary 0)).hom
        reducedSingularIntegralCoefficients 0 ≫
      (TopCat.of (Convexity.StdSimplex ℝ (Fin 2))).singularHomology₀ε
        reducedSingularIntegralCoefficients := by
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin 2))
  let Y := TopCat.of (standardSimplexBoundary 0)
  let R := reducedSingularIntegralCoefficients
  let K := (TopCat.toSSet.obj Y).chainComplex R
  let i := (singularSubspacePair X (standardSimplexBoundary 0)).hom
  apply SSet.chainComplex_hom_ext
  intro σ
  have hl : (TopCat.toSSet.obj Y).ιChainComplex (R := R) σ ≫
      (standardSimplexBoundaryZeroCoeff 0 + standardSimplexBoundaryZeroCoeff 1) = 𝟙 R := by
    obtain rfl | rfl := standardSimplexBoundary_zero_simplex_cases σ <;>
      simp [Y, R, Preadditive.comp_add, standardSimplexBoundaryZeroCoeff_generator]
  rw [hl, ← Category.assoc, standardSimplexBoundaryZeroHomologyChainIso_inv_generator,
    Category.assoc]
  change 𝟙 R = K.liftCycles ((TopCat.toSSet.obj Y).ιChainComplex σ) 0 _ _ ≫
    K.homologyπ 0 ≫ HomologicalComplex.homologyMap (SSet.chainComplexMap i R) 0 ≫
      (TopCat.toSSet.obj X).homology₀ε R
  rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap, SSet.ι_chainComplexMap_f]
  exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε (TopCat.toSSet.obj X) R (i.app _ σ)).symm

/-- The endpoint chain attached to a relative one-class has coefficient sum
zero, by the exact connecting-map relation. -/
lemma standardSimplexBoundaryZeroCoeff_sum_connecting
    (a : (singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))
      (standardSimplexBoundary 0)).homology (C := ModuleCat ℤ) reducedSingularIntegralCoefficients 1) :
    let b := standardSimplexBoundaryZeroHomologyChainIso.hom
      (((singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))
        (standardSimplexBoundary 0)).homologyδ reducedSingularIntegralCoefficients 1 0) a)
    standardSimplexBoundaryZeroCoeff 0 b + standardSimplexBoundaryZeroCoeff 1 b = 0 := by
  let P := singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))
    (standardSimplexBoundary 0)
  let R := reducedSingularIntegralCoefficients
  change ((P.homologyδ R 1 0) ≫ standardSimplexBoundaryZeroHomologyChainIso.hom ≫
    (standardSimplexBoundaryZeroCoeff 0 + standardSimplexBoundaryZeroCoeff 1)) a = 0
  rw [standardSimplexBoundaryZeroCoeff_sum_homology,
    ← Category.assoc standardSimplexBoundaryZeroHomologyChainIso.hom,
    Iso.hom_inv_id, Category.id_comp,
    ← Category.assoc, P.homologyδ_comp R 1 0, zero_comp]
  rfl

/-- The endpoint difference has first coefficient one. -/
lemma standardSimplexBoundaryZeroCoeff_boundaryChain :
    standardSimplexBoundaryZeroCoeff 0 (standardSimplexBoundaryChain 0) = ULift.up 1 := by
  classical
  unfold standardSimplexBoundaryChain
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    map_add, map_zsmul]
  have h (j : Fin 2) := congrArg (fun f => f (ULift.up 1))
    (standardSimplexBoundaryZeroCoeff_generator 0 j)
  change ∀ j, standardSimplexBoundaryZeroCoeff 0
    (((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
      (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet 0 j)) (ULift.up 1)) = _ at h
  rw [h 0, h 1]
  simp

/-- Every endpoint chain with coefficient sum zero is an integral multiple
of the alternating boundary of the identity edge. -/
lemma standardSimplexBoundaryZeroCoeff_span
    (c : ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).chainComplex
      reducedSingularIntegralCoefficients).X 0)
    (h : standardSimplexBoundaryZeroCoeff 0 c + standardSimplexBoundaryZeroCoeff 1 c = 0) :
    c = (standardSimplexBoundaryZeroCoeff 0 c).down • standardSimplexBoundaryChain 0 := by
  classical
  have hd := congrArg (fun f => f c) standardSimplexBoundaryZeroCoeff_decomposition
  change _ + _ = c at hd
  trans ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
      (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet 0 0))
      (standardSimplexBoundaryZeroCoeff 0 c) +
    ((TopCat.toSSet.obj (TopCat.of (standardSimplexBoundary 0))).ιChainComplex
      (R := reducedSingularIntegralCoefficients) (standardSimplexBoundaryFaceSSet 0 1))
      (standardSimplexBoundaryZeroCoeff 1 c)
  · exact hd.symm
  have h1 : standardSimplexBoundaryZeroCoeff 1 c = -standardSimplexBoundaryZeroCoeff 0 c :=
    eq_neg_of_add_eq_zero_right h
  rw [h1]
  unfold standardSimplexBoundaryChain
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_one_zsmul, zsmul_add, zsmul_neg, map_neg]
  rw [← map_zsmul, ← map_zsmul]
  have hs : (standardSimplexBoundaryZeroCoeff 0 c).down • (ULift.up 1 : ULift ℤ) =
      standardSimplexBoundaryZeroCoeff 0 c := by
    apply ULift.ext
    simp
  rw [hs]

/-- The connecting map in dimension one is injective because the interval
has zero first homology. -/
lemma standardSimplexBoundary_zero_connecting_mono :
    Mono ((singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))
      (standardSimplexBoundary 0)).homologyδ reducedSingularIntegralCoefficients 1 0) := by
  let X := TopCat.of (Convexity.StdSimplex ℝ (Fin 2))
  let P := singularSubspacePair X (standardSimplexBoundary 0)
  have : ContractibleSpace X := standardSimplex_contractible 0
  change Mono ((P.shortExact_chainComplexShortComplex _).δ 1 0 _)
  exact (P.shortExact_chainComplexShortComplex _).mono_δ 1 0 rfl
    (singular_homology_isZero_of_contractible X reducedSingularIntegralCoefficients 1 (by decide))

/-- The interval identity edge generates its first relative homology,
with coefficient one at its positive endpoint. -/
lemma standardSimplexIdentityClass_equiv_zero :
    ∃ e : ℤ ≃ₗ[ℤ]
      (singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))
        (standardSimplexBoundary 0)).homology (C := ModuleCat ℤ)
          reducedSingularIntegralCoefficients 1,
      e 1 = standardSimplexIdentityClass 0 := by
  let P := singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin 2)))
    (standardSimplexBoundary 0)
  let R := reducedSingularIntegralCoefficients
  let d := (P.homologyδ R 1 0) ≫ standardSimplexBoundaryZeroHomologyChainIso.hom
  have : Mono (P.homologyδ R 1 0) := standardSimplexBoundary_zero_connecting_mono
  have hd : Function.Injective d := (ModuleCat.mono_iff_injective d).mp inferInstance
  have hg : d (standardSimplexIdentityClass 0) = standardSimplexBoundaryChain 0 := by
    change standardSimplexBoundaryZeroHomologyChainIso.hom
      ((P.homologyδ R 1 0) (standardSimplexIdentityClass 0)) = _
    rw [standardSimplexIdentityClass_connecting, standardSimplexBoundaryZeroHomologyChainIso_class]
  let f : ℤ →+ P.homology (C := ModuleCat ℤ) R 1 := zmultiplesHom _ (standardSimplexIdentityClass 0)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hab' := congrArg (fun x => (standardSimplexBoundaryZeroCoeff 0 (d x)).down) hab
      simp only [f, zmultiplesHom_apply] at hab'
      have hb := standardSimplexBoundaryZeroCoeff_boundaryChain
      simp only [map_zsmul, hg] at hab'
      rw [hb] at hab'
      simpa using hab' 
    · intro a
      refine ⟨(standardSimplexBoundaryZeroCoeff 0 (d a)).down, hd ?_⟩
      simp only [f, zmultiplesHom_apply]
      rw [map_zsmul, hg]
      exact (standardSimplexBoundaryZeroCoeff_span (d a)
        (standardSimplexBoundaryZeroCoeff_sum_connecting a)).symm
  refine ⟨(AddEquiv.ofBijective f hf).toIntLinearEquiv, ?_⟩
  change f 1 = _
  exact one_zsmul _

/-- Hatcher's identity-simplex primitive generator statement, isolated as a
source-backed provider. For the interval, the injective connecting map sends
the identity to the difference of the two endpoint generators; exactness
forces every image to have coefficient sum zero. In higher dimensions the
connecting map and projection modulo the contractible horn are isomorphisms.
The omitted facet induces an isomorphism by the explicit good-pair collars
and the closed-embedding collapse comparison. All other faces vanish modulo
the horn, leaving the zeroth face with coefficient one. Composing these
isomorphisms with the preceding dimension's equivalence proves the claim. -/
theorem standardSimplexIdentityClass_equiv_provider (n : ℕ) :
    ∃ e : ℤ ≃ₗ[ℤ]
      (singularSubspacePair
        (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 2))))
        (standardSimplexBoundary n)).homology (C := ModuleCat ℤ)
          reducedSingularIntegralCoefficients (n + 1),
      e 1 = standardSimplexIdentityClass n := by
  induction n with
  | zero => exact standardSimplexIdentityClass_equiv_zero
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    let R := reducedSingularIntegralCoefficients
    let P := singularSubspacePair (TopCat.of (Convexity.StdSimplex ℝ (Fin (n + 3))))
      (standardSimplexBoundary (n + 1))
    let Q := singularSubspacePair (TopCat.of (standardSimplexBoundary (n + 1)))
      (standardSimplexBoundaryHorn (n + 1))
    let d := P.homologyδ R (n + 2) (n + 1)
    let p := Q.homologyπ R (n + 1)
    let f := SSetPair.homologyMap (standardSimplexFacetPairMap n) R (n + 1)
    have : IsIso d := standardSimplexBoundary_connecting_isIso n
    have : IsIso p := standardSimplexBoundary_horn_projection_isIso (n + 1) (n + 1) (by omega)
    have : IsIso f := standardSimplexBoundaryFace_zero_homology_isIso n (n + 1) R
    let t := asIso d ≪≫ asIso p
    refine ⟨e.trans ((asIso f ≪≫ t.symm).toLinearEquiv), ?_⟩
    apply t.toLinearEquiv.injective
    simp only [LinearEquiv.trans_apply, he, CategoryTheory.Iso.toLinearEquiv_apply]
    change t.hom (t.inv (f (standardSimplexIdentityClass n))) =
      p (d (standardSimplexIdentityClass (n + 1)))
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
    exact (standardSimplexIdentityClass_facet_step n).symm

end HolomorphicAnosov

