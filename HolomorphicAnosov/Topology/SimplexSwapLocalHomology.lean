import HolomorphicAnosov.Topology.EmbeddedSimplexLocalClassGenerator
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexEmbeddedInterior
import HolomorphicAnosov.Topology.EuclideanPositiveSimplexFaceAvoidsZero
import HolomorphicAnosov.Topology.EuclideanPositiveLocalClass
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.LinearPathLocalHomology
import HolomorphicAnosov.Topology.PositiveLinearComponentPath
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Negative determinant action on local singular homology

Source: Hatcher, Algebraic Topology pp.108,115–118,125,269 (singular boundary,
relative quotient and the primitive simplex generator); Vector Bundles and
K-Theory pp.23–24 (components of the invertible real linear group).
Node: `topo.negative_linear_local_homology_action_g16`.

The explicit duplicate-vertex calculation below is an agent-written derivation
from these chain definitions. Let v₀=(-1,…,-1) and vᵢ=eᵢ for i>0. The linear
involution R(x)₀=-x₀, R(x)ᵢ=xᵢ-x₀ for i>0 swaps v₀,v₁ and fixes the remaining
vertices. Its matrix is lower triangular with diagonal (-1,1,…,1). Precompose
the positive simplex with the affine vertex map (0,1,0,2,…,n). The resulting
(n+1)-simplex has swapped and original n-simplex as faces 0 and 2, both with
positive sign. Every other face misses an original vertex. Since the only
zero preimage of the positive simplex has all barycentric weights positive,
these other faces avoid zero and vanish in the relative chain quotient.
Thus the sum of the swapped and original local classes is a boundary. The
existing embedded-simplex generator comparison then extends this equality
from the specified class to every class. Finally for det L<0, RL has positive
determinant and has a path to identity through injective maps. Multiplying
that path on the left by R gives a path from L to R. Homotopy invariance of
the punctured pair proves that L also acts by minus one. In dimension one
the same boundary is the triangle with ordered vertices (v₀,v₁,v₀), so no
higher-dimensional hemisphere or induction assumption is needed.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace HolomorphicAnosov
set_option backward.isDefEq.respectTransparency false

/-- The linear symmetry exchanging the first two vertices of the positive simplex. -/
def positiveSimplexSwap (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun x := WithLp.toLp 2 (fun i ↦ if i = 0 then -x 0 else x i - x 0)
  invFun x := WithLp.toLp 2 (fun i ↦ if i = 0 then -x 0 else x i - x 0)
  left_inv x := by ext i; by_cases hi : i = 0 <;> simp [hi]
  right_inv x := by ext i; by_cases hi : i = 0 <;> simp [hi]
  map_add' x y := by ext i; by_cases hi : i = 0 <;> simp [hi] <;> ring
  map_smul' a x := by ext i; by_cases hi : i = 0 <;> simp [hi, mul_sub]

/-- The exchanged coordinate changes sign; source: the displayed symmetry formula. -/
@[simp] theorem positiveSimplexSwap_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    positiveSimplexSwap n x 0 = -x 0 := by simp [positiveSimplexSwap]

/-- Every other coordinate subtracts the exchanged coordinate; source: the displayed formula. -/
@[simp] theorem positiveSimplexSwap_apply_succ (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    positiveSimplexSwap n x i.succ = x i.succ - x 0 := by simp [positiveSimplexSwap]

/-- The symmetry has determinant -1: its coordinate matrix is lower triangular
with diagonal (-1,1,…,1). Source: Hatcher VBKT pp.23–24 and the explicit matrix. -/
theorem positiveSimplexSwap_det (n : ℕ) :
    LinearMap.det (positiveSimplexSwap n).toLinearMap = -1 := by
  classical
  let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b]
  have hm (i j : Fin (n + 1)) :
      LinearMap.toMatrix b b (positiveSimplexSwap n).toLinearMap i j =
        if i = 0 then -(if j = 0 then 1 else 0)
        else (if i = j then 1 else 0) - (if j = 0 then 1 else 0) := by
    simp [LinearMap.toMatrix_apply, b, EuclideanSpace.basisFun_apply,
      positiveSimplexSwap, eq_comm]
  rw [Matrix.det_of_isLowerTriangular _ (by
    intro i j hij
    rw [hm]
    have hj : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
    have hji : i ≠ j := ne_of_lt hij
    simp [hj, hji])]
  rw [Fin.prod_univ_succ]
  simp [hm]

/-- The symmetry swaps the first two barycentric weights. Expanding the coordinate
formula gives this identity. Source: Hatcher AT p.269, ordered simplex convention. -/
theorem positiveSimplexSwap_simplex (n : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    positiveSimplexSwap n (euclideanPositiveSimplex (n + 1) t) =
      euclideanPositiveSimplex (n + 1)
        (Convexity.StdSimplex.map (Equiv.swap (0 : Fin (n + 2)) 1) t) := by
  classical
  ext i
  simp only [euclideanPositiveSimplex, ContinuousMap.coe_mk,
    PiLp.toLp_apply, Convexity.StdSimplex.weights_map,
    Finsupp.mapDomain_equiv_apply, Equiv.symm_swap]
  by_cases hi : i = 0
  · subst i
    simp [positiveSimplexSwap]
  · have hsi0 : i.succ ≠ (0 : Fin (n + 2)) := Fin.succ_ne_zero i
    have hsi1 : i.succ ≠ (1 : Fin (n + 2)) := fun h ↦ hi (Fin.succ_injective _ h)
    simp [positiveSimplexSwap, hi, Equiv.swap_apply_of_ne_of_ne hsi0 hsi1]

/-- Repeat the zeroth vertex at position two. -/
def positiveSimplexDuplicateVertex (n : ℕ) (i : Fin (n + 3)) : Fin (n + 2) :=
  ⟨if i.val < 2 then i.val else if i.val = 2 then 0 else i.val - 1, by
    split_ifs <;> omega⟩

/-- Removing the repeated vertex gives the original vertex order. Source: the explicit finite map. -/
theorem positiveSimplexDuplicateVertex_face_two (n : ℕ) :
    positiveSimplexDuplicateVertex n ∘ (⟨2, by omega⟩ : Fin (n + 3)).succAbove = id := by
  funext i
  apply Fin.ext
  simp only [Function.comp_apply, positiveSimplexDuplicateVertex, Fin.succAbove,
    Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp_all

/-- Removing the initial vertex exchanges vertices zero and one. Source: the explicit finite map. -/
theorem positiveSimplexDuplicateVertex_face_zero (n : ℕ) :
    positiveSimplexDuplicateVertex n ∘ (0 : Fin (n + 3)).succAbove =
      Equiv.swap (0 : Fin (n + 2)) 1 := by
  funext i
  by_cases hi0 : i = 0
  · subst i
    apply Fin.ext
    simp [positiveSimplexDuplicateVertex]
  by_cases hi1 : i = 1
  · subst i
    apply Fin.ext
    simp [positiveSimplexDuplicateVertex, Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  apply Fin.ext
  simp only [Function.comp_apply, Fin.succAbove_zero, positiveSimplexDuplicateVertex,
    Fin.val_succ]
  have h0 : i.val ≠ 0 := fun h ↦ hi0 (Fin.ext h)
  have h1 : i.val ≠ 1 := fun h ↦ hi1 (Fin.ext (h.trans (by simp)))
  split_ifs <;> omega

/-- Every other face omits an original vertex. Its omitted index is one for
face one and i-1 for face i>2. Source: the displayed duplicate-vertex map. -/
theorem positiveSimplexDuplicateVertex_face_omits (n : ℕ)
    (i : Fin (n + 3)) (hi0 : i ≠ 0) (hi2 : i ≠ ⟨2, by omega⟩) :
    ∃ j : Fin (n + 2), j ∉ Set.range (positiveSimplexDuplicateVertex n ∘ i.succAbove) := by
  have h0 : i.val ≠ 0 := fun h ↦ hi0 (Fin.ext h)
  have h2 : i.val ≠ 2 := fun h ↦ hi2 (Fin.ext h)
  let j : Fin (n + 2) := ⟨if i.val = 1 then 1 else i.val - 1, by split_ifs <;> omega⟩
  refine ⟨j, ?_⟩
  rintro ⟨k, hk⟩
  have hv := congrArg Fin.val hk
  dsimp [j, positiveSimplexDuplicateVertex, Fin.succAbove] at hv
  split_ifs at hv <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def] <;> omega

/-- An omitted original vertex has zero weight; a zero image would force every
weight to be zero, contradicting total weight one. Source: Hatcher AT p.269 and
the explicit affine simplex formula. -/
theorem positiveSimplexDuplicateVertex_face_avoids_zero (n : ℕ)
    (i : Fin (n + 3)) (hi0 : i ≠ 0) (hi2 : i ≠ ⟨2, by omega⟩)
    (t : Convexity.StdSimplex ℝ (Fin (n + 2))) :
    euclideanPositiveSimplex (n + 1) (Convexity.StdSimplex.map
      (positiveSimplexDuplicateVertex n) (Convexity.StdSimplex.map i.succAbove t)) ≠ 0 := by
  intro hz
  let u := Convexity.StdSimplex.map (positiveSimplexDuplicateVertex n)
    (Convexity.StdSimplex.map i.succAbove t)
  have hconstant (j : Fin (n + 2)) : u.weights j = u.weights 0 := by
    refine Fin.cases rfl (fun k ↦ ?_) j
    exact sub_eq_zero.mp (congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x k) hz)
  obtain ⟨j, hj⟩ := positiveSimplexDuplicateVertex_face_omits n i hi0 hi2
  have hj0 : u.weights j = 0 := by
    dsimp only [u]
    rw [← Convexity.StdSimplex.map_comp, Convexity.StdSimplex.weights_map]
    exact Finsupp.mapDomain_of_notMem_range _ _ hj
  apply Convexity.StdSimplex.weights_ne_zero u
  ext k
  exact (hconstant k).trans ((hconstant j).symm.trans hj0)

/-- The symmetry as a map of the actual punctured Euclidean pair. -/
def positiveSimplexSwapPair (n : ℕ) :
    singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) ({0} : Set _)ᶜ ⟶
      singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) ({0} : Set _)ᶜ :=
  singularSubspacePairMap
    (TopCat.ofHom (toContinuousMap (positiveSimplexSwap n).toContinuousLinearEquiv)) _ _
    (fun _x hx h ↦ hx ((positiveSimplexSwap n).injective (h.trans (map_zero _).symm)))

/-- The duplicated simplex bounds the sum of the swapped and original relative
chains. Faces zero and two survive with positive sign; all others factor through
the punctured subspace and are killed by the quotient. Source: Hatcher AT pp.108,115–118. -/
theorem positiveSimplexSwap_chain_boundary (n : ℕ) :
    let P := singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) ({0} : Set _)ᶜ
    let R := reducedSingularIntegralCoefficients
    let K := P.chainComplex R
    ∃ b : K.X (n + 2), K.d (n + 2) (n + 1) b =
      (SSetPair.chainComplexMap (positiveSimplexSwapPair n) R).f (n + 1)
        (euclideanPositiveLocalChain (n + 1)) + euclideanPositiveLocalChain (n + 1) := by
  classical
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let A : Set X := ({0} : Set _)ᶜ
  let P := singularSubspacePair X A
  let R := reducedSingularIntegralCoefficients
  let K := P.chainComplex R
  let u : C(Convexity.StdSimplex ℝ (Fin (n + 3)), X) :=
    (euclideanPositiveSimplex (n + 1)).comp
      ⟨Convexity.StdSimplex.map (positiveSimplexDuplicateVertex n),
        Convexity.StdSimplex.continuous_map ℝ _⟩
  let σ := (X.toSSetObjEquiv (op ⦋n + 2⦌)).symm u
  let τ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (euclideanPositiveSimplex (n + 1))
  let a : Fin (n + 3) := ⟨2, by omega⟩
  have htwo : (TopCat.toSSet.obj X).δ a σ = τ := by
    apply (X.toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro t
    change euclideanPositiveSimplex (n + 1) (Convexity.StdSimplex.map
      (positiveSimplexDuplicateVertex n) (Convexity.StdSimplex.map a.succAbove t)) = _
    rw [← Convexity.StdSimplex.map_comp]
    simp only [a, positiveSimplexDuplicateVertex_face_two, Convexity.StdSimplex.map_id]
    rfl
  have hzero : (TopCat.toSSet.obj X).δ 0 σ =
      (positiveSimplexSwapPair n).hom.right.app _ τ := by
    apply (X.toSSetObjEquiv _).injective
    apply ContinuousMap.ext
    intro t
    change euclideanPositiveSimplex (n + 1) (Convexity.StdSimplex.map
      (positiveSimplexDuplicateVertex n) (Convexity.StdSimplex.map (0 : Fin (n + 3)).succAbove t)) =
      positiveSimplexSwap n (euclideanPositiveSimplex (n + 1) t)
    rw [← Convexity.StdSimplex.map_comp, positiveSimplexDuplicateVertex_face_zero]
    exact (positiveSimplexSwap_simplex n t).symm
  have hkill (i : Fin (n + 3)) (hi0 : i ≠ 0) (hia : i ≠ a) :
      (TopCat.toSSet.obj X).ιChainComplex (R := R) ((TopCat.toSSet.obj X).δ i σ) ≫
        (P.chainComplexπ R).f (n + 1) = 0 := by
    let v : C(Convexity.StdSimplex ℝ (Fin (n + 2)), A) :=
      ⟨fun t ↦ ⟨X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t,
        positiveSimplexDuplicateVertex_face_avoids_zero n i hi0 hia t⟩,
        (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)).continuous.subtype_mk _⟩
    let α := ((TopCat.of A).toSSetObjEquiv (op ⦋n + 1⦌)).symm v
    have hα : (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ α =
        (TopCat.toSSet.obj X).δ i σ := by
      apply (X.toSSetObjEquiv _).injective
      ext t
      rfl
    rw [← hα, ← SSet.ι_chainComplexMap_f, Category.assoc]
    change _ ≫ (SSet.chainComplexMap P.hom R).f (n + 1) ≫ (P.chainComplexπ R).f (n + 1) = 0
    rw [P.chainComplex_condition_f]
    simp
  let b := (P.chainComplexπ R).f (n + 2)
    (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) (ULift.up 1))
  refine ⟨b, ?_⟩
  have hb : (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      (P.chainComplexπ R).f (n + 2) ≫ K.d (n + 2) (n + 1) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ (P.chainComplexπ R).f (n + 1)) ≫
        (SSetPair.chainComplexMap (positiveSimplexSwapPair n) R).f (n + 1) +
      (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ (P.chainComplexπ R).f (n + 1) := by
    rw [(P.chainComplexπ R).comm]
    change _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) ≫ _ = _
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
    rw [← Finset.sum_subset (show ({0, a} : Finset (Fin (n + 3))) ⊆ Finset.univ by simp)
      (by intro i _ hi; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
          rw [hkill i hi.1 hi.2]; simp)]
    have h0a : (0 : Fin (n + 3)) ≠ a := by intro h; have := congrArg Fin.val h; dsimp [a] at this; omega
    rw [Finset.sum_insert (show (0 : Fin (n + 3)) ∉ ({a} : Finset _) by simpa using h0a), Finset.sum_singleton]
    simp only [
      Fin.val_zero, pow_zero, one_smul, hzero, htwo]
    have ha : (-1 : ℤ) ^ a.val = 1 := by norm_num [a]
    rw [ha, one_smul]
    apply congrArg (fun v ↦ v + (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫
      (P.chainComplexπ R).f (n + 1))
    have hmap := SSet.ι_chainComplexMap_f _ _ (positiveSimplexSwapPair n).hom.right R τ
    have hmap' := congrArg (fun h ↦ h ≫ (P.chainComplexπ R).f (n + 1)) hmap
    refine hmap'.symm.trans ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun h ↦ (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ h)
        (pair_projection_naturality (positiveSimplexSwapPair n) R (n + 1)).symm).trans
        (Category.assoc _ _ _).symm)
  exact congrArg (fun f ↦ f (ULift.up 1)) hb

/-- Projecting the boundary identity to cycles modulo boundaries proves the swap
sends the specified local class to its negative. Source: Hatcher AT pp.108,115–118. -/
theorem positiveSimplexSwap_localClass (n : ℕ) :
    SSetPair.homologyMap (positiveSimplexSwapPair n) reducedSingularIntegralCoefficients (n + 1)
      (euclideanPositiveLocalClass (n + 1)) = -euclideanPositiveLocalClass (n + 1) := by
  let P := singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) ({0} : Set _)ᶜ
  let K := P.chainComplex reducedSingularIntegralCoefficients
  let S := K.sc (n + 1)
  let f := (HomologicalComplex.shortComplexFunctor _ _ (n + 1)).map
    (SSetPair.chainComplexMap (positiveSimplexSwapPair n) reducedSingularIntegralCoefficients)
  let c : LinearMap.ker S.g.hom :=
    ⟨euclideanPositiveLocalChain (n + 1), euclideanPositiveLocalChain_cycle (n + 1)⟩
  let d : LinearMap.ker S.g.hom := ⟨f.τ₂ c, by
    change (f.τ₂ ≫ S.g) c = 0
    rw [f.comm₂₃]
    change f.τ₃ (S.g c) = 0
    rw [c.property, map_zero]⟩
  have hmap := GoodPair.shortComplex_homologyMap_cycle f c d rfl
  change ShortComplex.homologyMap f
      (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π c)) =
    -S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π c)
  rw [hmap]
  obtain ⟨b, hb⟩ := positiveSimplexSwap_chain_boundary n
  let b' : S.X₁ := (K.xPrevIso (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) by rfl)).inv b
  have hzero : S.moduleCatLeftHomologyData.π (d + c) = 0 := by
    have heq : S.moduleCatLeftHomologyData.f' b' = d + c := by
      apply Subtype.ext
      change ((K.xPrevIso _).inv ≫ K.dTo (n + 1)) b = _
      rw [K.xPrevIso_comp_dTo]
      exact hb
    rw [← heq]
    exact congrArg (fun h ↦ h b') S.moduleCatLeftHomologyData.wπ
  have hsum : S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π d) +
      S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π c) = 0 := by
    rw [← map_add, ← map_add, hzero, map_zero]
  exact eq_neg_of_add_eq_zero_left hsum

/-- A negative determinant map is joined to the simplex swap by an invertible path. -/
theorem negative_linear_equiv_path_to_simplexSwap (n : ℕ)
    (L : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hL : LinearMap.det L.toLinearMap < 0) :
    ∃ D : unitInterval → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)),
      Continuous D ∧ (∀ t, Function.Injective (D t)) ∧
      D 0 = L.toContinuousLinearEquiv.toContinuousLinearMap ∧
      D 1 = (positiveSimplexSwap n).toContinuousLinearEquiv.toContinuousLinearMap := by
  let R := positiveSimplexSwap n
  let A := L.trans R
  have hA : 0 < LinearMap.det A.toLinearMap := by
    change 0 < LinearMap.det (R.toLinearMap.comp L.toLinearMap)
    rw [LinearMap.det_comp, positiveSimplexSwap_det]
    linarith
  obtain ⟨D, hD, hI, h0, h1⟩ := exists_positive_linear_equiv_injective_path (n + 1) A hA
  let E : unitInterval → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    fun t ↦ R.toContinuousLinearEquiv.toContinuousLinearMap.comp (D t)
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · exact Continuous.clm_comp continuous_const hD
  · intro t
    exact R.injective.comp (hI t)
  · dsimp only [E]
    rw [h0]
    ext x i
    change R (R (L x)) i = L x i
    by_cases hi : i = 0 <;> simp [R, positiveSimplexSwap, hi]
  · dsimp only [E]
    rw [h1]
    ext x
    rfl

/-- Swapping two vertices acts by minus one on local homology. The duplicate
vertex chain has the original and swapped simplices as its only nonzero relative
faces. Its boundary makes their classes negatives. The embedded simplex class
generates local homology, so the equality holds for every class.
Source: Hatcher, Algebraic Topology pp.108,115–118,125,269. -/
theorem positiveSimplexSwap_localHomology (n : ℕ)
    (c : (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({0} : Set _)ᶜ).homology (C := ModuleCat ℤ) reducedSingularIntegralCoefficients (n + 1)) :
    SSetPair.homologyMap (positiveSimplexSwapPair n) reducedSingularIntegralCoefficients (n + 1) c = -c := by
  have hgen := embeddedSimplex_localClass_free_generator n (euclideanPositiveSimplex (n + 1))
    (euclideanPositiveSimplex_embedded_interior (n + 1)).1
    (euclideanPositiveSimplex_embedded_interior (n + 1)).2
    (euclideanPositiveSimplex_face_avoids_zero n)
  obtain ⟨z, hz⟩ := hgen.2 c
  have hz' : z • euclideanPositiveLocalClass (n + 1) = c := by
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ
      ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
        ({0} : Set _)ᶜ).homology (C := ModuleCat ℤ) reducedSingularIntegralCoefficients (n + 1)))]
    exact hz
  rw [← hz', map_zsmul, positiveSimplexSwap_localClass, zsmul_neg]

/-- Every negative determinant linear map acts by minus one on local homology.
Compose with the simplex swap to obtain positive determinant, contract that
composition through invertible maps, and multiply the path by the swap again.
Relative homotopy invariance identifies the action with the already computed
swap action. Source: Hatcher VBKT pp.23–24 and AT pp.108,118,125,269. -/
theorem negative_linear_local_homology_action (n : ℕ)
    (L : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (hL : LinearMap.det L.toLinearMap < 0) :
    let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
    let A : Set X := {x | x ≠ 0}
    let f : X ⟶ X := TopCat.ofHom (toContinuousMap L.toContinuousLinearEquiv)
    ∀ c : (singularSubspacePair X A).homology (C := ModuleCat ℤ) singularIntegralCoefficients (n + 1),
      SSetPair.homologyMap (singularSubspacePairMap f A A
        (fun _x hx h ↦ hx (L.injective (h.trans L.map_zero.symm))))
        singularIntegralCoefficients (n + 1) c = -c := by
  obtain ⟨D, hD, hI, h0, h1⟩ := negative_linear_equiv_path_to_simplexSwap n L hL
  have hmaps := linear_path_local_homology D hD hI (n + 1)
  simp only [h0, h1] at hmaps
  have hf : toContinuousMap L.toContinuousLinearEquiv.toContinuousLinearMap =
      toContinuousMap L.toContinuousLinearEquiv := by ext x; rfl
  have hg : toContinuousMap (positiveSimplexSwap n).toContinuousLinearEquiv.toContinuousLinearMap =
      toContinuousMap (positiveSimplexSwap n).toContinuousLinearEquiv := by ext x; rfl
  simp only [hf, hg] at hmaps
  dsimp only
  rw [hmaps]
  exact positiveSimplexSwap_localHomology n

end HolomorphicAnosov

