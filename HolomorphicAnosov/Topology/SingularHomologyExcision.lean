import HolomorphicAnosov.Topology.SingularHomologyExcision.PairProjectionNaturality
import HolomorphicAnosov.Topology.SingularHomologyExcision.QuotientDegreeIsIso
import HolomorphicAnosov.Topology.SingularHomologyExcision.QuotientIso
import HolomorphicAnosov.Topology.SingularHomologyExcision.PairNaturality
import HolomorphicAnosov.Topology.SingularHomologyExcision.HomologyNaturality
import HolomorphicAnosov.Topology.SingularHomologyExcision.CoefficientNaturality
import HolomorphicAnosov.Topology.SingularHomologyExcision.ComplementCover
import HolomorphicAnosov.Topology.SingularHomologyExcision.SourceEquivOfSmall
import HolomorphicAnosov.Topology.SingularHomologyExcision.HomologyIsIsoOfEquiv
import HolomorphicAnosov.Topology.SingularBarycentricSubdivisionGeometry
import Mathlib.Algebra.Homology.Homotopy
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
import Mathlib.Geometry.Convex.Hull
import Mathlib.Analysis.Convex.MetricSpace
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Analysis.SpecificLimits.Basic

section NativeConstruction

/-!
# Explicit native barycentric chain operator construction

Source: Hatcher, Algebraic Topology, Proposition 2.21(2)–(3), pp.121–123.
This isolated construction uses ordered affine vertex tuples and finite signed lists.
Its coefficient extension is the actual native simplicial-chain coproduct morphism.
No chain identity, support certificate or eventual-smallness fact is assumed.
-/

universe u v w
variable {K : Type w} [CommRing K]

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial

namespace HolomorphicAnosov.NativeBarycentricOperators

/-- The actual closed standard simplex in its Mathlib weights topology. -/
abbrev Simplex (n : ℕ) := StdSimplex ℝ (Fin (n + 1))

local instance simplexMetric (n : ℕ) : MetricSpace (Simplex n) :=
  Topology.IsEmbedding.comapMetricSpace
    (fun x : Simplex n ↦ fun j ↦ x.weights j)
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1)))

/-- A finite signed list of ordered vertex simplices, retaining repetitions. -/
abbrev SignedTuples (k n : ℕ) := List (ℤ × (Fin (n + 1) → Simplex k))

/-- The actual equal-weight barycenter of an ordered tuple (Hatcher p.121). -/
def tupleBarycenter {k n : ℕ} (v : Fin (n + 1) → Simplex k) : Simplex k :=
  iConvexComb (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) v

/-- The finite coning recursion Sλ=c_b(S∂λ), with S[v]=[v] (Hatcher pp.121–122).
The alternating boundary signs are retained, and the barycenter is the new FIRST vertex. -/
def subdivisionTuples {k : ℕ} (n : ℕ) (v : Fin (n + 1) → Simplex k) : SignedTuples k n :=
  match n, v with
  | 0, v => [(1, v)]
  | n + 1, v => (List.finRange (n + 2)).flatMap fun i ↦
      (subdivisionTuples n (v ∘ i.succAbove)).map fun t ↦
        ((-1 : ℤ) ^ i.val * t.1, Fin.cons (tupleBarycenter v) t.2)

/-- The finite coning recursion Tλ=c_b(λ−T∂λ) (Hatcher p.122).
The zero-degree term is the allowed degenerate edge [v,v], not a normalized zero chain. -/
def homotopyTuples {k : ℕ} (n : ℕ) (v : Fin (n + 1) → Simplex k) :
    SignedTuples k (n + 1) :=
  match n, v with
  | 0, v => [(1, Fin.cons (v 0) v)]
  | n + 1, v => [(1, Fin.cons (tupleBarycenter v) v)] ++
      (List.finRange (n + 2)).flatMap fun i ↦
        (homotopyTuples n (v ∘ i.succAbove)).map fun t ↦
          (-((-1 : ℤ) ^ i.val * t.1), Fin.cons (tupleBarycenter v) t.2)

/-- The literal affine interpolation of an ordered tuple in standard-simplex weights. -/
def interpolate {k n : ℕ} (v : Fin (n + 1) → Simplex k) (w : Simplex n) : Simplex k :=
  iConvexComb w v

/-- Every output weight is the finite weighted sum of the corresponding vertex weights.
Source: Hatcher linear simplices p.121 and the native finite convex-combination formula. -/
theorem interpolate_weights {k n : ℕ} (v : Fin (n + 1) → Simplex k)
    (w : Simplex n) (j : Fin (k + 1)) :
    (interpolate v w).weights j = ∑ i, w.weights i * (v i).weights j := by
  simp only [interpolate, iConvexComb, StdSimplex.weights_sConvexComb,
    StdSimplex.weights_map, Finsupp.sum_apply]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_mul])]
  exact Finsupp.sum_fintype _ _ (by simp)


/-- Native topology makes this exact affine simplex continuous (Hatcher p.121). -/
theorem interpolate_continuous {k n : ℕ} (v : Fin (n + 1) → Simplex k) :
    Continuous (interpolate v) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (k + 1))).continuous_iff]
  apply continuous_pi
  intro j
  simp only [Function.comp_apply, interpolate_weights]
  fun_prop

/-- The actual continuous affine simplex associated with the tuple, not an opaque map. -/
def affineSimplex {k n : ℕ} (v : Fin (n + 1) → Simplex k) : C(Simplex n, Simplex k) :=
  ⟨interpolate v, interpolate_continuous v⟩

/-- Extend the actual finite signed domain chain by postcomposing with a singular simplex.
Source: Hatcher p.122–123, Sσ=σ#(SΔ) and Tσ=σ#(TΔ), with arbitrary coefficients. -/
def signedGeneratorMap {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (terms : SignedTuples k n) :
    R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n :=
  (terms.map fun t ↦ t.1 • (TopCat.toSSet.obj X).ιChainComplex
    ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex t.2)))).sum

/-- Actual subdivision degree morphism of native singular chain modules (Hatcher p.122).
The native coproduct leaves every coefficient unchanged except the displayed integer signs. -/
def subdivisionComponent (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X n :=
  Sigma.desc fun σ ↦ signedGeneratorMap R (X.toSSetObjEquiv (op ⦋n⦌) σ)
    (subdivisionTuples n (fun i ↦ StdSimplex.single i))

/-- Actual raising-degree homotopy morphism of native singular chain modules (Hatcher p.123). -/
def homotopyComponent (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) :=
  Sigma.desc fun σ ↦ signedGeneratorMap R (X.toSSetObjEquiv (op ⦋n⦌) σ)
    (homotopyTuples n (fun i ↦ StdSimplex.single i))

/-- The coproduct morphism has precisely the displayed subdivision on each native generator. -/
theorem subdivisionComponent_generator (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫ subdivisionComponent X R n =
      signedGeneratorMap R (X.toSSetObjEquiv (op ⦋n⦌) σ)
        (subdivisionTuples n (fun i ↦ StdSimplex.single i)) := by
  exact Sigma.ι_comp_desc _ σ

/-- The raising-degree coproduct morphism has the displayed homotopy on each generator. -/
theorem homotopyComponent_generator (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (n : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫ homotopyComponent X R n =
      signedGeneratorMap R (X.toSSetObjEquiv (op ⦋n⦌) σ)
        (homotopyTuples n (fun i ↦ StdSimplex.single i)) := by
  exact Sigma.ι_comp_desc _ σ

/-- Native singular generators postcompose by the literal continuous map.
Source: Hatcher p.110 and the native singular-set functor. -/
theorem singular_generator_postcompose {X Y : TopCat.{u}} (f : X ⟶ Y) {n : ℕ}
    (σ : C(Simplex n, X)) :
    (TopCat.toSSet.map f).app (op ⦋n⦌) ((X.toSSetObjEquiv (op ⦋n⦌)).symm σ) =
      (Y.toSSetObjEquiv (op ⦋n⦌)).symm (f.hom.comp σ) := by
  rfl

/-- Finite signed chains commute with actual postcomposition, retaining all coefficients.
Source: Hatcher pp.122–123; distributivity of native chain maps over finite integer sums. -/
theorem signedGeneratorMap_postcompose {X Y : TopCat.{u}} (f : X ⟶ Y)
    {k n : ℕ} (R : ModuleCat.{max u v} K) (σ : C(Simplex k, X)) (terms : SignedTuples k n) :
    signedGeneratorMap R σ terms ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n =
      signedGeneratorMap R (f.hom.comp σ) terms := by
  induction terms with
  | nil => simp [signedGeneratorMap]
  | cons t terms ih =>
    simp only [signedGeneratorMap, List.map_cons, List.sum_cons] at ih ⊢
    rw [Preadditive.add_comp, Preadditive.zsmul_comp,
      SSet.ι_chainComplexMap_f, singular_generator_postcompose]
    rw [ih]
    rfl

/-- S's actual native degree maps commute with every continuous postcomposition.
Source: Hatcher p.122, checked on every original singular generator. -/
theorem subdivisionComponent_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    (R : ModuleCat.{max u v} K) (n : ℕ) :
    subdivisionComponent X R n ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫ subdivisionComponent Y R n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, subdivisionComponent_generator, signedGeneratorMap_postcompose,
    SSet.ι_chainComplexMap_f_assoc, subdivisionComponent_generator]
  congr 1

/-- T's actual native degree maps commute with every continuous postcomposition.
Source: Hatcher p.123; this same equation provides supported-subspace factorization. -/
theorem homotopyComponent_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    (R : ModuleCat.{max u v} K) (n : ℕ) :
    homotopyComponent X R n ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f (n + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫ homotopyComponent Y R n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, homotopyComponent_generator, signedGeneratorMap_postcompose,
    SSet.ι_chainComplexMap_f_assoc, homotopyComponent_generator]
  congr 1

/-- S preserves the chains of each original subspace, with its actual induced topology.
Source: Hatcher pp.122–124; specialize postcomposition to the continuous subtype inclusion. -/
theorem subdivisionComponent_subspace (X : TopCat.{u}) (A : Set X)
    (R : ModuleCat.{max u v} K) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X)) R).f n ≫
        subdivisionComponent X R n =
      subdivisionComponent (TopCat.of A) R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X)) R).f n := by
  exact (subdivisionComponent_naturality _ R n).symm

/-- T preserves the same supported subspace chains in its raising degree.
Source: Hatcher pp.123–124; no openness or closedness of A is required. -/
theorem homotopyComponent_subspace (X : TopCat.{u}) (A : Set X)
    (R : ModuleCat.{max u v} K) (n : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X)) R).f n ≫
        homotopyComponent X R n =
      homotopyComponent (TopCat.of A) R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of A ⟶ X)) R).f (n + 1) := by
  exact (homotopyComponent_naturality _ R n).symm

/-- Interpolation of the standard ordered vertices is the literal identity simplex. -/
theorem affineSimplex_identity (n : ℕ) :
    affineSimplex (fun i : Fin (n + 1) ↦ StdSimplex.single i) = ContinuousMap.id (Simplex n) := by
  apply ContinuousMap.ext
  intro w
  exact StdSimplex.iConvexComb_single w

/-- Interpolation commutes with every coordinate face or degeneracy map.
Source: Hatcher pp.122–123, affine compatibility with the standard simplex operators. -/
theorem interpolate_map {k n m : ℕ} (v : Fin (n + 1) → Simplex k)
    (f : Fin (m + 1) → Fin (n + 1)) (w : Simplex m) :
    interpolate v (StdSimplex.map f w) = interpolate (v ∘ f) w := by
  exact iConvexComb_map w f v

/-- The singular face of an affine tuple is exactly the omitted-vertex tuple.
Source: Hatcher p.122, with the native singular-set face equivalence. -/
theorem affine_generator_face {X : TopCat.{u}} {k n : ℕ} (σ : C(Simplex k, X))
    (v : Fin (n + 2) → Simplex k) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i
        ((X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (σ.comp (affineSimplex v))) =
      (X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex (v ∘ i.succAbove))) := by
  apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
  ext w
  rw [TopCat.toSSetObjEquiv_δ_apply]
  simp only [Equiv.apply_symm_apply, ContinuousMap.comp_apply, affineSimplex]
  change σ (interpolate v (StdSimplex.map i.succAbove w)) =
    σ (interpolate (v ∘ i.succAbove) w)
  rw [interpolate_map]

/-- The native boundary of every affine generator is the original alternating face sum.
Source: Hatcher p.108 and p.122; no chain identity is assumed. -/
theorem affine_generator_boundary {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (v : Fin (n + 2) → Simplex k) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (σ.comp (affineSimplex v))) ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (TopCat.toSSet.obj X).ιChainComplex (R := R)
          ((X.toSSetObjEquiv (op ⦋n⦌)).symm
            (σ.comp (affineSimplex (v ∘ i.succAbove)))) := by
  rw [SSet.ιChainComplex_d]
  simp only [affine_generator_face]

/-- The exact zeroth subdivision map is identity, including arbitrary coefficients. -/
theorem subdivisionComponent_zero (X : TopCat.{u}) (R : ModuleCat.{max u v} K) :
    subdivisionComponent X R 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [subdivisionComponent_generator]
  simp [signedGeneratorMap, subdivisionTuples, affineSimplex_identity]

/-- The cone homotopy at degree zero has zero boundary: both endpoints are the original
vertex. This keeps the allowed degenerate singular edge rather than normalizing it away. -/
theorem homotopyComponent_zero_boundary (X : TopCat.{u}) (R : ModuleCat.{max u v} K) :
    homotopyComponent X R 0 ≫ ((TopCat.toSSet.obj X).chainComplex R).d 1 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, homotopyComponent_generator]
  simp only [homotopyTuples, signedGeneratorMap, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, one_smul, add_zero]
  rw [affine_generator_boundary]
  simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero,
    one_smul, Fin.val_succ, Fin.val_zero, zero_add, pow_one, neg_one_zsmul]
  have hfaces :
      (fun i : Fin 1 ↦ (Fin.cons (α := fun _ ↦ Simplex 0) (StdSimplex.single (0 : Fin 1))
        (fun j : Fin 1 ↦ StdSimplex.single j)) ((0 : Fin 2).succAbove i)) =
      (fun i : Fin 1 ↦ (Fin.cons (α := fun _ ↦ Simplex 0) (StdSimplex.single (0 : Fin 1))
        (fun j : Fin 1 ↦ StdSimplex.single j)) ((1 : Fin 2).succAbove i)) := by
    funext i
    subsingleton
  change (Fin.cons (α := fun _ ↦ Simplex 0) (StdSimplex.single (0 : Fin 1))
    (fun j : Fin 1 ↦ StdSimplex.single j)) ∘ (0 : Fin 2).succAbove =
    (Fin.cons (α := fun _ ↦ Simplex 0) (StdSimplex.single (0 : Fin 1))
    (fun j : Fin 1 ↦ StdSimplex.single j)) ∘ (1 : Fin 2).succAbove at hfaces
  rw [hfaces]
  simp

/-- The cone boundary is the original simplex minus the cone on its alternating boundary.
Source: Hatcher p.121, the literal first-vertex cone identity; repeated vertices are allowed. -/
theorem affine_cone_boundary {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (b : Simplex k) (v : Fin (n + 2) → Simplex k) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n + 2⦌)).symm
          (σ.comp (affineSimplex (Fin.cons b v)))) ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) =
      (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (σ.comp (affineSimplex v))) -
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (TopCat.toSSet.obj X).ιChainComplex (R := R)
          ((X.toSSetObjEquiv (op ⦋n + 1⦌)).symm
            (σ.comp (affineSimplex (Fin.cons b (v ∘ i.succAbove))))) := by
  rw [affine_generator_boundary, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
    Fin.cons_comp_succ, Fin.val_succ, pow_succ, Fin.cons_comp_succ_succAbove]
  simp only [mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  have hremove (i : Fin (n + 2)) : i.removeNth v = v ∘ i.succAbove := by
    funext j
    exact Fin.removeNth_apply i v j
  simp only [hremove, sub_eq_add_neg]

/-- At degree zero the cone boundary is its endpoint minus its apex.
Source: Hatcher p.121, including the degenerate edge when these points agree. -/
theorem affine_cone_zero_boundary {X : TopCat.{u}} {k : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (b : Simplex k) (v : Fin 1 → Simplex k) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋1⦌)).symm
          (σ.comp (affineSimplex (Fin.cons b v)))) ≫
        ((TopCat.toSSet.obj X).chainComplex R).d 1 0 =
      (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋0⦌)).symm (σ.comp (affineSimplex v))) -
      (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋0⦌)).symm
          (σ.comp (affineSimplex (fun _ : Fin 1 ↦ b)))) := by
  rw [affine_generator_boundary, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
    Fin.cons_comp_succ, Fin.sum_univ_one, Fin.val_succ, zero_add, pow_one, neg_one_zsmul]
  have hface : (Fin.cons (α := fun _ ↦ Simplex k) b v) ∘ (Fin.succ (0 : Fin 1)).succAbove =
      (fun _ : Fin 1 ↦ b) := by
    funext i
    fin_cases i
    rfl
  rw [hface]
  simp only [sub_eq_add_neg]

/-- Affine interpolation stays in every actual convex set containing its vertices.
Source: Hatcher p.121, convex support of linear simplices. -/
theorem interpolate_mem {k n : ℕ} {C : Set (Simplex k)}
    (hC : IsConvexSet ℝ C) {v : Fin (n + 1) → Simplex k}
    (hv : ∀ i, v i ∈ C) (w : Simplex n) : interpolate v w ∈ C := by
  exact hC.iConvexComb_mem fun i _ ↦ hv i

/-- Every recursively subdivided vertex remains in the original convex support.
Source: Hatcher pp.121–122; each new apex is the actual equal-weight barycenter. -/
theorem subdivisionTuples_mem {k : ℕ} (n : ℕ) {C : Set (Simplex k)}
    (hC : IsConvexSet ℝ C) (v : Fin (n + 1) → Simplex k)
    (hv : ∀ i, v i ∈ C) :
    ∀ t ∈ subdivisionTuples n v, ∀ j, t.2 j ∈ C := by
  induction n with
  | zero =>
    intro t ht j
    simp only [subdivisionTuples, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    exact hv j
  | succ n ih =>
    intro t ht j
    simp only [subdivisionTuples, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨i, _, a, ha, rfl⟩ := ht
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · exact hC.iConvexComb_mem fun i _ ↦ hv i
    · exact ih _ (fun l ↦ hv (i.succAbove l)) a ha j

/-- All homotopy vertices also stay in the original convex support, including the repeated
zeroth vertex. Source: Hatcher p.123, support of the first-vertex cone recursion. -/
theorem homotopyTuples_mem {k : ℕ} (n : ℕ) {C : Set (Simplex k)}
    (hC : IsConvexSet ℝ C) (v : Fin (n + 1) → Simplex k)
    (hv : ∀ i, v i ∈ C) :
    ∀ t ∈ homotopyTuples n v, ∀ j, t.2 j ∈ C := by
  induction n with
  | zero =>
    intro t ht j
    simp only [homotopyTuples, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    exact Fin.cases (hv 0) hv j
  | succ n ih =>
    intro t ht j
    simp only [homotopyTuples, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap, List.mem_map] at ht
    rcases ht with ht | ⟨i, _, a, ha, rfl⟩
    · subst t
      exact Fin.cases (hC.iConvexComb_mem fun i _ ↦ hv i) hv j
    · refine Fin.cases ?_ (fun j ↦ ?_) j
      · exact hC.iConvexComb_mem fun i _ ↦ hv i
      · exact ih _ (fun l ↦ hv (i.succAbove l)) a ha j

/-- Every actual affine image in the S recursion lies in the convex hull of the original
vertices. Source: Hatcher pp.121–122; this is the precise domain support needed for meshes. -/
theorem subdivisionTuples_image_hull {k : ℕ} (n : ℕ)
    (v : Fin (n + 1) → Simplex k) {t : ℤ × (Fin (n + 1) → Simplex k)}
    (ht : t ∈ subdivisionTuples n v) (w : Simplex n) :
    interpolate t.2 w ∈ Convexity.convexHull ℝ (Set.range v) := by
  apply interpolate_mem (IsConvexSet.convexHull (R := ℝ) (s := Set.range v))
  exact subdivisionTuples_mem n (IsConvexSet.convexHull (R := ℝ) (s := Set.range v)) v
    (fun i ↦ subset_convexHull_self ⟨i, rfl⟩) t ht

/-- The T recursion has the same full convex-hull support, including all degenerate tuples.
Source: Hatcher p.123, so no dimension or distinct-vertex assumption is introduced. -/
theorem homotopyTuples_image_hull {k : ℕ} (n : ℕ)
    (v : Fin (n + 1) → Simplex k) {t : ℤ × (Fin (n + 2) → Simplex k)}
    (ht : t ∈ homotopyTuples n v) (w : Simplex (n + 1)) :
    interpolate t.2 w ∈ Convexity.convexHull ℝ (Set.range v) := by
  apply interpolate_mem (IsConvexSet.convexHull (R := ℝ) (s := Set.range v))
  exact homotopyTuples_mem n (IsConvexSet.convexHull (R := ℝ) (s := Set.range v)) v
    (fun i ↦ subset_convexHull_self ⟨i, rfl⟩) t ht

/-- The native simplicial set of all ordered affine vertex tuples. Its face maps literally
omit a vertex, so its actual chain differential squares to zero before interpolation. -/
abbrev tupleSSet (k : ℕ) : SSet where
  obj Δ := Fin (Δ.unop.len + 1) → Simplex k
  map θ := ↾fun v ↦ v ∘ θ.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Native first-vertex cone on the ordered-tuple chain coproduct (Hatcher p.121). -/
def tupleCone (k : ℕ) (R : ModuleCat.{v} K) (b : Simplex k) (n : ℕ) :
    ((tupleSSet k).chainComplex R).X n ⟶ ((tupleSSet k).chainComplex R).X (n + 1) :=
  Sigma.desc fun v ↦ (tupleSSet k).ιChainComplex (R := R) (Fin.cons b v)

/-- The native coproduct cone retains exactly the original ordered vertices. -/
theorem tupleCone_generator (k : ℕ) (R : ModuleCat.{v} K) (b : Simplex k) (n : ℕ)
    (v : Fin (n + 1) → Simplex k) :
    (tupleSSet k).ιChainComplex (R := R) v ≫ tupleCone k R b n =
      (tupleSSet k).ιChainComplex (R := R) (Fin.cons b v) := by
  exact Sigma.ι_comp_desc _ v

/-- ∂c+c∂=id in positive degrees for the genuine ordered-tuple complex.
Source: Hatcher p.121, cancellation of the original alternating cone faces. -/
theorem tupleCone_boundary (k : ℕ) (R : ModuleCat.{v} K) (b : Simplex k) (n : ℕ) :
    tupleCone k R b (n + 1) ≫ ((tupleSSet k).chainComplex R).d (n + 2) (n + 1) +
      ((tupleSSet k).chainComplex R).d (n + 1) n ≫ tupleCone k R b n = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [Preadditive.comp_add, ← Category.assoc, tupleCone_generator, SSet.ιChainComplex_d]
  simp only [← Category.assoc, SSet.ιChainComplex_d,
    Preadditive.sum_comp, Preadditive.zsmul_comp]
  rw [Fin.sum_univ_succ]
  have hface (i : Fin (n + 2)) : (tupleSSet k).δ i v = v ∘ i.succAbove := rfl
  have hcone0 : (tupleSSet k).δ (0 : Fin (n + 3)) (Fin.cons b v) = v := by
    change Fin.cons b v ∘ (0 : Fin (n + 3)).succAbove = v
    simp only [Fin.succAbove_zero, Fin.cons_comp_succ]
  have hcones (i : Fin (n + 2)) :
      (tupleSSet k).δ i.succ (Fin.cons b v) = Fin.cons b (v ∘ i.succAbove) := by
    change Fin.cons b v ∘ i.succ.succAbove = _
    rw [Fin.cons_comp_succ_succAbove]
    rfl
  simp only [Fin.val_zero, pow_zero, one_smul, hcone0, Fin.val_succ, pow_succ,
    hcones, hface, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib,
    tupleCone_generator, Category.comp_id]
  abel

/-- Native augmentation of zeroth ordered-tuple chains, sending each vertex to its
unchanged coefficient. Source: Hatcher p.121, augmented cone convention. -/
def tupleAugmentation (k : ℕ) (R : ModuleCat.{v} K) :
    ((tupleSSet k).chainComplex R).X 0 ⟶ R := Sigma.desc fun _ ↦ 𝟙 R

/-- The degree-zero cone identity retains the necessary augmentation term.
Source: Hatcher p.121; its two endpoints are v and b, in that order of boundary signs. -/
theorem tupleCone_zero_boundary (k : ℕ) (R : ModuleCat.{v} K) (b : Simplex k) :
    tupleCone k R b 0 ≫ ((tupleSSet k).chainComplex R).d 1 0 =
      𝟙 _ - tupleAugmentation k R ≫
        (tupleSSet k).ιChainComplex (R := R) (fun _ : Fin 1 ↦ b) := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [← Category.assoc, tupleCone_generator, SSet.ιChainComplex_d,
    Preadditive.comp_sub, Category.comp_id, ← Category.assoc]
  have he : (tupleSSet k).ιChainComplex (R := R) v ≫ tupleAugmentation k R = 𝟙 R :=
    Sigma.ι_comp_desc _ v
  rw [he, Category.id_comp, Fin.sum_univ_succ]
  have h0 : (tupleSSet k).δ (0 : Fin 2) (Fin.cons b v) = v := by
    change Fin.cons b v ∘ (0 : Fin 2).succAbove = v
    simp
  have h1 : (tupleSSet k).δ (1 : Fin 2) (Fin.cons b v) = (fun _ : Fin 1 ↦ b) := by
    funext i
    fin_cases i
    rfl
  simp [h0, h1, sub_eq_add_neg]

/-- Native augmentation annihilates every degree-one boundary (Hatcher p.121). -/
theorem tuple_boundary_augmentation (k : ℕ) (R : ModuleCat.{v} K) :
    ((tupleSSet k).chainComplex R).d 1 0 ≫ tupleAugmentation k R = 0 := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  have he (w : (tupleSSet k) _⦋0⦌) :
      (tupleSSet k).ιChainComplex (R := R) w ≫ tupleAugmentation k R = 𝟙 R :=
    Sigma.ι_comp_desc _ w
  simp [he, Fin.sum_univ_succ]

/-- The literal native coproduct recursion Sλ=c_b(S∂λ), with S₀=id.
Source: Hatcher pp.121–122; the apex is the actual tuple barycenter. -/
def tupleSubdivision (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ) :
    ((tupleSSet k).chainComplex R).X n ⟶ ((tupleSSet k).chainComplex R).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => Sigma.desc fun v ↦ (tupleSSet k).ιChainComplex (R := R) v ≫
      ((tupleSSet k).chainComplex R).d (n + 1) n ≫ tupleSubdivision k R n ≫
        tupleCone k R (tupleBarycenter v) n

/-- Every tuple generator has the exact recursive subdivision formula. -/
theorem tupleSubdivision_succ_generator (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ)
    (v : Fin (n + 2) → Simplex k) :
    (tupleSSet k).ιChainComplex (R := R) v ≫ tupleSubdivision k R (n + 1) =
      (tupleSSet k).ιChainComplex (R := R) v ≫
        ((tupleSSet k).chainComplex R).d (n + 1) n ≫ tupleSubdivision k R n ≫
          tupleCone k R (tupleBarycenter v) n := by
  exact Sigma.ι_comp_desc _ v

/-- Subdivision commutes with the actual native chain differential in every degree.
Source: Hatcher p.122: the cone identity and ∂²=0 inductively cancel the extra term. -/
theorem tupleSubdivision_boundary (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ) :
    tupleSubdivision k R (n + 1) ≫ ((tupleSSet k).chainComplex R).d (n + 1) n =
      ((tupleSSet k).chainComplex R).d (n + 1) n ≫ tupleSubdivision k R n := by
  induction n with
  | zero =>
    apply SSet.chainComplex_hom_ext
    intro v
    rw [← Category.assoc, tupleSubdivision_succ_generator]
    simp only [tupleSubdivision, Category.id_comp, Category.comp_id]
    simp only [Category.assoc]
    rw [tupleCone_zero_boundary, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, tuple_boundary_augmentation]
    simp
  | succ n ih =>
    apply SSet.chainComplex_hom_ext
    intro v
    rw [← Category.assoc, tupleSubdivision_succ_generator]
    have hc := tupleCone_boundary k R (tupleBarycenter v) n
    have hc' := eq_sub_of_add_eq hc
    simp only [Category.assoc]
    rw [hc', Preadditive.comp_sub, Category.comp_id]
    simp only [← Category.assoc]
    rw [ih, Preadditive.comp_sub]
    simp only [← Category.assoc]
    simp only [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
    simp

/-- Native raising-degree recursion Tλ=c_b(λ−T∂λ), retaining the degenerate T₀ edge.
Source: Hatcher pp.122–123, with actual tuple coproduct morphisms. -/
def tupleHomotopy (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ) :
    ((tupleSSet k).chainComplex R).X n ⟶ ((tupleSSet k).chainComplex R).X (n + 1) :=
  match n with
  | 0 => Sigma.desc fun v ↦ (tupleSSet k).ιChainComplex (R := R) (Fin.cons (v 0) v)
  | n + 1 => Sigma.desc fun v ↦ ((tupleSSet k).ιChainComplex (R := R) v -
      (tupleSSet k).ιChainComplex (R := R) v ≫
        ((tupleSSet k).chainComplex R).d (n + 1) n ≫ tupleHomotopy k R n) ≫
          tupleCone k R (tupleBarycenter v) (n + 1)

/-- The tuple homotopy has exactly Hatcher's signed cone recursion on every generator. -/
theorem tupleHomotopy_succ_generator (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ)
    (v : Fin (n + 2) → Simplex k) :
    (tupleSSet k).ιChainComplex (R := R) v ≫ tupleHomotopy k R (n + 1) =
      ((tupleSSet k).ιChainComplex (R := R) v -
        (tupleSSet k).ιChainComplex (R := R) v ≫
          ((tupleSSet k).chainComplex R).d (n + 1) n ≫ tupleHomotopy k R n) ≫
            tupleCone k R (tupleBarycenter v) (n + 1) := by
  exact Sigma.ι_comp_desc _ v

/-- The degenerate zeroth tuple cone has zero boundary (Hatcher p.122). -/
theorem tupleHomotopy_zero_boundary (k : ℕ) (R : ModuleCat.{v} K) :
    tupleHomotopy k R 0 ≫ ((tupleSSet k).chainComplex R).d 1 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [← Category.assoc]
  have ht : (tupleSSet k).ιChainComplex (R := R) v ≫ tupleHomotopy k R 0 =
      (tupleSSet k).ιChainComplex (R := R) (Fin.cons (v 0) v) := Sigma.ι_comp_desc _ v
  rw [ht, SSet.ιChainComplex_d, Fin.sum_univ_succ]
  have hfaces : (tupleSSet k).δ (0 : Fin 2) (Fin.cons (v 0) v) =
      (tupleSSet k).δ (1 : Fin 2) (Fin.cons (v 0) v) := by
    funext i
    fin_cases i
    rfl
  simp [hfaces]

/-- The literal recursive T is a native chain homotopy from id to S in every positive degree.
Source: Hatcher pp.122–123; cone boundary, augmentation and ∂²=0 prove the identities. -/
theorem tupleHomotopy_boundary (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ) :
    tupleHomotopy k R (n + 1) ≫ ((tupleSSet k).chainComplex R).d (n + 2) (n + 1) +
      ((tupleSSet k).chainComplex R).d (n + 1) n ≫ tupleHomotopy k R n =
        𝟙 _ - tupleSubdivision k R (n + 1) := by
  induction n with
  | zero =>
    apply SSet.chainComplex_hom_ext
    intro v
    rw [Preadditive.comp_add, ← Category.assoc, tupleHomotopy_succ_generator]
    have hc := eq_sub_of_add_eq (tupleCone_boundary k R (tupleBarycenter v) 0)
    have hcycle :
        ((tupleSSet k).ιChainComplex (R := R) v -
          (tupleSSet k).ιChainComplex (R := R) v ≫
            ((tupleSSet k).chainComplex R).d 1 0 ≫ tupleHomotopy k R 0) ≫
              ((tupleSSet k).chainComplex R).d 1 0 =
        (tupleSSet k).ιChainComplex (R := R) v ≫
          ((tupleSSet k).chainComplex R).d 1 0 := by
      simp only [Preadditive.sub_comp, Category.assoc, tupleHomotopy_zero_boundary,
        comp_zero, sub_zero]
    simp only [Category.assoc]
    rw [hc, Preadditive.comp_sub, Category.comp_id]
    simp only [← Category.assoc] at hcycle ⊢
    rw [hcycle, Preadditive.comp_sub, Category.comp_id, tupleSubdivision_succ_generator]
    simp only [tupleSubdivision]
    abel
  | succ n ih =>
    apply SSet.chainComplex_hom_ext
    intro v
    rw [Preadditive.comp_add, ← Category.assoc, tupleHomotopy_succ_generator]
    have hc := eq_sub_of_add_eq (tupleCone_boundary k R (tupleBarycenter v) (n + 1))
    have ht := eq_sub_of_add_eq ih
    have hcycle :
        ((tupleSSet k).ιChainComplex (R := R) v -
          (tupleSSet k).ιChainComplex (R := R) v ≫
            ((tupleSSet k).chainComplex R).d (n + 2) (n + 1) ≫
              tupleHomotopy k R (n + 1)) ≫
                ((tupleSSet k).chainComplex R).d (n + 2) (n + 1) =
        (tupleSSet k).ιChainComplex (R := R) v ≫
          ((tupleSSet k).chainComplex R).d (n + 2) (n + 1) ≫
            tupleSubdivision k R (n + 1) := by
      simp only [Preadditive.sub_comp, Category.assoc]
      rw [ht]
      simp only [Preadditive.comp_sub, Category.comp_id, ← Category.assoc]
      simp only [Category.assoc, HomologicalComplex.d_comp_d, comp_zero, zero_comp]
      abel
    simp only [Category.assoc]
    rw [hc, Preadditive.comp_sub, Category.comp_id]
    simp only [← Category.assoc] at hcycle ⊢
    rw [hcycle, Preadditive.comp_sub, Category.comp_id, tupleSubdivision_succ_generator]
    simp only [Category.assoc]
    abel

/-- Literal finite signed tuple chain in the native coproduct, with no normalization. -/
def tupleSignedMap {k n : ℕ} (R : ModuleCat.{v} K) (terms : SignedTuples k n) :
    R ⟶ ((tupleSSet k).chainComplex R).X n :=
  (terms.map fun t ↦ t.1 • (tupleSSet k).ιChainComplex (R := R) t.2).sum

/-- Signed tuple coning is the actual native cone morphism, with the original signs.
Source: Hatcher pp.121–123; distribute the native morphism over the finite chain. -/
theorem tupleSignedMap_cone {k n : ℕ} (R : ModuleCat.{v} K) (b : Simplex k)
    (a : ℤ) (terms : SignedTuples k n) :
    tupleSignedMap R (terms.map fun t ↦ (a * t.1, Fin.cons b t.2)) =
      a • (tupleSignedMap R terms ≫ tupleCone k R b n) := by
  induction terms with
  | nil => simp [tupleSignedMap]
  | cons t terms ih =>
    simp only [tupleSignedMap, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Preadditive.add_comp, Preadditive.zsmul_comp, tupleCone_generator]
    simp [smul_add, mul_smul]

/-- Finite face-list flattening is the original full alternating finite sum. -/
theorem tupleSignedMap_flatMap {k n m : ℕ} (R : ModuleCat.{v} K)
    (f : Fin m → SignedTuples k n) :
    tupleSignedMap R ((List.finRange m).flatMap f) = ∑ i, tupleSignedMap R (f i) := by
  have hlist (l : List (Fin m)) :
      tupleSignedMap R (l.flatMap f) = (l.map fun i ↦ tupleSignedMap R (f i)).sum := by
    induction l with
    | nil => simp [tupleSignedMap]
    | cons i l ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      simp only [tupleSignedMap, List.map_append, List.sum_append] at ih ⊢
      rw [ih]
  rw [hlist, ← Fin.sum_univ_def]

/-- The native recursive subdivision agrees exactly with the original finite signed list.
Source: Hatcher pp.121–122, so the chain identity applies to the genuine mesh-support list. -/
theorem tupleSubdivision_signed (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ)
    (v : Fin (n + 1) → Simplex k) :
    (tupleSSet k).ιChainComplex (R := R) v ≫ tupleSubdivision k R n =
      tupleSignedMap R (subdivisionTuples n v) := by
  induction n with
  | zero => simp [tupleSubdivision, tupleSignedMap, subdivisionTuples]
  | succ n ih =>
    rw [tupleSubdivision_succ_generator]
    rw [← Category.assoc, ← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
    simp only [subdivisionTuples, tupleSignedMap_flatMap]
    apply Finset.sum_congr rfl
    intro i _
    rw [tupleSignedMap_cone]
    have hf : (tupleSSet k).δ i v = v ∘ i.succAbove := rfl
    rw [hf, ih]

/-- Affine interpolation is an actual simplicial map into the singular simplicial set.
Source: Hatcher p.122; compatibility holds for every face and degeneracy. -/
def tupleRealization (k : ℕ) : tupleSSet k ⟶ TopCat.toSSet.obj (TopCat.of (Simplex k)) where
  app Δ := ↾fun v ↦ ((TopCat.of (Simplex k)).toSSetObjEquiv Δ).symm (affineSimplex v)
  naturality Δ Γ θ := by
    ext v
    change ((TopCat.of (Simplex k)).toSSetObjEquiv Γ).symm
        (affineSimplex (v ∘ θ.unop.toOrderHom)) =
      (TopCat.toSSet.obj (TopCat.of (Simplex k))).map θ
        (((TopCat.of (Simplex k)).toSSetObjEquiv Δ).symm (affineSimplex v))
    have he := TopCat.toSSetObjEquiv_symm_naturality (X := TopCat.of (Simplex k))
      θ.unop (affineSimplex v)
    refine Eq.trans ?_ he.symm
    congr 1
    apply ContinuousMap.ext
    intro w
    exact (interpolate_map v θ.unop.toOrderHom w).symm

/-- The native realization sends the signed tuple list to its actual affine singular chain.
Source: Hatcher p.122, without substituting an opaque chain pairing. -/
theorem tupleSignedMap_realization {k n : ℕ} (R : ModuleCat.{v} K)
    (terms : SignedTuples k n) :
    tupleSignedMap R terms ≫ (SSet.chainComplexMap (tupleRealization k) R).f n =
      signedGeneratorMap R (ContinuousMap.id (Simplex k)) terms := by
  induction terms with
  | nil => simp [tupleSignedMap, signedGeneratorMap]
  | cons t terms ih =>
    simp only [tupleSignedMap, signedGeneratorMap, List.map_cons, List.sum_cons] at ih ⊢
    rw [Preadditive.add_comp, Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f, ih]
    rfl

/-- The actual native tuple homotopy is precisely the original finite signed T list.
Source: Hatcher pp.122–123; no quotient by degenerate tuples is taken. -/
theorem tupleHomotopy_signed (k : ℕ) (R : ModuleCat.{v} K) (n : ℕ)
    (v : Fin (n + 1) → Simplex k) :
    (tupleSSet k).ιChainComplex (R := R) v ≫ tupleHomotopy k R n =
      tupleSignedMap R (homotopyTuples n v) := by
  induction n with
  | zero =>
    rw [show (tupleSSet k).ιChainComplex (R := R) v ≫ tupleHomotopy k R 0 =
      (tupleSSet k).ιChainComplex (R := R) (Fin.cons (v 0) v) from Sigma.ι_comp_desc _ v]
    simp [tupleSignedMap, homotopyTuples]
  | succ n ih =>
    rw [tupleHomotopy_succ_generator, Preadditive.sub_comp, tupleCone_generator]
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
    have hf (i : Fin (n + 2)) : (tupleSSet k).δ i v = v ∘ i.succAbove := rfl
    simp only [hf, ih]
    have happ {m : ℕ} (s t : SignedTuples k m) :
        tupleSignedMap R (s ++ t) = tupleSignedMap R s + tupleSignedMap R t := by
      simp [tupleSignedMap]
    rw [homotopyTuples, happ, tupleSignedMap_flatMap]
    simp only [tupleSignedMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_smul, add_zero]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he := tupleSignedMap_cone R (tupleBarycenter v) (-((-1 : ℤ) ^ i.val))
      (homotopyTuples n (v ∘ i.succAbove))
    simp only [neg_mul] at he
    simpa only [tupleSignedMap, neg_smul] using he.symm

/-- Coefficient change on each original singular simplex is the native coproduct map.
Source: Hatcher p.153, applying an arbitrary abelian-group homomorphism coefficientwise. -/
theorem singular_coefficient_generator (X : TopCat.{u}) {R Q : ModuleCat.{max u v} K}
    (φ : R ⟶ Q) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        (((SSet.chainComplexFunctor (ModuleCat.{max u v} K)).map φ).app (TopCat.toSSet.obj X)).f n =
      φ ≫ (TopCat.toSSet.obj X).ιChainComplex (R := Q) σ := by
  change Sigma.ι (fun _ : (TopCat.toSSet.obj X) _⦋n⦌ ↦ R) σ ≫ CategoryTheory.Limits.Sigma.map (fun _ ↦ φ) = _
  exact Sigma.ι_map _ σ

/-- The actual signed affine list commutes with every coefficient homomorphism.
Source: Hatcher p.153; no freeness or flatness premise is used. -/
theorem signedGeneratorMap_coefficients {X : TopCat.{u}} {k n : ℕ}
    {R Q : ModuleCat.{max u v} K} (φ : R ⟶ Q) (σ : C(Simplex k, X)) (terms : SignedTuples k n) :
    signedGeneratorMap R σ terms ≫
        (((SSet.chainComplexFunctor (ModuleCat.{max u v} K)).map φ).app (TopCat.toSSet.obj X)).f n =
      φ ≫ signedGeneratorMap Q σ terms := by
  induction terms with
  | nil => simp [signedGeneratorMap]
  | cons t terms ih =>
    simp only [signedGeneratorMap, List.map_cons, List.sum_cons] at ih ⊢
    rw [Preadditive.add_comp, Preadditive.zsmul_comp, singular_coefficient_generator, ih]
    simp only [Preadditive.comp_add, Preadditive.comp_zsmul]

/-- The singular S components commute with arbitrary native coefficient changes. -/
theorem subdivisionComponent_coefficients (X : TopCat.{u}) {R Q : ModuleCat.{max u v} K}
    (φ : R ⟶ Q) (n : ℕ) :
    subdivisionComponent X R n ≫
        (((SSet.chainComplexFunctor (ModuleCat.{max u v} K)).map φ).app (TopCat.toSSet.obj X)).f n =
      (((SSet.chainComplexFunctor (ModuleCat.{max u v} K)).map φ).app (TopCat.toSSet.obj X)).f n ≫
        subdivisionComponent X Q n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, subdivisionComponent_generator, signedGeneratorMap_coefficients,
    ← Category.assoc, singular_coefficient_generator, Category.assoc,
    subdivisionComponent_generator]

/-- The singular T components commute with the same native coefficient changes. -/
theorem homotopyComponent_coefficients (X : TopCat.{u}) {R Q : ModuleCat.{max u v} K}
    (φ : R ⟶ Q) (n : ℕ) :
    homotopyComponent X R n ≫
        (((SSet.chainComplexFunctor (ModuleCat.{max u v} K)).map φ).app (TopCat.toSSet.obj X)).f (n + 1) =
      (((SSet.chainComplexFunctor (ModuleCat.{max u v} K)).map φ).app (TopCat.toSSet.obj X)).f n ≫
        homotopyComponent X Q n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, homotopyComponent_generator, signedGeneratorMap_coefficients,
    ← Category.assoc, singular_coefficient_generator, Category.assoc,
    homotopyComponent_generator]


/-- Affine interpolation preserves each actual equal-weight tuple barycenter. -/
theorem interpolate_barycenter {l k n : ℕ} (u : Fin (k + 1) → Simplex l)
    (v : Fin (n + 1) → Simplex k) :
    interpolate u (tupleBarycenter v) = tupleBarycenter (interpolate u ∘ v) := by
  exact (iConvexComb_assoc (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) v u).symm

/-- The signed S recursion preserves affine vertex interpolation, including its face signs.
Source: Hatcher p.122, the actual affine compatibility needed for singular faces. -/
theorem subdivisionTuples_interpolate {l k : ℕ} (u : Fin (k + 1) → Simplex l)
    (n : ℕ) (v : Fin (n + 1) → Simplex k) :
    subdivisionTuples n (interpolate u ∘ v) =
      (subdivisionTuples n v).map (fun t ↦ (t.1, interpolate u ∘ t.2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [subdivisionTuples, List.map_flatMap, List.map_map]
    apply congrArg (fun f ↦ (List.finRange (n + 2)).flatMap f)
    funext i
    rw [show (interpolate u ∘ v) ∘ i.succAbove = interpolate u ∘ (v ∘ i.succAbove) from rfl,
      ih, List.map_map]
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply]
    apply Prod.ext
    · rfl
    · rw [← interpolate_barycenter]
      funext j
      exact Fin.cases rfl (fun _ ↦ rfl) j

/-- Composition of actual affine simplices equals interpolation of their vertex images. -/
theorem affineSimplex_comp {l k n : ℕ} (u : Fin (k + 1) → Simplex l)
    (v : Fin (n + 1) → Simplex k) :
    (affineSimplex u).comp (affineSimplex v) = affineSimplex (interpolate u ∘ v) := by
  apply ContinuousMap.ext
  intro w
  exact (iConvexComb_assoc w v u).symm

/-- The actual signed affine chain respects interpolation of its original vertex tuples. -/
theorem signedGeneratorMap_interpolate {X : TopCat.{u}} {l k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex l, X)) (u : Fin (k + 1) → Simplex l) (terms : SignedTuples k n) :
    signedGeneratorMap R σ (terms.map (fun t ↦ (t.1, interpolate u ∘ t.2))) =
      signedGeneratorMap R (σ.comp (affineSimplex u)) terms := by
  simp only [signedGeneratorMap, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [← affineSimplex_comp]
  rfl

/-- Native singular-chain map realizing tuples and postcomposing with the original σ. -/
def tupleInto {X : TopCat.{u}} {k : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) :
    (tupleSSet k).chainComplex R ⟶ (TopCat.toSSet.obj X).chainComplex R where
  f n := Sigma.desc fun v ↦ (TopCat.toSSet.obj X).ιChainComplex (R := R)
    ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex v)))
  comm' i j h := by
    have hi : i = j + 1 := h.symm
    subst i
    apply SSet.chainComplex_hom_ext
    intro v
    have hg (n : ℕ) (w : (tupleSSet k).obj (op ⦋n⦌)) :
        (tupleSSet k).ιChainComplex (R := R) w ≫
          (Sigma.desc fun w ↦ (TopCat.toSSet.obj X).ιChainComplex (R := R)
            ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex w)))) =
        (TopCat.toSSet.obj X).ιChainComplex (R := R)
          ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex w))) :=
      Sigma.ι_comp_desc _ w
    rw [← Category.assoc, hg, affine_generator_boundary, SSet.ιChainComplex_d_assoc]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hg]
    rfl

/-- This realization sends every tuple generator to its actual affine singular simplex. -/
theorem tupleInto_generator {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (v : Fin (n + 1) → Simplex k) :
    (tupleSSet k).ιChainComplex (R := R) v ≫ (tupleInto R σ).f n =
      (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex v))) := by
  exact Sigma.ι_comp_desc _ v

/-- Every finite signed tuple chain realizes to precisely its original signed singular chain. -/
theorem tupleSignedMap_into {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (terms : SignedTuples k n) :
    tupleSignedMap R terms ≫ (tupleInto R σ).f n = signedGeneratorMap R σ terms := by
  induction terms with
  | nil => simp [tupleSignedMap, signedGeneratorMap]
  | cons t terms ih =>
    simp only [tupleSignedMap, signedGeneratorMap, List.map_cons, List.sum_cons] at ih ⊢
    rw [Preadditive.add_comp, Preadditive.zsmul_comp, tupleInto_generator, ih]

/-- An actual affine singular generator subdivides using its own genuine vertex tuple.
Source: Hatcher p.122, affine compatibility of the signed barycentric recursion. -/
theorem subdivisionComponent_affine_generator {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (v : Fin (n + 1) → Simplex k) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex v))) ≫
          subdivisionComponent X R n = signedGeneratorMap R σ (subdivisionTuples n v) := by
  rw [subdivisionComponent_generator, Equiv.apply_symm_apply]
  have hv : interpolate v ∘ (fun i : Fin (n + 1) ↦ StdSimplex.single i) = v := by
    funext i
    exact iConvexComb_single i v
  rw [← hv, subdivisionTuples_interpolate, signedGeneratorMap_interpolate, hv]

/-- The genuine tuple S realizes to the original singular S, in every degree. -/
theorem tupleSubdivision_into {X : TopCat.{u}} {k : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (n : ℕ) :
    tupleSubdivision k R n ≫ (tupleInto R σ).f n =
      (tupleInto R σ).f n ≫ subdivisionComponent X R n := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [← Category.assoc, tupleSubdivision_signed, tupleSignedMap_into,
    ← Category.assoc, tupleInto_generator, subdivisionComponent_affine_generator]

/-- The standard ordered tuple realizes to the original singular generator itself. -/
theorem tupleInto_standard_generator {X : TopCat.{u}} {n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (tupleSSet n).ιChainComplex (R := R) (fun i ↦ StdSimplex.single i) ≫
        (tupleInto R (X.toSSetObjEquiv (op ⦋n⦌) σ)).f n =
      (TopCat.toSSet.obj X).ιChainComplex (R := R) σ := by
  rw [tupleInto_generator, affineSimplex_identity]
  simp

/-- The original native singular subdivision commutes with ∂ in every degree.
Source: Hatcher p.122; transport the proved tuple identity through actual singular realization. -/
theorem subdivisionComponent_boundary (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (n : ℕ) :
    subdivisionComponent X R (n + 1) ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n =
      ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ subdivisionComponent X R n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  let F := tupleInto R (X.toSSetObjEquiv (op ⦋n + 1⦌) σ)
  have hstd := tupleInto_standard_generator R σ
  change (tupleSSet (n + 1)).ιChainComplex (R := R) (fun i ↦ StdSimplex.single i) ≫
    F.f (n + 1) = (TopCat.toSSet.obj X).ιChainComplex (R := R) σ at hstd
  have hSp : F.f (n + 1) ≫ subdivisionComponent X R (n + 1) =
      tupleSubdivision (n + 1) R (n + 1) ≫ F.f (n + 1) :=
    (tupleSubdivision_into R (X.toSSetObjEquiv (op ⦋n + 1⦌) σ) (n + 1)).symm
  have hSn : tupleSubdivision (n + 1) R n ≫ F.f n =
      F.f n ≫ subdivisionComponent X R n :=
    tupleSubdivision_into R (X.toSSetObjEquiv (op ⦋n + 1⦌) σ) n
  rw [← hstd]
  simp only [Category.assoc]
  rw [← Category.assoc (F.f (n + 1)) (subdivisionComponent X R (n + 1)), hSp]
  simp only [Category.assoc]
  rw [F.comm]
  rw [← Category.assoc (tupleSubdivision (n + 1) R (n + 1)), tupleSubdivision_boundary]
  simp only [Category.assoc]
  rw [hSn, ← Category.assoc (F.f (n + 1)), F.comm]
  simp only [Category.assoc]

/-- The signed T recursion preserves every actual affine interpolation, including T₀.
Source: Hatcher p.123, literal affine compatibility of its degenerate cone recursion. -/
theorem homotopyTuples_interpolate {l k : ℕ} (u : Fin (k + 1) → Simplex l)
    (n : ℕ) (v : Fin (n + 1) → Simplex k) :
    homotopyTuples n (interpolate u ∘ v) =
      (homotopyTuples n v).map (fun t ↦ (t.1, interpolate u ∘ t.2)) := by
  induction n with
  | zero =>
    simp only [homotopyTuples, List.map_cons, List.map_nil]
    apply congrArg (fun t ↦ [t])
    apply Prod.ext
    · rfl
    · funext j
      exact Fin.cases rfl (fun _ ↦ rfl) j
  | succ n ih =>
    simp only [homotopyTuples, List.map_append, List.map_cons, List.map_nil,
      List.map_flatMap, List.map_map]
    apply congrArg₂ (· ++ ·)
    · apply congrArg (fun t ↦ [t])
      apply Prod.ext
      · rfl
      · rw [← interpolate_barycenter]
        funext j
        exact Fin.cases rfl (fun _ ↦ rfl) j
    · apply congrArg (fun f ↦ (List.finRange (n + 2)).flatMap f)
      funext i
      rw [show (interpolate u ∘ v) ∘ i.succAbove = interpolate u ∘ (v ∘ i.succAbove) from rfl,
        ih, List.map_map]
      apply List.map_congr_left
      intro t _
      simp only [Function.comp_apply]
      apply Prod.ext
      · rfl
      · rw [← interpolate_barycenter]
        funext j
        exact Fin.cases rfl (fun _ ↦ rfl) j

/-- An actual affine singular generator has precisely the signed T list on its own tuple. -/
theorem homotopyComponent_affine_generator {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (v : Fin (n + 1) → Simplex k) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex v))) ≫
          homotopyComponent X R n = signedGeneratorMap R σ (homotopyTuples n v) := by
  rw [homotopyComponent_generator, Equiv.apply_symm_apply]
  have hv : interpolate v ∘ (fun i : Fin (n + 1) ↦ StdSimplex.single i) = v := by
    funext i
    exact iConvexComb_single i v
  rw [← hv, homotopyTuples_interpolate, signedGeneratorMap_interpolate, hv]

/-- The proved native tuple T realizes to the original singular T component. -/
theorem tupleHomotopy_into {X : TopCat.{u}} {k : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (n : ℕ) :
    tupleHomotopy k R n ≫ (tupleInto R σ).f (n + 1) =
      (tupleInto R σ).f n ≫ homotopyComponent X R n := by
  apply SSet.chainComplex_hom_ext
  intro v
  rw [← Category.assoc, tupleHomotopy_signed, tupleSignedMap_into,
    ← Category.assoc, tupleInto_generator, homotopyComponent_affine_generator]

/-- The original signed native singular T satisfies ∂T+T∂=id−S in every positive degree.
Source: Hatcher p.123; transport the exact tuple cone identities to the original singular chains. -/
theorem homotopyComponent_boundary (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (n : ℕ) :
    homotopyComponent X R (n + 1) ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) +
      ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ homotopyComponent X R n =
        𝟙 _ - subdivisionComponent X R (n + 1) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  let F := tupleInto R (X.toSSetObjEquiv (op ⦋n + 1⦌) σ)
  have hstd := tupleInto_standard_generator R σ
  change (tupleSSet (n + 1)).ιChainComplex (R := R) (fun i ↦ StdSimplex.single i) ≫
    F.f (n + 1) = (TopCat.toSSet.obj X).ιChainComplex (R := R) σ at hstd
  have hTp : F.f (n + 1) ≫ homotopyComponent X R (n + 1) =
      tupleHomotopy (n + 1) R (n + 1) ≫ F.f (n + 2) :=
    (tupleHomotopy_into R (X.toSSetObjEquiv (op ⦋n + 1⦌) σ) (n + 1)).symm
  have hTn : F.f n ≫ homotopyComponent X R n =
      tupleHomotopy (n + 1) R n ≫ F.f (n + 1) :=
    (tupleHomotopy_into R (X.toSSetObjEquiv (op ⦋n + 1⦌) σ) n).symm
  have hSp : tupleSubdivision (n + 1) R (n + 1) ≫ F.f (n + 1) =
      F.f (n + 1) ≫ subdivisionComponent X R (n + 1) :=
    tupleSubdivision_into R (X.toSSetObjEquiv (op ⦋n + 1⦌) σ) (n + 1)
  have he := congrArg (fun f ↦ f ≫ F.f (n + 1))
    (tupleHomotopy_boundary (n + 1) R n)
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.id_comp,
    Category.assoc] at he
  rw [← F.comm, hSp] at he
  rw [← hstd]
  simp only [Preadditive.comp_add, Preadditive.comp_sub, Category.comp_id, Category.assoc]
  rw [← Category.assoc (F.f (n + 1)) (homotopyComponent X R (n + 1)), hTp,
    ← Category.assoc (F.f (n + 1)) (((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n),
    F.comm]
  simp only [Category.assoc]
  rw [hTn]
  have he' := congrArg (fun f ↦
    (tupleSSet (n + 1)).ιChainComplex (R := R) (fun i ↦ StdSimplex.single i) ≫ f) he
  simpa only [Preadditive.comp_add, Preadditive.comp_sub, Category.assoc] using he'

/-- Genuine native barycentric subdivision chain endomorphism.
Source: Hatcher p.122, with the proved exact signed component boundary identities. -/
def subdivisionChainMap (X : TopCat.{u}) (R : ModuleCat.{max u v} K) :
    (TopCat.toSSet.obj X).chainComplex R ⟶ (TopCat.toSSet.obj X).chainComplex R where
  f n := subdivisionComponent X R n
  comm' i j h := by
    have hi : i = j + 1 := h.symm
    subst i
    exact subdivisionComponent_boundary X R j

/-- The literal degree-raising T components, zero off the actual chain-complex homotopy shape. -/
def homotopyFamily (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (i j : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X i ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X j :=
  if h : i + 1 = j then homotopyComponent X R i ≫
    eqToHom (congrArg ((TopCat.toSSet.obj X).chainComplex R).X h) else 0

/-- Actual native homotopy from identity to barycentric subdivision.
Source: Hatcher p.123; the proved component identities include zero and degenerate simplices. -/
def subdivisionHomotopy (X : TopCat.{u}) (R : ModuleCat.{max u v} K) :
    Homotopy (𝟙 ((TopCat.toSSet.obj X).chainComplex R)) (subdivisionChainMap X R) where
  hom := homotopyFamily X R
  zero i j h := by
    have hij : ¬ i + 1 = j := by
      intro he
      apply h
      exact he
    simp [homotopyFamily, hij]
  comm i := by
    cases i with
    | zero =>
      rw [dNext_eq_zero _ 0 (by simp), prevD_eq _ (show
        (ComplexShape.down ℕ).Rel 1 0 from rfl)]
      simp [homotopyFamily, subdivisionChainMap, homotopyComponent_zero_boundary,
        subdivisionComponent_zero]
    | succ n =>
      have he := homotopyComponent_boundary X R n
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)]
      simp only [homotopyFamily, dite_eq_left rfl, eqToHom_refl, Category.comp_id,
        subdivisionChainMap]
      change 𝟙 _ = ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫
          homotopyComponent X R n + homotopyComponent X R (n + 1) ≫
            ((TopCat.toSSet.obj X).chainComplex R).d (n + 2) (n + 1) +
              subdivisionComponent X R (n + 1)
      rw [add_comm _ (homotopyComponent X R (n + 1) ≫ _), he]
      abel

/-- The actual affine simplex weights are the literal finite vector convex combination.
Source: Hatcher p.121, the normed-coordinate form of linear interpolation. -/
theorem interpolate_weights_vector {k n : ℕ} (v : Fin (n + 1) → Simplex k)
    (w : Simplex n) :
    (fun j ↦ (interpolate v w).weights j) =
      ∑ i, w.weights i • (fun j ↦ (v i).weights j) := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact interpolate_weights v w j

/-- The normed-vector distance to an actual convex combination is bounded by the same
convex combination of vertex distances. Source: Hatcher p.120, finite triangle inequality. -/
theorem dist_weights_interpolate_le {k n : ℕ} (v : Fin (n + 1) → Simplex k)
    (w : Simplex n) (b : Simplex k) :
    dist (fun j ↦ b.weights j) (fun j ↦ (interpolate v w).weights j) ≤
      ∑ i, w.weights i * dist (fun j ↦ b.weights j) (fun j ↦ (v i).weights j) := by
  let : ConvexSpace ℝ (Fin (k + 1) → ℝ) := ConvexSpace.ofModule
  rw [interpolate_weights_vector]
  have hcomb : iConvexComb w (fun i j ↦ (v i).weights j) =
      ∑ i, w.weights i • (fun j ↦ (v i).weights j) := by
    rw [iConvexComb_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
  rw [← hcomb]
  have he := dist_iConvexComb_right_le (fun j ↦ b.weights j) w
    (fun i j ↦ (v i).weights j)
  rw [iConvexComb_eq_sum, iConvexComb_eq_sum] at he
  rw [Finsupp.sum_fintype _ _ (by intro i; simp),
    Finsupp.sum_fintype _ _ (by intro i; simp)] at he
  rw [hcomb]
  simpa only [smul_eq_mul] using he

/-- The real coordinate bound passes from all original vertices to every actual affine point.
Source: Hatcher p.120, normalized nonnegative convex weights. -/
theorem dist_weights_interpolate_bound {k n : ℕ} (v : Fin (n + 1) → Simplex k)
    (w : Simplex n) (b : Simplex k) (D : ℝ)
    (hv : ∀ i, dist (fun j ↦ b.weights j) (fun j ↦ (v i).weights j) ≤ D) :
    dist (fun j ↦ b.weights j) (fun j ↦ (interpolate v w).weights j) ≤ D := by
  refine (dist_weights_interpolate_le v w b).trans ?_
  calc
    (∑ i, w.weights i * dist (fun j ↦ b.weights j) (fun j ↦ (v i).weights j)) ≤
        ∑ i, w.weights i * D := Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hv i) (w.weights_nonneg i)
    _ = D := by
      rw [← Finset.sum_mul]
      have hw : ∑ i, w.weights i = 1 := by
        have ht := w.total
        rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)] at ht
        exact ht
      rw [hw, one_mul]

/-- The full tuple barycenter is at most n/(n+1) times the original vertex diameter
from each vertex. Source: Hatcher p.120; the self-distance term is exactly zero. -/
theorem barycenter_weights_dist_vertex {k n : ℕ} (v : Fin (n + 1) → Simplex k)
    (D : ℝ) (hv : ∀ i j, dist (fun a ↦ (v i).weights a) (fun a ↦ (v j).weights a) ≤ D)
    (i : Fin (n + 1)) :
    dist (fun a ↦ (tupleBarycenter v).weights a) (fun a ↦ (v i).weights a) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) * D := by
  rw [dist_comm]
  refine (dist_weights_interpolate_le v
    (StdSimplex.barycenter (K := ℝ) (M := Fin (n + 1))) (v i)).trans ?_
  simp only [StdSimplex.weights_barycenter_apply, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one]
  have hsum : (∑ j : Fin (n + 1),
      dist (fun a ↦ (v i).weights a) (fun a ↦ (v j).weights a)) ≤ (n : ℝ) * D := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [dist_self, add_zero]
    calc
      _ ≤ ∑ _j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, D :=
        Finset.sum_le_sum fun j _ ↦ hv i j
      _ = (n : ℝ) * D := by simp
  rw [← Finset.mul_sum]
  calc
    ((n : ℝ) + 1)⁻¹ * ∑ j, dist (fun a ↦ (v i).weights a) (fun a ↦ (v j).weights a) ≤
        ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (by positivity))
    _ = ((n : ℝ) / ((n : ℝ) + 1)) * D := by ring

/-- Each actual S-list vertex is literally an affine combination of the original tuple.
Source: Hatcher pp.121–122; this retains a witness rather than only hull membership. -/
theorem subdivisionTuples_vertex_interpolation {k : ℕ} (n : ℕ)
    (v : Fin (n + 1) → Simplex k) :
    ∀ t ∈ subdivisionTuples n v, ∀ j, ∃ w : Simplex n, t.2 j = interpolate v w := by
  induction n with
  | zero =>
    intro t ht j
    simp only [subdivisionTuples, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    exact ⟨StdSimplex.single j, (iConvexComb_single j v).symm⟩
  | succ n ih =>
    intro t ht j
    simp only [subdivisionTuples, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨i, _, a, ha, rfl⟩ := ht
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · exact ⟨StdSimplex.barycenter, rfl⟩
    · obtain ⟨w, hw⟩ := ih (v ∘ i.succAbove) a ha j
      exact ⟨StdSimplex.map i.succAbove w, hw.trans (interpolate_map v i.succAbove w).symm⟩

/-- Every actual barycentric child vertex pair satisfies the exact n/(n+1) mesh bound.
Source: Hatcher p.120, coning the subdivided face to the full barycenter, including n=0. -/
theorem subdivisionTuples_weights_mesh {k : ℕ} (n : ℕ)
    (v : Fin (n + 1) → Simplex k) (D : ℝ)
    (hv : ∀ i j, dist (fun a ↦ (v i).weights a) (fun a ↦ (v j).weights a) ≤ D) :
    ∀ t ∈ subdivisionTuples n v, ∀ i j,
      dist (fun a ↦ (t.2 i).weights a) (fun a ↦ (t.2 j).weights a) ≤
        ((n : ℝ) / ((n : ℝ) + 1)) * D := by
  have hD : 0 ≤ D := by simpa using hv 0 0
  induction n with
  | zero =>
    intro t ht i j
    simp only [subdivisionTuples, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    have hij : i = j := by omega
    simp [hij]
  | succ n ih =>
    intro t ht i j
    simp only [subdivisionTuples, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨f, _, a, ha, rfl⟩ := ht
    have hface : ∀ i j, dist (fun b ↦ (v (f.succAbove i)).weights b)
        (fun b ↦ (v (f.succAbove j)).weights b) ≤ D := fun i j ↦ hv _ _
    have hapex (j : Fin (n + 1)) :
        dist (fun b ↦ (tupleBarycenter v).weights b) (fun b ↦ (a.2 j).weights b) ≤
          (((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) * D := by
      obtain ⟨w, hw⟩ := subdivisionTuples_vertex_interpolation (n + 1) v
        ((-1 : ℤ) ^ f.val * a.1, Fin.cons (tupleBarycenter v) a.2)
        (by simp only [subdivisionTuples, List.mem_flatMap, List.mem_map]
            exact ⟨f, List.mem_finRange f, a, ha, rfl⟩) j.succ
      change a.2 j = interpolate v w at hw
      rw [hw]
      exact dist_weights_interpolate_bound v w (tupleBarycenter v) _
        (barycenter_weights_dist_vertex v D hv)
    have hratio : (n : ℝ) / ((n : ℝ) + 1) ≤
        ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero, dist_self]
        positivity
      · exact hapex j
    · refine Fin.cases ?_ (fun j ↦ ?_) j
      · simpa only [Fin.cons_zero, Fin.cons_succ, dist_comm] using hapex i
      · exact (ih (v ∘ f.succAbove) hface a ha i j).trans
          (mul_le_mul_of_nonneg_right (by convert hratio using 1; push_cast; ring) hD)

/-- Two arbitrary affine points of a tuple satisfy its same vertex-pair diameter bound.
Source: Hatcher p.120, apply the finite convex-distance estimate successively to both points. -/
theorem dist_weights_interpolate_pair_bound {k n : ℕ} (v : Fin (n + 1) → Simplex k)
    (D : ℝ) (hv : ∀ i j, dist (fun a ↦ (v i).weights a) (fun a ↦ (v j).weights a) ≤ D)
    (w z : Simplex n) :
    dist (fun a ↦ (interpolate v w).weights a) (fun a ↦ (interpolate v z).weights a) ≤ D := by
  rw [dist_comm]
  apply dist_weights_interpolate_bound v w (interpolate v z) D
  intro i
  rw [dist_comm]
  exact dist_weights_interpolate_bound v z (v i) D (hv i)

/-- The actual finite iterated signed subdivision tuples, retaining coefficients and repetitions.
Source: Hatcher pp.122–124, repeatedly apply the same fixed-dimension S recursion. -/
def iteratedSubdivisionTuples {k : ℕ} (n r : ℕ)
    (v : Fin (n + 1) → Simplex k) : SignedTuples k n :=
  match r with
  | 0 => [(1, v)]
  | r + 1 => (subdivisionTuples n v).flatMap fun t ↦
      (iteratedSubdivisionTuples n r t.2).map fun a ↦ (t.1 * a.1, a.2)

/-- Every actual r-fold signed descendant has the same fixed-dimensional q^r mesh bound.
Source: Hatcher p.121, iterate the shape-independent one-step estimate without changing n. -/
theorem iteratedSubdivisionTuples_weights_mesh {k : ℕ} (n r : ℕ)
    (v : Fin (n + 1) → Simplex k) (D : ℝ)
    (hv : ∀ i j, dist (fun a ↦ (v i).weights a) (fun a ↦ (v j).weights a) ≤ D) :
    ∀ t ∈ iteratedSubdivisionTuples n r v, ∀ i j,
      dist (fun a ↦ (t.2 i).weights a) (fun a ↦ (t.2 j).weights a) ≤
        ((n : ℝ) / ((n : ℝ) + 1)) ^ r * D := by
  induction r generalizing v D with
  | zero =>
    intro t ht i j
    simp only [iteratedSubdivisionTuples, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    simpa using hv i j
  | succ r ih =>
    intro t ht i j
    simp only [iteratedSubdivisionTuples, List.mem_flatMap, List.mem_map] at ht
    obtain ⟨s, hs, a, ha, rfl⟩ := ht
    have hstep := subdivisionTuples_weights_mesh n v D hv s hs
    have he := ih s.2 (((n : ℝ) / ((n : ℝ) + 1)) * D) hstep a ha i j
    simpa only [pow_succ, mul_assoc] using he

/-- The full affine image of every iterated descendant satisfies the exact q^r diameter bound.
Source: Hatcher pp.120–121; this controls all simplex points, not only its vertices. -/
theorem iteratedSubdivisionTuples_image_mesh {k : ℕ} (n r : ℕ)
    (v : Fin (n + 1) → Simplex k) (D : ℝ)
    (hv : ∀ i j, dist (fun a ↦ (v i).weights a) (fun a ↦ (v j).weights a) ≤ D)
    {t : ℤ × (Fin (n + 1) → Simplex k)} (ht : t ∈ iteratedSubdivisionTuples n r v)
    (w z : Simplex n) :
    dist (fun a ↦ (interpolate t.2 w).weights a) (fun a ↦ (interpolate t.2 z).weights a) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) ^ r * D :=
  dist_weights_interpolate_pair_bound t.2 _
    (iteratedSubdivisionTuples_weights_mesh n r v D hv t ht) w z


/-- Pull back the ambient weights metric along the native closed-simplex embedding; this
preserves the standard simplex topology and enables compact metric cover arguments. -/
theorem standard_simplex_lebesgue_number_weights {k : ℕ} (𝒰 : Set (Set (Simplex k)))
    (hopen : ∀ U ∈ 𝒰, IsOpen U) (hcover : (Set.univ : Set (Simplex k)) ⊆ ⋃₀ 𝒰) :
    ∃ δ > 0, ∀ x : Simplex k, ∃ U ∈ 𝒰, Metric.ball x δ ⊆ U := by
  simpa only [Set.subset_univ, Set.mem_univ, true_implies] using
    lebesgue_number_lemma_of_metric_sUnion (s := (Set.univ : Set (Simplex k)))
      isCompact_univ hopen hcover

/-- All points of the native simplex have coordinate distance at most one.
Source: Hatcher p.120; Mathlib's diameter bound for the compact weights realization. -/
theorem simplex_weights_dist_le_one {k : ℕ} (x y : Simplex k) :
    dist (fun j ↦ x.weights j) (fun j ↦ y.weights j) ≤ 1 :=
  (Metric.dist_le_diam_of_mem (StdSimplex.isBounded_range_toFun_comp_weights _)
    (Set.mem_range_self x) (Set.mem_range_self y)).trans
      (StdSimplex.diam_range_toFun_comp_weights_subset_closedBall _)

/-- Every sufficiently deep actual signed descendant is contained in one open-cover member.
Source: Hatcher Proposition 2.21(3), p.123. The weights metric induces the native topology;
its Lebesgue radius and the q^r mesh estimate give a depth valid for all later iterates.
The ratio is also less than one in dimension zero, where it equals zero. -/
theorem iteratedSubdivisionTuples_eventually_small {k n : ℕ}
    (v : Fin (n + 1) → Simplex k) (𝒰 : Set (Set (Simplex k)))
    (hopen : ∀ U ∈ 𝒰, IsOpen U) (hcover : (Set.univ : Set (Simplex k)) ⊆ ⋃₀ 𝒰) :
    ∃ N : ℕ, ∀ r ≥ N, ∀ t ∈ iteratedSubdivisionTuples n r v,
      ∃ U ∈ 𝒰, Set.range (affineSimplex t.2) ⊆ U := by
  obtain ⟨δ, hδ, hball⟩ := standard_simplex_lebesgue_number_weights 𝒰 hopen hcover
  have hq0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hq1 : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually_lt_const hδ)
  refine ⟨N, fun r hr t ht ↦ ?_⟩
  obtain ⟨U, hU, hsub⟩ := hball (interpolate t.2 (StdSimplex.single 0))
  refine ⟨U, hU, fun x hx ↦ hsub ?_⟩
  obtain ⟨w, rfl⟩ := hx
  change dist (fun j ↦ (interpolate t.2 w).weights j)
    (fun j ↦ (interpolate t.2 (StdSimplex.single 0)).weights j) < δ
  have hmesh := iteratedSubdivisionTuples_image_mesh n r v 1
    (fun i j ↦ simplex_weights_dist_le_one (v i) (v j)) ht w (StdSimplex.single 0)
  exact lt_of_le_of_lt (by simpa only [mul_one] using hmesh) (hN r hr)

/-- A continuous singular simplex has a depth after which every actual subdivision term
lies wholly in A or wholly in B. Source: Hatcher p.123, the pulled-back interiors cover.
The assertion is about each term before any cancellation of its coefficient. -/
theorem singular_simplex_eventually_small {X : TopCat.{u}} (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) {n : ℕ} (σ : C(Simplex n, X)) :
    ∃ N : ℕ, ∀ r ≥ N,
      ∀ t ∈ iteratedSubdivisionTuples n r (fun i ↦ StdSimplex.single i),
        Set.range (σ.comp (affineSimplex t.2)) ⊆ A ∨
          Set.range (σ.comp (affineSimplex t.2)) ⊆ B := by
  let 𝒰 : Set (Set (Simplex n)) := {σ ⁻¹' interior A, σ ⁻¹' interior B}
  have hopen : ∀ U ∈ 𝒰, IsOpen U := by
    intro U hU
    rcases hU with rfl | hU
    · exact isOpen_interior.preimage σ.continuous
    · obtain rfl := Set.mem_singleton_iff.mp hU
      exact isOpen_interior.preimage σ.continuous
  have hc : (Set.univ : Set (Simplex n)) ⊆ ⋃₀ 𝒰 := by
    intro x _
    have hx : σ x ∈ interior A ∪ interior B := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact Set.mem_sUnion.mpr ⟨_, Set.mem_insert _ _, hx⟩
    · exact Set.mem_sUnion.mpr ⟨_, Set.mem_insert_of_mem _ (Set.mem_singleton _), hx⟩
  obtain ⟨N, hN⟩ := iteratedSubdivisionTuples_eventually_small
    (fun i : Fin (n + 1) ↦ StdSimplex.single i) 𝒰 hopen hc
  refine ⟨N, fun r hr t ht ↦ ?_⟩
  obtain ⟨U, hU, hs⟩ := hN r hr t ht
  rcases hU with rfl | hU
  · left
    rintro _ ⟨w, rfl⟩
    exact interior_subset (hs (Set.mem_range_self w))
  · obtain rfl := Set.mem_singleton_iff.mp hU
    right
    rintro _ ⟨w, rfl⟩
    exact interior_subset (hs (Set.mem_range_self w))

/-- A finite family of singular simplices has a common eventual subdivision depth.
Source: Hatcher p.123. Take the maximum of the individual depths; empty families use zero. -/
theorem finite_singular_simplices_eventually_small {X : TopCat.{u}} (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) {n : ℕ}
    (F : Finset C(Simplex n, X)) :
    ∃ N : ℕ, ∀ σ ∈ F, ∀ r ≥ N,
      ∀ t ∈ iteratedSubdivisionTuples n r (fun i ↦ StdSimplex.single i),
        Set.range (σ.comp (affineSimplex t.2)) ⊆ A ∨
          Set.range (σ.comp (affineSimplex t.2)) ⊆ B := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert σ F hσ ih =>
    obtain ⟨N, hN⟩ := singular_simplex_eventually_small A B hcover σ
    obtain ⟨M, hM⟩ := ih
    refine ⟨max N M, fun τ hτ r hr t ht ↦ ?_⟩
    rcases Finset.mem_insert.mp hτ with rfl | hτ
    · exact hN r ((le_max_left N M).trans hr) t ht
    · exact hM τ hτ r ((le_max_right N M).trans hr) t ht

/-- Multiplying every signed coefficient scales the actual native generator map.
Source: Hatcher pp.121–123, distributivity for arbitrary integer-module coefficients. -/
theorem signedGeneratorMap_scale {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (a : ℤ) (terms : SignedTuples k n) :
    signedGeneratorMap R σ (terms.map fun t ↦ (a * t.1, t.2)) =
      a • signedGeneratorMap R σ terms := by
  induction terms with
  | nil => simp [signedGeneratorMap]
  | cons t terms ih =>
    simp only [signedGeneratorMap, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, smul_add, mul_smul]

/-- The iterated signed-list recursion realizes to the literal power of native subdivision.
Source: Hatcher pp.122–123. Expand each coefficient summand and use affine compatibility;
this identifies the geometric descendants with the actual chain operator for every R. -/
theorem iteratedSubdivisionTuples_generator {X : TopCat.{u}} {k n : ℕ} (R : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (r : ℕ) (v : Fin (n + 1) → Simplex k) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R)
        ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex v))) ≫
          (End.of (subdivisionComponent X R n)) ^ r =
      signedGeneratorMap R σ (iteratedSubdivisionTuples n r v) := by
  induction r generalizing v with
  | zero => simp [iteratedSubdivisionTuples, signedGeneratorMap]
  | succ r ih =>
    rw [pow_succ, End.mul_def, ← Category.assoc, subdivisionComponent_affine_generator]
    have hlist (terms : SignedTuples k n) :
        signedGeneratorMap R σ terms ≫ (End.of (subdivisionComponent X R n)) ^ r =
          signedGeneratorMap R σ (terms.flatMap fun t ↦
            (iteratedSubdivisionTuples n r t.2).map fun a ↦ (t.1 * a.1, a.2)) := by
      induction terms with
      | nil => simp [signedGeneratorMap]
      | cons t terms hterms =>
        simp only [List.flatMap_cons]
        change (t.1 • (TopCat.toSSet.obj X).ιChainComplex
          ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex t.2))) +
            signedGeneratorMap R σ terms) ≫ _ = _
        rw [Preadditive.add_comp, Preadditive.zsmul_comp, ih, hterms]
        simp only [signedGeneratorMap, List.map_append, List.sum_append]
        exact congrArg (fun z ↦ z + _) (signedGeneratorMap_scale R σ t.1
          (iteratedSubdivisionTuples n r t.2)).symm
    exact hlist (subdivisionTuples n v)

/-- On an original singular generator, the power of S has exactly the standard-simplex
iterated list just proved eventually small. Source: Hatcher pp.122–123. -/
theorem iteratedSubdivisionComponent_generator (X : TopCat.{u}) (R : ModuleCat.{max u v} K)
    (n r : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        (End.of (subdivisionComponent X R n)) ^ r =
      signedGeneratorMap R (X.toSSetObjEquiv (op ⦋n⦌) σ)
        (iteratedSubdivisionTuples n r (fun i ↦ StdSimplex.single i)) := by
  simpa only [affineSimplex_identity, ContinuousMap.comp_id, Equiv.symm_apply_apply] using
    iteratedSubdivisionTuples_generator R (X.toSSetObjEquiv (op ⦋n⦌) σ) r
      (fun i ↦ StdSimplex.single i)

/-- A simplex is small when its whole image lies in one of the two original subsets.
Source: Hatcher pp.119–123; no openness of either subset is required. -/
def simplexSmall {X : TopCat.{u}} (A B : Set X) {n : ℕ} (σ : C(Simplex n, X)) : Prop :=
  Set.range σ ⊆ A ∨ Set.range σ ⊆ B

/-- The original continuous restriction to the i-th face.
Source: Hatcher p.121, the affine inclusion omitting vertex i. -/
def simplexFace {X : TopCat.{u}} {n : ℕ} (σ : C(Simplex (n + 1), X))
    (i : Fin (n + 2)) : C(Simplex n, X) :=
  σ.comp (affineSimplex (fun j ↦ StdSimplex.single (i.succAbove j)))

/-- Restricting a small simplex to any face preserves its cover member.
Source: Hatcher p.119; the face image is contained in the simplex image. -/
theorem simplexSmall_face {X : TopCat.{u}} {A B : Set X} {n : ℕ}
    {σ : C(Simplex (n + 1), X)} (hσ : simplexSmall A B σ) (i : Fin (n + 2)) :
    simplexSmall A B (simplexFace σ i) := by
  rcases hσ with hσ | hσ
  · exact Or.inl (fun _ ⟨w, hw⟩ ↦ hw ▸ hσ (Set.mem_range_self _))
  · exact Or.inr (fun _ ⟨w, hw⟩ ↦ hw ▸ hσ (Set.mem_range_self _))

open scoped Classical in
/-- Source-faithful subdivision depths with an explicit face guard.
Source: Hatcher pp.123–124. Small simplices use zero; otherwise take the maximum of an
actual eventual-smallness depth and the depths of every face. This avoids relying on
cancellation of signed chains to establish the face inequality. -/
def guardedSubdivisionDepth (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (n : ℕ) (σ : C(Simplex n, X)) : ℕ :=
  match n, σ with
  | 0, σ => if simplexSmall A B σ then 0
      else Nat.find (singular_simplex_eventually_small A B hcover σ)
  | n + 1, σ => if simplexSmall A B σ then 0
      else max (Nat.find (singular_simplex_eventually_small A B hcover σ))
        (Finset.univ.sup fun i : Fin (n + 2) ↦
          guardedSubdivisionDepth X A B hcover n (simplexFace σ i))

/-- Every small simplex is assigned depth zero, including every supported A- or B-simplex.
Source: Hatcher p.124, the strict retraction normalization. -/
theorem guardedSubdivisionDepth_small {X : TopCat.{u}} (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) {n : ℕ} {σ : C(Simplex n, X)}
    (hσ : simplexSmall A B σ) : guardedSubdivisionDepth X A B hcover n σ = 0 := by
  cases n <;> simp [guardedSubdivisionDepth, hσ]

/-- The chosen depth of every codimension-one face is at most its parent's chosen depth.
Source: Hatcher pp.123–124, made explicit in the recursive maximum. -/
theorem guardedSubdivisionDepth_face_le {X : TopCat.{u}} (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) {n : ℕ}
    (σ : C(Simplex (n + 1), X)) (i : Fin (n + 2)) :
    guardedSubdivisionDepth X A B hcover n (simplexFace σ i) ≤
      guardedSubdivisionDepth X A B hcover (n + 1) σ := by
  classical
  by_cases hσ : simplexSmall A B σ
  · rw [guardedSubdivisionDepth_small A B hcover (simplexSmall_face hσ i)]
    exact Nat.zero_le _
  · rw [guardedSubdivisionDepth, ite_eq_right hσ]
    apply le_trans _ (le_max_right _ _)
    exact Finset.le_sup (f := fun j : Fin (n + 2) ↦
      guardedSubdivisionDepth X A B hcover n (simplexFace σ j)) (Finset.mem_univ i)

/-- At every depth at least the guarded depth, all actual subdivision terms are small.
Source: Hatcher p.123; use eventual smallness in the non-small case, and image containment
in the small case. No coefficient-cancellation argument enters this statement. -/
theorem guardedSubdivisionDepth_small_terms {X : TopCat.{u}} (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) {n : ℕ}
    (σ : C(Simplex n, X)) (r : ℕ) (hr : guardedSubdivisionDepth X A B hcover n σ ≤ r)
    (t : ℤ × (Fin (n + 1) → Simplex n))
    (ht : t ∈ iteratedSubdivisionTuples n r (fun i ↦ StdSimplex.single i)) :
    simplexSmall A B (σ.comp (affineSimplex t.2)) := by
  classical
  by_cases hσ : simplexSmall A B σ
  · rcases hσ with hσ | hσ
    · exact Or.inl (fun _ ⟨w, hw⟩ ↦ hw ▸ hσ (Set.mem_range_self _))
    · exact Or.inr (fun _ ⟨w, hw⟩ ↦ hw ▸ hσ (Set.mem_range_self _))
  · have hdepth : Nat.find (singular_simplex_eventually_small A B hcover σ) ≤
        guardedSubdivisionDepth X A B hcover n σ := by
      cases n with
      | zero => simp [guardedSubdivisionDepth, hσ]
      | succ n => exact (by rw [guardedSubdivisionDepth, ite_eq_right hσ]; exact le_max_left _ _)
    exact Nat.find_spec (singular_simplex_eventually_small A B hcover σ)
      r (hdepth.trans hr) t ht

/-- The degree component of a power of the native subdivision chain map is its component power.
Source: Hatcher p.123; composition of native chain maps is degreewise composition. -/
theorem subdivisionChainMap_pow_f (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (r n : ℕ) :
    ((End.of (subdivisionChainMap X R)) ^ r).f n =
      (End.of (subdivisionComponent X R n)) ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [pow_succ, End.mul_def, HomologicalComplex.comp_f, ih]
    rfl

/-- The literal telescoping homotopy from identity to the r-th subdivision power.
Source: Hatcher p.123, D_r = sum_{j<r} T S^j. Each successor appends the native
homotopy T precomposed with S^r, and all endpoint equalities have zero homotopy. -/
def iteratedSubdivisionHomotopy (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (r : ℕ) :
    Homotopy (𝟙 ((TopCat.toSSet.obj X).chainComplex R))
      ((End.of (subdivisionChainMap X R)) ^ r) :=
  match r with
  | 0 => Homotopy.ofEq (by rfl)
  | r + 1 =>
    (iteratedSubdivisionHomotopy X R r).trans
      (((Homotopy.ofEq (Category.comp_id _).symm).trans
        ((subdivisionHomotopy X R).compLeft ((End.of (subdivisionChainMap X R)) ^ r))).trans
          (Homotopy.ofEq (by rw [pow_succ', End.mul_def])))

/-- The native finite homotopy has exactly Hatcher's finite sum of S^j followed by T.
Source: Hatcher p.123, with the zero-length sum empty. -/
theorem iteratedSubdivisionHomotopy_hom (X : TopCat.{u}) (R : ModuleCat.{max u v} K) (r n : ℕ) :
    (iteratedSubdivisionHomotopy X R r).hom n (n + 1) =
      ∑ j ∈ Finset.range r,
        ((End.of (subdivisionComponent X R n)) ^ j) ≫ homotopyComponent X R n := by
  induction r with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty]
    rfl
  | succ r ih =>
    change (iteratedSubdivisionHomotopy X R r).hom n (n + 1) +
      (0 + (((End.of (subdivisionChainMap X R)) ^ r).f n ≫
        homotopyFamily X R n (n + 1)) + 0) = _
    rw [zero_add, add_zero, ih, subdivisionChainMap_pow_f, Finset.sum_range_succ]
    congr 2
    simp only [homotopyFamily, dite_eq_left rfl, eqToHom_refl, Category.comp_id]

/-- The actual variable-depth native family D, defined on each coefficient summand using
its guarded simplex depth. Source: Hatcher pp.123–124; no global uniform depth is assumed. -/
def guardedHomotopyFamily (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X i ⟶
      ((TopCat.toSSet.obj X).chainComplex R).X j :=
  Sigma.desc fun σ ↦ (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
    (iteratedSubdivisionHomotopy X R
      (guardedSubdivisionDepth X A B hcover i (X.toSSetObjEquiv (op ⦋i⦌) σ))).hom i j

/-- The variable-depth family is the prescribed finite homotopy on every actual generator.
Source: Hatcher p.123 and native chain coproduct universality. -/
theorem guardedHomotopyFamily_generator (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋i⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      guardedHomotopyFamily X A B hcover R i j =
        (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
          (iteratedSubdivisionHomotopy X R
            (guardedSubdivisionDepth X A B hcover i
              (X.toSSetObjEquiv (op ⦋i⦌) σ))).hom i j :=
  Sigma.ι_comp_desc _ σ

/-- D is supported in the chain-homotopy degree shape.
Source: Hatcher p.123; each finite D_r is an actual native homotopy. -/
theorem guardedHomotopyFamily_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) :
    guardedHomotopyFamily X A B hcover R i j = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [guardedHomotopyFamily_generator, (iteratedSubdivisionHomotopy X R _).zero i j hij]

/-- D vanishes on each small native simplex, because its assigned depth is zero.
Source: Hatcher p.124, the normalization giving the strict retraction on small chains. -/
theorem guardedHomotopyFamily_small_generator (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋i⦌))
    (hσ : simplexSmall A B (X.toSSetObjEquiv (op ⦋i⦌) σ)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      guardedHomotopyFamily X A B hcover R i j = 0 := by
  rw [guardedHomotopyFamily_generator, guardedSubdivisionDepth_small A B hcover hσ]
  change _ ≫ 0 = 0
  exact comp_zero

/-- Hatcher's ambient chain map rho = id - boundary D - D boundary.
Source: Hatcher p.123. The native null-homotopic-map construction proves commutation with
boundary from boundary squared zero; its image in small chains is a separate obligation. -/
def guardedSubdivisionChainMap (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    (TopCat.toSSet.obj X).chainComplex R ⟶ (TopCat.toSSet.obj X).chainComplex R :=
  𝟙 _ - Homotopy.nullHomotopicMap (guardedHomotopyFamily X A B hcover R)

/-- The genuine variable-depth D is a native homotopy from identity to the ambient rho.
Source: Hatcher p.123, the defining equation, including the ordinary degree-zero boundary. -/
def guardedSubdivisionHomotopy (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    Homotopy (𝟙 ((TopCat.toSSet.obj X).chainComplex R))
      (guardedSubdivisionChainMap X A B hcover R) where
  hom := guardedHomotopyFamily X A B hcover R
  zero := guardedHomotopyFamily_zero X A B hcover R
  comm i := by
    change 𝟙 _ = _ + _ + (𝟙 _ - (_ + _))
    abel

/-- The variable homotopy annihilates every chain map carried wholly into A or wholly into B.
Source: Hatcher p.124; all its generator images have depth zero. In particular this applies
to the actual subspace inclusions, and is the vanishing needed for relative descent. -/
theorem guardedHomotopyFamily_comp_supported {X Y : TopCat.{u}} (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (f : Y ⟶ X)
    (hf : Set.range f ⊆ A ∨ Set.range f ⊆ B) (i j : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) R).f i ≫
      guardedHomotopyFamily X A B hcover R i j = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, comp_zero]
  apply guardedHomotopyFamily_small_generator
  change simplexSmall A B (f.hom.comp (Y.toSSetObjEquiv (op ⦋i⦌) σ))
  rcases hf with hf | hf
  · exact Or.inl (fun _ ⟨w, hw⟩ ↦ hw ▸ hf (Set.mem_range_self _))
  · exact Or.inr (fun _ ⟨w, hw⟩ ↦ hw ▸ hf (Set.mem_range_self _))

/-- The ambient rho fixes every chain supported through A or B, with its literal inclusion map.
Source: Hatcher p.124. D and its boundary correction vanish after either supported chain map. -/
theorem guardedSubdivisionChainMap_comp_supported {X Y : TopCat.{u}} (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (f : Y ⟶ X)
    (hf : Set.range f ⊆ A ∨ Set.range f ⊆ B) :
    SSet.chainComplexMap (TopCat.toSSet.map f) R ≫
        guardedSubdivisionChainMap X A B hcover R =
      SSet.chainComplexMap (TopCat.toSSet.map f) R := by
  unfold guardedSubdivisionChainMap
  rw [Preadditive.comp_sub, Category.comp_id, Homotopy.comp_nullHomotopicMap]
  have hz : (fun i j ↦ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f i ≫
      guardedHomotopyFamily X A B hcover R i j) = 0 := by
    funext i j
    exact guardedHomotopyFamily_comp_supported A B hcover R f hf i j
  rw [hz]
  have hzero : Homotopy.nullHomotopicMap
      (0 : ∀ i j, ((TopCat.toSSet.obj Y).chainComplex R).X i ⟶
        ((TopCat.toSSet.obj X).chainComplex R).X j) = 0 := by
    ext i
    simp [Homotopy.nullHomotopicMap]
  rw [hzero, sub_zero]

/-- A signed list vanishes after any morphism killing each of its actual simplex summands.
Source: Hatcher pp.123–124; finite additivity, valid for arbitrary coefficient modules. -/
theorem signedGeneratorMap_comp_zero {X : TopCat.{u}} {k n : ℕ} (R Q : ModuleCat.{max u v} K)
    (σ : C(Simplex k, X)) (terms : SignedTuples k n)
    (q : ((TopCat.toSSet.obj X).chainComplex R).X n ⟶ Q)
    (hq : ∀ t ∈ terms, (TopCat.toSSet.obj X).ιChainComplex (R := R)
      ((X.toSSetObjEquiv (op ⦋n⦌)).symm (σ.comp (affineSimplex t.2))) ≫ q = 0) :
    signedGeneratorMap R σ terms ≫ q = 0 := by
  induction terms with
  | nil => simp [signedGeneratorMap]
  | cons t terms ih =>
    simp only [signedGeneratorMap, List.map_cons, List.sum_cons]
    rw [Preadditive.add_comp, Preadditive.zsmul_comp, hq t List.mem_cons_self]
    change t.1 • 0 + signedGeneratorMap R σ terms ≫ q = 0
    rw [ih (fun a ha ↦ hq a (List.mem_cons_of_mem _ ha))]
    simp

/-- The native T preserves smallness, expressed by vanishing after every small-chain quotient.
Source: Hatcher p.123; every term is the original simplex postcomposed with an affine map. -/
theorem homotopyComponent_small_comp_zero (X : TopCat.{u}) (A B : Set X)
    (R Q : ModuleCat.{max u v} K) (n : ℕ)
    (q : ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) ⟶ Q)
    (hq : ∀ τ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌),
      simplexSmall A B (X.toSSetObjEquiv (op ⦋n + 1⦌) τ) →
        (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ q = 0)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : simplexSmall A B (X.toSSetObjEquiv (op ⦋n⦌) σ)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      homotopyComponent X R n ≫ q = 0 := by
  rw [← Category.assoc, homotopyComponent_generator]
  apply signedGeneratorMap_comp_zero
  intro t _
  apply hq
  rw [Equiv.apply_symm_apply]
  rcases hσ with hσ | hσ
  · exact Or.inl (fun _ ⟨w, hw⟩ ↦ hw ▸ hσ (Set.mem_range_self _))
  · exact Or.inr (fun _ ⟨w, hw⟩ ↦ hw ▸ hσ (Set.mem_range_self _))

/-- At or above its guarded depth, an iterated native simplex is killed by every map
killing small simplices. Source: Hatcher p.123; use the checked list identity before cancellation. -/
theorem iteratedSubdivisionComponent_small_comp_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R Q : ModuleCat.{max u v} K) (n r : ℕ)
    (q : ((TopCat.toSSet.obj X).chainComplex R).X n ⟶ Q)
    (hq : ∀ τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌),
      simplexSmall A B (X.toSSetObjEquiv (op ⦋n⦌) τ) →
        (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ q = 0)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hr : guardedSubdivisionDepth X A B hcover n
      (X.toSSetObjEquiv (op ⦋n⦌) σ) ≤ r) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      ((End.of (subdivisionComponent X R n)) ^ r) ≫ q = 0 := by
  rw [← Category.assoc, iteratedSubdivisionComponent_generator]
  apply signedGeneratorMap_comp_zero
  intro t ht
  apply hq
  rw [Equiv.apply_symm_apply]
  exact guardedSubdivisionDepth_small_terms A B hcover _ r hr t ht

/-- After smallness is reached, every additional TS^j term is small.
Source: Hatcher p.124; this is the individual summand in the face-depth correction tail. -/
theorem subdivision_homotopy_tail_term_comp_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R Q : ModuleCat.{max u v} K) (n r : ℕ)
    (q : ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) ⟶ Q)
    (hq : ∀ τ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌),
      simplexSmall A B (X.toSSetObjEquiv (op ⦋n + 1⦌) τ) →
        (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ q = 0)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hr : guardedSubdivisionDepth X A B hcover n
      (X.toSSetObjEquiv (op ⦋n⦌) σ) ≤ r) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      ((End.of (subdivisionComponent X R n)) ^ r) ≫ homotopyComponent X R n ≫ q = 0 :=
  iteratedSubdivisionComponent_small_comp_zero X A B hcover R Q n r
    (homotopyComponent X R n ≫ q)
    (fun τ hτ ↦ homotopyComponent_small_comp_zero X A B R Q n q hq τ hτ) σ hr

/-- The exact difference of finite native homotopies is their finite tail.
Source: Hatcher p.124, D_r-D_m = sum_{m≤j<r} TS^j for m≤r. -/
theorem iteratedSubdivisionHomotopy_tail (X : TopCat.{u}) (R : ModuleCat.{max u v} K)
    (n m r : ℕ) (hmr : m ≤ r) :
    (iteratedSubdivisionHomotopy X R r).hom n (n + 1) -
        (iteratedSubdivisionHomotopy X R m).hom n (n + 1) =
      ∑ j ∈ Finset.Ico m r,
        ((End.of (subdivisionComponent X R n)) ^ j) ≫ homotopyComponent X R n := by
  rw [iteratedSubdivisionHomotopy_hom, iteratedSubdivisionHomotopy_hom,
    Finset.sum_Ico_eq_sub _ hmr]

/-- Above the guarded depth, finite homotopies agree modulo small chains on each generator.
Source: Hatcher p.124; every term of the exact difference is small. -/
theorem iteratedSubdivisionHomotopy_tail_comp_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R Q : ModuleCat.{max u v} K) (n r : ℕ)
    (q : ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) ⟶ Q)
    (hq : ∀ τ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌),
      simplexSmall A B (X.toSSetObjEquiv (op ⦋n + 1⦌) τ) →
        (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ q = 0)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hr : guardedSubdivisionDepth X A B hcover n
      (X.toSSetObjEquiv (op ⦋n⦌) σ) ≤ r) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        (iteratedSubdivisionHomotopy X R r).hom n (n + 1) ≫ q =
      (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        guardedHomotopyFamily X A B hcover R n (n + 1) ≫ q := by
  rw [← Category.assoc _ (guardedHomotopyFamily X A B hcover R n (n + 1)),
    guardedHomotopyFamily_generator, Category.assoc]
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← Preadditive.sub_comp, iteratedSubdivisionHomotopy_tail _ _ _ _ _ hr]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  apply Finset.sum_eq_zero
  intro j hj
  exact subdivision_homotopy_tail_term_comp_zero X A B hcover R Q n j q hq σ
    (Finset.mem_Ico.mp hj).1

/-- The native singular face equivalence is the same continuous face used by guarded depths.
Source: Hatcher p.108; the actual affine omitted-vertex inclusion. -/
theorem native_simplexFace (X : TopCat.{u}) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) (i : Fin (n + 2)) :
    X.toSSetObjEquiv (op ⦋n⦌) ((TopCat.toSSet.obj X).δ i σ) =
      simplexFace (X.toSSetObjEquiv (op ⦋n + 1⦌) σ) i := by
  have h := congrArg (X.toSSetObjEquiv (op ⦋n⦌))
    (affine_generator_face (X.toSSetObjEquiv (op ⦋n + 1⦌) σ)
      (fun i ↦ StdSimplex.single i) i)
  simpa only [affineSimplex_identity, ContinuousMap.comp_id, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, simplexFace, Function.comp_def] using h

/-- The face part of D at the parent's fixed depth equals the variable face part modulo
small chains. Source: Hatcher p.124, the guarded face inequalities and exact finite tails. -/
theorem guardedHomotopyFamily_boundary_comp_eq (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R Q : ModuleCat.{max u v} K) (n : ℕ)
    (q : ((TopCat.toSSet.obj X).chainComplex R).X (n + 1) ⟶ Q)
    (hq : ∀ τ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌),
      simplexSmall A B (X.toSSetObjEquiv (op ⦋n + 1⦌) τ) →
        (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ q = 0)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫
        (iteratedSubdivisionHomotopy X R
          (guardedSubdivisionDepth X A B hcover (n + 1)
            (X.toSSetObjEquiv (op ⦋n + 1⦌) σ))).hom n (n + 1) ≫ q =
      (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫
        guardedHomotopyFamily X A B hcover R n (n + 1) ≫ q := by
  simp only [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Category.assoc, Category.assoc]
  apply iteratedSubdivisionHomotopy_tail_comp_zero X A B hcover R Q n _ q hq
  rw [native_simplexFace]
  exact guardedSubdivisionDepth_face_le A B hcover _ i

/-- The ambient rho sends each generator to small chains, characterized universally by
annihilation under every morphism killing the actual small generators.
Source: Hatcher pp.123–124. Compare the fixed-depth and variable-depth homotopy identities;
the top D terms agree, and the face terms differ by the checked small finite tails. -/
theorem guardedSubdivisionChainMap_small_comp_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R Q : ModuleCat.{max u v} K) (n : ℕ)
    (q : ((TopCat.toSSet.obj X).chainComplex R).X n ⟶ Q)
    (hq : ∀ τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌),
      simplexSmall A B (X.toSSetObjEquiv (op ⦋n⦌) τ) →
        (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫ q = 0) :
    (guardedSubdivisionChainMap X A B hcover R).f n ≫ q = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  let m := guardedSubdivisionDepth X A B hcover n (X.toSSetObjEquiv (op ⦋n⦌) σ)
  have hs := iteratedSubdivisionComponent_small_comp_zero X A B hcover R Q n m q hq σ
    (le_refl m)
  have hv := congrArg (fun f ↦ (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫ f ≫ q)
    ((guardedSubdivisionHomotopy X A B hcover R).comm n)
  have hf := congrArg (fun f ↦ (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫ f ≫ q)
    ((iteratedSubdivisionHomotopy X R m).comm n)
  have htop : (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      (guardedSubdivisionHomotopy X A B hcover R).hom n (n + 1) ≫
        ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ q =
      (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
        (iteratedSubdivisionHomotopy X R m).hom n (n + 1) ≫
          ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ q := by
    change _ ≫ guardedHomotopyFamily X A B hcover R n (n + 1) ≫ _ = _
    rw [← Category.assoc _ (guardedHomotopyFamily X A B hcover R n (n + 1)),
      guardedHomotopyFamily_generator, Category.assoc]
  simp only [HomologicalComplex.id_f, Preadditive.add_comp, Preadditive.comp_add,
    Category.id_comp, subdivisionChainMap_pow_f] at hv hf
  cases n with
  | zero =>
    rw [Homotopy.dNext_zero_chainComplex] at hv hf
    rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 from rfl)] at hv hf
    simp only [comp_zero, zero_comp, zero_add, Category.assoc] at hv hf
    rw [htop] at hv
    rw [hs, add_zero] at hf
    rw [← hf] at hv
    simpa only [comp_zero] using
      (add_left_cancel (hv.symm.trans (add_zero _).symm))
  | succ n =>
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)] at hv hf
    rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)] at hv hf
    simp only [Category.assoc] at hv hf
    have hface := guardedHomotopyFamily_boundary_comp_eq X A B hcover R Q n q hq σ
    change _ = _ ≫ _ + _ + _ at hv
    rw [htop] at hv
    change _ = _ ≫ ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫
      guardedHomotopyFamily X A B hcover R n (n + 1) ≫ q + _ + _ at hv
    rw [← hface] at hv
    rw [hs, add_zero] at hf
    rw [← hf] at hv
    simpa only [comp_zero] using
      (add_left_cancel (hv.symm.trans (add_zero _).symm))


end HolomorphicAnosov.NativeBarycentricOperators


namespace HolomorphicAnosov.NativeBarycentricOperators
open HolomorphicAnosov
/-- A singular simplex whose image lies in A belongs to the actual singular subspace image.
Source: Hatcher p.110; the lift equips each value with its given subspace membership. -/
theorem supported_simplex_mem_subspace {X : TopCat.{u}} (A : Set X) {n : ℕ}
    (τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hτ : Set.range (X.toSSetObjEquiv (op ⦋n⦌) τ) ⊆ A) :
    τ ∈ (singularSubspace X A).obj (op ⦋n⦌) := by
  let g : C(Simplex n, TopCat.of A) :=
    ⟨fun x ↦ ⟨(X.toSSetObjEquiv (op ⦋n⦌) τ) x, hτ ⟨x, rfl⟩⟩,
      (X.toSSetObjEquiv (op ⦋n⦌) τ).continuous.subtype_mk _⟩
  refine ⟨(TopCat.toSSetObjEquiv (TopCat.of A) (op ⦋n⦌)).symm g, ?_⟩
  apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Projection to the actual quotient by the small-chain join kills every small simplex.
Source: Hatcher p.124; apply the native cokernel equation to its supported generator. -/
theorem small_join_projection_generator_zero {X : TopCat.{u}} (A B : Set X)
    (R : ModuleCat.{max u v} K) {n : ℕ} {τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)}
    (hτ : simplexSmall A B (X.toSSetObjEquiv (op ⦋n⦌) τ)) :
    (TopCat.toSSet.obj X).ιChainComplex (R := R) τ ≫
      ((singularSubspace X A ⊔ singularSubspace X B).pair.chainComplexπ R).f n = 0 := by
  let U := singularSubspace X A ⊔ singularSubspace X B
  have hmem : τ ∈ U.obj (op ⦋n⦌) := by
    rcases hτ with hA | hB
    · exact Or.inl (supported_simplex_mem_subspace A τ hA)
    · exact Or.inr (supported_simplex_mem_subspace B τ hB)
  have h := congrArg (fun f ↦ U.toSSet.ιChainComplex (R := R) ⟨τ, hmem⟩ ≫ f)
    (U.pair.chainComplex_condition_f R n)
  change U.toSSet.ιChainComplex (R := R) ⟨τ, hmem⟩ ≫
    (SSet.chainComplexMap U.ι R).f n ≫ (U.pair.chainComplexπ R).f n = _ at h
  rw [SSet.ι_chainComplexMap_f_assoc, comp_zero] at h
  exact h

/-- The ambient variable-depth chain map vanishes under the actual join-relative projection.
Source: Hatcher p.124; instantiate the universal small-image result with this native cokernel. -/
theorem guardedSubdivisionChainMap_join_projection_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    guardedSubdivisionChainMap X A B hcover R ≫
      ((singularSubspace X A ⊔ singularSubspace X B).pair.chainComplexπ R) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact guardedSubdivisionChainMap_small_comp_zero X A B hcover R _ n _
    (fun τ hτ ↦ small_join_projection_generator_zero A B R hτ)

/-- The actual small-chain factorization of the ambient rho through the native join inclusion.
Source: Hatcher p.124. The inclusion is the kernel of the native relative projection,
and the checked annihilation identity supplies its kernel lift. -/
def smallChainRetraction (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    (TopCat.toSSet.obj X).chainComplex R ⟶
      (singularSubspace X A ⊔ singularSubspace X B).toSSet.chainComplex R :=
  ((singularSubspace X A ⊔ singularSubspace X B).pair.shortExact_chainComplexShortComplex R).exact.lift
    (guardedSubdivisionChainMap X A B hcover R)
    (guardedSubdivisionChainMap_join_projection_zero X A B hcover R)

/-- Composing the small-chain retraction with the literal join inclusion gives rho.
Source: Hatcher p.124; the defining equation of the kernel factorization. -/
theorem smallChainRetraction_inclusion (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    smallChainRetraction X A B hcover R ≫
        SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R =
      guardedSubdivisionChainMap X A B hcover R :=
  ShortComplex.Exact.lift_f _ _ _

/-- Membership in the actual subspace image implies image containment.
Source: Hatcher p.110; forget the subtype witness of the witnessing subspace simplex. -/
theorem subspace_simplex_supported {X : TopCat.{u}} (A : Set X) {n : ℕ}
    (τ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hτ : τ ∈ (singularSubspace X A).obj (op ⦋n⦌)) :
    Set.range (X.toSSetObjEquiv (op ⦋n⦌) τ) ⊆ A := by
  obtain ⟨γ, rfl⟩ := hτ
  rintro _ ⟨x, rfl⟩
  exact ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌) γ x).property

/-- The variable homotopy vanishes on the native small-chain join in every bidegree.
Source: Hatcher p.124; the summands of the join are precisely small simplices. -/
theorem guardedHomotopyFamily_join_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ) :
    (SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R).f i ≫
      guardedHomotopyFamily X A B hcover R i j = 0 := by
  apply SSet.chainComplex_hom_ext
  intro τ
  rw [SSet.ι_chainComplexMap_f_assoc, comp_zero]
  apply guardedHomotopyFamily_small_generator
  rcases τ.property with hA | hB
  · exact Or.inl (subspace_simplex_supported A τ.val hA)
  · exact Or.inr (subspace_simplex_supported B τ.val hB)

/-- Rho is the identity on the literal small-chain inclusion.
Source: Hatcher p.124; the variable homotopy is zero on the whole join. -/
theorem guardedSubdivisionChainMap_join_fixed (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R ≫
      guardedSubdivisionChainMap X A B hcover R =
        SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R := by
  unfold guardedSubdivisionChainMap
  rw [Preadditive.comp_sub, Category.comp_id, Homotopy.comp_nullHomotopicMap]
  have hz : (fun i j ↦
      (SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R).f i ≫
        guardedHomotopyFamily X A B hcover R i j) = 0 := by
    funext i j
    exact guardedHomotopyFamily_join_zero X A B hcover R i j
  rw [hz]
  have hzero : Homotopy.nullHomotopicMap
      (0 : ∀ i j, ((singularSubspace X A ⊔ singularSubspace X B).toSSet.chainComplex R).X i ⟶
        ((TopCat.toSSet.obj X).chainComplex R).X j) = 0 := by
    ext i
    simp [Homotopy.nullHomotopicMap]
  rw [hzero, sub_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The small-chain factorization is a strict left inverse to the literal join inclusion.
Source: Hatcher p.124; cancel the monic inclusion after the checked rho identity. -/
theorem inclusion_smallChainRetraction (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R ≫
      smallChainRetraction X A B hcover R = 𝟙 _ := by
  let : Mono (SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R) :=
    ((singularSubspace X A ⊔ singularSubspace X B).pair.shortExact_chainComplexShortComplex R).mono_f
  apply (cancel_mono (SSet.chainComplexMap
    (singularSubspace X A ⊔ singularSubspace X B).ι R)).mp
  rw [Category.assoc, smallChainRetraction_inclusion, Category.id_comp,
    guardedSubdivisionChainMap_join_fixed]

/-- A-chain inclusion into the small-chain join, with the actual supported simplex model.
Source: Hatcher p.124, C(A) inside C(A)+C(B). -/
abbrev smallRelativePair (X : TopCat.{u}) (A B : Set X) : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE
    (show singularSubspace X A ≤ singularSubspace X A ⊔ singularSubspace X B from le_sup_left))

set_option backward.isDefEq.respectTransparency false in
/-- The absolute retraction restricts to the identity inclusion on A-supported chains.
Source: Hatcher p.124; factor the A inclusion through the join, then use the strict retraction. -/
theorem smallChainRetraction_on_A (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    SSet.chainComplexMap (singularSubspace X A).ι R ≫
        smallChainRetraction X A B hcover R =
      SSet.chainComplexMap (smallRelativePair X A B).hom R := by
  have hi : SSet.chainComplexMap (smallRelativePair X A B).hom R ≫
      SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R =
        SSet.chainComplexMap (singularSubspace X A).ι R := by
    exact ((SSet.chainComplexFunctor (ModuleCat.{max u v} K)).obj R).map_comp
      (smallRelativePair X A B).hom (singularSubspace X A ⊔ singularSubspace X B).ι |>.symm
  rw [← hi, Category.assoc, inclusion_smallChainRetraction]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- The native retraction followed by the small relative projection annihilates A-chains.
Source: Hatcher p.124; its A restriction is the original A inclusion. -/
theorem smallChainRetraction_relative_condition (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    SSet.chainComplexMap (singularSubspace X A).ι R ≫
      (smallChainRetraction X A B hcover R ≫ (smallRelativePair X A B).chainComplexπ R) = 0 := by
  rw [← Category.assoc, smallChainRetraction_on_A]
  exact (smallRelativePair X A B).chainComplex_condition R

/-- The actual retraction descended through the A-chain cokernel.
Source: Hatcher p.124; use the native cokernel universal property on chain complexes. -/
def smallRelativeRetraction (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    (singularSubspace X A).pair.chainComplex R ⟶ (smallRelativePair X A B).chainComplex R :=
  ((singularSubspace X A).pair.isColimitCokernelCoforkChainComplex R).desc
    (CokernelCofork.ofπ
      (smallChainRetraction X A B hcover R ≫ (smallRelativePair X A B).chainComplexπ R)
      (smallChainRetraction_relative_condition X A B hcover R))

/-- The descended retraction preserves the literal relative projections.
Source: Hatcher p.124; the defining equation of native cokernel descent. -/
theorem smallRelativeRetraction_projection (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    (singularSubspace X A).pair.chainComplexπ R ≫ smallRelativeRetraction X A B hcover R =
      smallChainRetraction X A B hcover R ≫ (smallRelativePair X A B).chainComplexπ R :=
  Cofork.IsColimit.π_desc
    ((singularSubspace X A).pair.isColimitCokernelCoforkChainComplex R)

/-- D annihilates the native A-supported chain inclusion in each bidegree.
Source: Hatcher p.124; every A-supported simplex has guarded depth zero. -/
theorem guardedHomotopyFamily_A_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ) :
    (SSet.chainComplexMap (singularSubspace X A).ι R).f i ≫
      guardedHomotopyFamily X A B hcover R i j = 0 := by
  apply SSet.chainComplex_hom_ext
  intro τ
  rw [SSet.ι_chainComplexMap_f_assoc, comp_zero]
  exact guardedHomotopyFamily_small_generator X A B hcover R i j τ.val
    (Or.inl (subspace_simplex_supported A τ.val τ.property))

set_option backward.isDefEq.respectTransparency false in
/-- The A-chain vanishing equation required for the degreewise relative homotopy descent.
Source: Hatcher p.124; postcompose the actual zero family with the relative projection. -/
theorem guardedRelativeHomotopy_condition (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ) :
    (SSet.chainComplexMap (singularSubspace X A).ι R).f i ≫
      (guardedHomotopyFamily X A B hcover R i j ≫
        ((singularSubspace X A).pair.chainComplexπ R).f j) = 0 := by
  rw [← Category.assoc, guardedHomotopyFamily_A_zero, zero_comp]

/-- The actual variable-depth D descended through A in source and target degrees.
Source: Hatcher p.124; use the native degreewise relative cokernel, retaining its projection. -/
def guardedRelativeHomotopyFamily (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ) :
    ((singularSubspace X A).pair.chainComplex R).X i ⟶
      ((singularSubspace X A).pair.chainComplex R).X j :=
  ((singularSubspace X A).pair.isColimitCokernelCoforkChainComplexX R i).desc
    (CokernelCofork.ofπ (guardedHomotopyFamily X A B hcover R i j ≫
      ((singularSubspace X A).pair.chainComplexπ R).f j)
      (guardedRelativeHomotopy_condition X A B hcover R i j))

/-- The descended homotopy has its original defining equation after the native projection.
Source: Hatcher p.124; the degreewise cokernel universal property. -/
theorem guardedRelativeHomotopyFamily_projection (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ) :
    ((singularSubspace X A).pair.chainComplexπ R).f i ≫
      guardedRelativeHomotopyFamily X A B hcover R i j =
        guardedHomotopyFamily X A B hcover R i j ≫
          ((singularSubspace X A).pair.chainComplexπ R).f j :=
  Cofork.IsColimit.π_desc
    ((singularSubspace X A).pair.isColimitCokernelCoforkChainComplexX R i)

/-- The literal pair map from small chains modulo A to ambient chains modulo A.
Source: Hatcher p.124, the relative small inclusion. -/
def smallRelativeInclusion (X : TopCat.{u}) (A B : Set X) :
    smallRelativePair X A B ⟶ (singularSubspace X A).pair :=
  SSetPair.homMk (𝟙 _) (singularSubspace X A ⊔ singularSubspace X B).ι (by
    ext n σ
    rfl)

/-- The native relative inclusion commutes with its original projections.
Source: Hatcher p.124 and naturality of Mathlib's relative projection. -/
theorem smallRelativeInclusion_projection (X : TopCat.{u}) (A B : Set X) (R : ModuleCat.{max u v} K) :
    (smallRelativePair X A B).chainComplexπ R ≫
        SSetPair.chainComplexMap (smallRelativeInclusion X A B) R =
      SSet.chainComplexMap (singularSubspace X A ⊔ singularSubspace X B).ι R ≫
        (singularSubspace X A).pair.chainComplexπ R := by
  exact ((((SSetPair.chainComplexFunctorπ (ModuleCat.{max u v} K)).app R).naturality
    (smallRelativeInclusion X A B))).symm

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion followed by the descended retraction is strictly the identity.
Source: Hatcher p.124; cancel the actual small relative projection. -/
theorem smallRelativeInclusion_retraction (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    SSetPair.chainComplexMap (smallRelativeInclusion X A B) R ≫
      smallRelativeRetraction X A B hcover R = 𝟙 _ := by
  apply (cancel_epi ((smallRelativePair X A B).chainComplexπ R)).mp
  rw [← Category.assoc, smallRelativeInclusion_projection, Category.assoc,
    smallRelativeRetraction_projection, ← Category.assoc, inclusion_smallChainRetraction]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The other relative composite is rho after passage to the actual A-quotient.
Source: Hatcher p.124; combine the two projection equations and the absolute factorization. -/
theorem smallRelativeRetraction_inclusion_projection (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    (singularSubspace X A).pair.chainComplexπ R ≫
        (smallRelativeRetraction X A B hcover R ≫
          SSetPair.chainComplexMap (smallRelativeInclusion X A B) R) =
      guardedSubdivisionChainMap X A B hcover R ≫
        (singularSubspace X A).pair.chainComplexπ R := by
  rw [← Category.assoc, smallRelativeRetraction_projection, Category.assoc,
    smallRelativeInclusion_projection, ← Category.assoc, smallChainRetraction_inclusion]

set_option backward.isDefEq.respectTransparency false in
/-- The descended D vanishes outside the chain-homotopy shape.
Source: Hatcher p.124; cancel the epimorphic degreewise relative projection. -/
theorem guardedRelativeHomotopyFamily_zero (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) (i j : ℕ)
    (hij : ¬ (ComplexShape.down ℕ).Rel j i) :
    guardedRelativeHomotopyFamily X A B hcover R i j = 0 := by
  apply (cancel_epi (((singularSubspace X A).pair.chainComplexπ R).f i)).mp
  rw [guardedRelativeHomotopyFamily_projection, guardedHomotopyFamily_zero _ _ _ _ _ _ _ hij,
    zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The descended homotopy satisfies the exact relative homotopy equation.
Source: Hatcher p.124. Precompose by the epimorphic native A-quotient projection;
its chain identity and the defining equations of the descended D reduce to the checked
ambient homotopy equation, without any choice of representatives. -/
def smallRelativeHomotopy (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    Homotopy (𝟙 ((singularSubspace X A).pair.chainComplex R))
      (smallRelativeRetraction X A B hcover R ≫
        SSetPair.chainComplexMap (smallRelativeInclusion X A B) R) where
  hom := guardedRelativeHomotopyFamily X A B hcover R
  zero := guardedRelativeHomotopyFamily_zero X A B hcover R
  comm i := by
    let π := (singularSubspace X A).pair.chainComplexπ R
    have hfamilies : (fun i j ↦ π.f i ≫ guardedRelativeHomotopyFamily X A B hcover R i j) =
        (fun i j ↦ guardedHomotopyFamily X A B hcover R i j ≫ π.f j) := by
      funext i j
      exact guardedRelativeHomotopyFamily_projection X A B hcover R i j
    apply (cancel_epi (π.f i)).mp
    have h := congrArg (fun f ↦ f ≫ π.f i)
      ((guardedSubdivisionHomotopy X A B hcover R).comm i)
    have hcomp := congrArg (fun f ↦ f.f i)
      (smallRelativeRetraction_inclusion_projection X A B hcover R)
    simp only [HomologicalComplex.comp_f] at hcomp
    rw [Preadditive.comp_add, Preadditive.comp_add,
      ← dNext_comp_left, ← prevD_comp_left, hfamilies, dNext_comp_right, prevD_comp_right]
    simp only [HomologicalComplex.comp_f]
    rw [hcomp]
    simp only [Preadditive.add_comp, HomologicalComplex.id_f, Category.comp_id,
      Category.id_comp] at h ⊢
    exact h

/-- Native relative small-chain equivalence with forward map the literal inclusion.
Source: Hatcher Proposition 2.21 and excision, pp.123–124; the strict inverse identity and
relative D homotopy are the actual native chain-complex constructions above. -/
def smallRelativeHomotopyEquiv (X : TopCat.{u}) (A B : Set X)
    (hcover : interior A ∪ interior B = Set.univ) (R : ModuleCat.{max u v} K) :
    HomotopyEquiv ((smallRelativePair X A B).chainComplex R)
      ((singularSubspace X A).pair.chainComplex R) where
  hom := SSetPair.chainComplexMap (smallRelativeInclusion X A B) R
  inv := smallRelativeRetraction X A B hcover R
  homotopyHomInvId := Homotopy.ofEq (smallRelativeInclusion_retraction X A B hcover R)
  homotopyInvHomId := (smallRelativeHomotopy X A B hcover R).symm

end HolomorphicAnosov.NativeBarycentricOperators





end
end NativeConstruction


/-!
# Ordinary singular excision with arbitrary abelian coefficients

Source: Hatcher, *Algebraic Topology*, Theorem 2.20, p. 119, Proposition 2.21
and its proof, pp. 119–124, the proof of excision, p. 124, and Homology with
Coefficients, p. 153 (`literature/hatcher-at.pdf`).

All simplicial pairs here are the actual singular pairs of the original
subspaces, with induced topologies. The small-chain objects use the join of
the actual supported singular subcomplexes, rather than all singular simplices
in their set-theoretic union. The coefficient object is arbitrary in
`ModuleCat ℤ`; these are precisely abelian groups, with their canonical integer
action. A common universe is used for spaces and coefficients, with `ULift`
available for a smaller coefficient group. No freeness, flatness, finite
generation, separation or openness premise is imposed.

The conclusion fixes every forward map to its literal inclusion-induced native
chain or homology map. The homotopy equivalence and the quotient isomorphism are
conclusions, never supplied assumptions. Homology naturality is stated for
continuous maps preserving both subspaces and for coefficient homomorphisms;
the noncanonical subdivision-depth choices need not be natural themselves.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

noncomputable section

/-- Ordinary singular excision for arbitrary abelian coefficients, through actual
subdivision/small-chain and relative-quotient equivalences, with naturality.

Source: Hatcher, *Algebraic Topology*, Theorem 2.20 p. 119, Proposition 2.21
pp. 119–124 and the excision proof p. 124; arbitrary coefficient groups p. 153.

Complete natural-language proof:

In each degree the native singular chain module is a coproduct of copies of the
arbitrary coefficient group `R`, one for every continuous simplex. Identify it
with finitely supported coefficient functions on those same simplices. The
generator boundary is the alternating sum of faces, with degree-zero outgoing
boundary zero. The singular-subspace adapter identifies subspace chains with
the summands on ambient simplices supported in that subset, and identifies
the native pair complex with the quotient by those summands, preserving the
actual projections and inclusion maps. For arbitrary `R` the same adapter
argument uses its coproduct summands in place of integer generators; no tensor
exactness is needed. Put `K=C(A)+C(B)`. Its simplices are those wholly in A or
wholly in B, so its native simplicial model is the join of the two supported
subcomplexes. Faces preserve their cover member, making K a subcomplex.

For subdivision first work with linear simplices in a convex real vector
space. Temporarily augment in degree minus one with the empty generator,
and define the cone `c_b[v₀,…,vₙ]=[b,v₀,…,vₙ]`. Expansion of the alternating
boundary gives `∂c_b+c_b∂=id`. For a simplex λ with barycenter b, put
`S[∅]=[∅]` and `Sλ=c_b(S∂λ)`. Induction and `∂²=0` give `∂S=S∂`.
Put `T[∅]=0` and `Tλ=c_b(λ−T∂λ)`. The cone identity and the lower-degree
homotopy identity give `∂Tλ=λ−T∂λ−Sλ`, hence `∂T+T∂=id−S`.
For a vertex `S[v]=[v]` and `T[v]=[v,v]`, whose boundary is zero; no normalized
chain quotient discards this allowed degenerate singular simplex. Discard the
auxiliary negative degree to obtain the ordinary nonnegative identities.
Apply the same finite signed formulas coefficientwise to any element of R.

For a continuous singular simplex σ define Sσ and Tσ by postcomposing the
corresponding chains in its standard simplex with σ. Affine maps preserve
barycenters, vertex tuples, and cones, so this construction commutes with the
face maps and proves the chain and homotopy identities on singular generators.
Every resulting simplex has image in the original simplex image: recursively
coned vertices remain in the convex standard simplex. Thus S and T preserve
A-supported chains, B-supported chains, and K. The construction commutes with
postcomposition of continuous maps and with coefficient homomorphisms.

Pull back the open cover by the interiors of A and B to the compact metric
standard simplex of σ. A Lebesgue number ε>0 exists for this cover. In positive
dimension n, each depth-m barycentric cell has diameter bounded by
`(n/(n+1))^m` times the original diameter, which tends to zero. Hence every
term of a sufficiently subdivided σ lies wholly in one cover member. Further
subdivision preserves this condition. Degree-zero simplices are already small.
Finite sets of simplices admit a maximum depth; no uniform depth over all
singular simplices is asserted.

Choose depths d(σ) inductively on dimension, zero for already small simplices,
and otherwise at least an eventual-smallness depth and all depths of the
finitely many codimension-one faces. This explicit face-depth guard avoids
inferring support from cancellations. Set `D_m=Σ_{j<m}TS^j`. Telescoping gives
`∂D_m+D_m∂=id−S^m`. Define `Dσ=D_{d(σ)}σ` and extend additively with the same
coefficients, and set `ρ=id−∂D−D∂`. Then `∂ρ=ρ∂` by `∂²=0`.
On a generator,
`ρσ=S^{d(σ)}σ+D_{d(σ)}∂σ−D∂σ`. The first term is small. For a face τ the
remaining difference is the sum of `TS^jτ` with `d(τ)≤j<d(σ)`. These terms
are small because the depth-d(τ) subdivision is small and later S and T preserve
its cover member. Thus ρ lands in K. If `i:K→C(X)` is inclusion, then `iρ=id_K`
in categorical composition order and `ρi` is homotopic to `id_C(X)` through
`∂D+D∂`. This agrees with the usual function-order identities `ρ∘i=id` and
`id−i∘ρ=∂D+D∂`. All A- and B-supported simplices have depth zero, so D is zero
on both supported chain subcomplexes.

Consequently ρ, i and D descend through the actual quotient by A-chains.
The relative small inclusion has a strict retraction and a homotopy of the
other composite to the identity, giving the second homotopy equivalence below
with forward map exactly its canonical pair chain map. At degree zero the
homotopy equation is `id−ir=∂₁D₀`, with no negative-degree boundary. The native
cokernel projections determine the descended maps uniquely and preserve their
original quotient interpretation.

Independently of the interiors cover, inclusion gives a chain isomorphism
`C(B)/C(A∩B) → K/C(A)`. Degreewise both sides are direct sums of copies of R
indexed by B-supported simplices not wholly in A. The inverse discards the
A-supported summands and keeps each remaining B-supported coefficient with
its unchanged simplex. This is well defined on the quotient for arbitrary R,
and the composites fix every summand. The forward map commutes with boundaries
by inclusion; cancel the degreewise isomorphisms to show that its inverse does
as well. This gives the first native quotient isomorphism below with its exact
inclusion forward map; it does not assume that R is free.

Compose this quotient isomorphism with the relative small-chain equivalence.
The adapter identifies the source supported intersection pair with the singular
pair of the actual nested subspace `{b:B | b.val∈A}` and preserves the pair
inclusion. Thus the composite is precisely the chain map of `(B,A∩B)→(X,A)`.
It is a chain homotopy equivalence with this fixed forward map. Applying native
homology produces an isomorphism in every natural degree, including zero.

For a continuous map f carrying A into A' and B into B', both composites in
the naturality square send a relative coefficient simplex rσ to r(f∘σ), modulo
the target subspace. They agree on chains and therefore on homology. Applying
a coefficient homomorphism to each summand likewise commutes with these exact
inclusion maps. Inverting the commuting square proves naturality of the inverse
homology isomorphisms without asserting naturality of the chosen depths.

For the closure/interior form take `B=X\Z`. The identity
`interior(X\Z)=X\closure Z` and `closure Z⊆interior A` give the interiors cover,
and the nested intersection is literally the subspace of `A\Z`. Conversely an
interiors cover gives `Z=X\B⊆A` and `closure Z=X\interior B⊆interior A`.
These are the same canonical inclusions. If X is empty all chains vanish; if
A is empty the cover forces B=X and inclusion is identity; if B is empty the
cover forces A=X and both relative complexes vanish. No reduced augmentation,
nonempty subspace, connectedness, or separation hypothesis is used.
-/
theorem singular_homology_excision_barycentric_subdivision :
    (∀ (X : TopCat.{u}) (A B : Set X) (R : ModuleCat.{u} ℤ),
      ∃ q : (singularIntersectionPair X A B).chainComplex R ≅
          (singularExcisionSmallPair X A B).chainComplex R,
        q.hom = SSetPair.chainComplexMap (singularExcisionQuotientInclusion X A B) R) ∧
    (∀ (X : TopCat.{u}) (A B : Set X), interior A ∪ interior B = Set.univ →
      ∀ R : ModuleCat.{u} ℤ,
        (∃ e : HomotopyEquiv ((singularExcisionSmallPair X A B).chainComplex R)
            ((singularSubspace X A).pair.chainComplex R),
          e.hom = SSetPair.chainComplexMap (singularExcisionSmallInclusion X A B) R) ∧
        (∃ e : HomotopyEquiv ((singularExcisionSource X A B).chainComplex R)
            ((singularSubspacePair X A).chainComplex R),
          e.hom = SSetPair.chainComplexMap (singularExcisionInclusion X A B) R) ∧
        ∀ n : ℕ, IsIso (SSetPair.homologyMap (singularExcisionInclusion X A B) R n)) ∧
    (∀ (X Y : TopCat.{u}) (f : X ⟶ Y) (A B : Set X) (A' B' : Set Y)
      (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') (R : ModuleCat.{u} ℤ) (n : ℕ),
      SSetPair.homologyMap (singularExcisionInclusion X A B) R n ≫
          SSetPair.homologyMap (singularSubspacePairMap f A A' hA) R n =
        SSetPair.homologyMap (singularExcisionSourceMap f A B A' B' hA hB) R n ≫
          SSetPair.homologyMap (singularExcisionInclusion Y A' B') R n) ∧
    (∀ (X : TopCat.{u}) (A B : Set X) (R Q : ModuleCat.{u} ℤ) (φ : R ⟶ Q) (n : ℕ),
      SSetPair.homologyMap (singularExcisionInclusion X A B) R n ≫
          singularRelativeCoefficientMap (singularSubspacePair X A) φ n =
        singularRelativeCoefficientMap (singularExcisionSource X A B) φ n ≫
          SSetPair.homologyMap (singularExcisionInclusion X A B) Q n) ∧
    (∀ (X : TopCat.{u}) (A Z : Set X), Z ⊆ A → closure Z ⊆ interior A →
      ∀ R : ModuleCat.{u} ℤ,
        (∃ e : HomotopyEquiv ((singularExcisionSource X A Zᶜ).chainComplex R)
            ((singularSubspacePair X A).chainComplex R),
          e.hom = SSetPair.chainComplexMap (singularExcisionInclusion X A Zᶜ) R) ∧
        ∀ n : ℕ, IsIso (SSetPair.homologyMap (singularExcisionInclusion X A Zᶜ) R n)) := by
  have hsmall : ∀ (X : TopCat.{u}) (A B : Set X),
      interior A ∪ interior B = Set.univ → ∀ R : ModuleCat.{u} ℤ,
      ∃ e : HomotopyEquiv ((singularExcisionSmallPair X A B).chainComplex R)
          ((singularSubspace X A).pair.chainComplex R),
        e.hom = SSetPair.chainComplexMap (singularExcisionSmallInclusion X A B) R := by
    intro X A B hcover R
    exact ⟨NativeBarycentricOperators.smallRelativeHomotopyEquiv.{u, u} X A B hcover R, rfl⟩
  have hsource : ∀ (X : TopCat.{u}) (A B : Set X),
      interior A ∪ interior B = Set.univ → ∀ R : ModuleCat.{u} ℤ,
      (∃ e : HomotopyEquiv ((singularExcisionSource X A B).chainComplex R)
          ((singularSubspacePair X A).chainComplex R),
        e.hom = SSetPair.chainComplexMap (singularExcisionInclusion X A B) R) ∧
      ∀ n : ℕ, IsIso (SSetPair.homologyMap (singularExcisionInclusion X A B) R n) := by
    intro X A B hcover R
    obtain ⟨small, hs⟩ := hsmall X A B hcover R
    obtain ⟨e, he⟩ := excision_source_equiv_of_small X A B R small hs
    exact ⟨⟨e, he⟩, excision_homology_isIso_of_equiv X A B R e he⟩
  refine ⟨excision_quotient_iso, ?_, excision_homology_naturality,
    excision_coefficient_naturality, ?_⟩
  · intro X A B hcover R
    exact ⟨hsmall X A B hcover R, hsource X A B hcover R⟩
  · intro X A Z _ hZ R
    exact hsource X A Zᶜ (excision_complement_cover X A Z hZ) R

end
end HolomorphicAnosov




