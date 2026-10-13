import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import HolomorphicAnosov.Topology.Homology.SingularSimplexCone
import HolomorphicAnosov.Topology.Homology.SingularSimplexConeFaces

/-!
# Singular cones and their signed tensor contraction

Bredon, *Topology and Geometry* (1993), IV Theorem 15.5, pp.219–220,
and VI Lemma 1.1, p.316. Chains are Mathlib's ordinary unnormalized
singular chains with the unit coefficient module ℚ, and tensor products
are Mathlib's total tensor complexes, including their degree-zero corner.
-/

noncomputable section

namespace HolomorphicAnosov
namespace SingularConvexCone

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped Simplicial

/-- Ordinary rational unnormalized singular chains, with unit coefficients. -/
abbrev chains (M : Model) : ChainComplex (ModuleCat ℚ) ℕ :=
  (TopCat.toSSet.obj M.space).chainComplex (ModuleCat.of ℚ ℚ)

/-- The cone simplex as an actual generator of the native singular set. -/
def coneGenerator (M : Model) (o : M.space) {n : ℕ}
    (σ : (TopCat.toSSet.obj M.space).obj (Opposite.op ⦋n⦌)) :
    (TopCat.toSSet.obj M.space).obj (Opposite.op ⦋n + 1⦌) :=
  (TopCat.toSSetObjEquiv M.space (Opposite.op ⦋n + 1⦌)).symm
    (cone M o (TopCat.toSSetObjEquiv M.space (Opposite.op ⦋n⦌) σ))

/-- Q-linear extension of the literal cone on simplex generators, by the
native degree coproduct universal property (Bredon IV15.5, p.220). -/
def coneMap (M : Model) (o : M.space) (n : ℕ) :
    (chains M).X n ⟶ (chains M).X (n + 1) :=
  ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
    (ModuleCat.of ℚ ℚ) n).desc
      (Cofan.mk _ (fun σ =>
        (TopCat.toSSet.obj M.space).ιChainComplex (coneGenerator M o σ)))

/-- The base point, as an actual singular zero-simplex. -/
def baseGenerator (M : Model) (o : M.space) :
    (TopCat.toSSet.obj M.space).obj (Opposite.op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv M.space (Opposite.op ⦋0⦌)).symm (ContinuousMap.const _ o)

/-- Bredon's augmentation endomorphism: every zero-generator maps to [o],
and all positive-degree components are zero. -/
def epsilonComponent (M : Model) (o : M.space) :
    ∀ n, (chains M).X n ⟶ (chains M).X n := fun n => match n with
  | 0 => ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) 0).desc
      (Cofan.mk _ (fun _ =>
        (TopCat.toSSet.obj M.space).ιChainComplex (baseGenerator M o)))
  | _ + 1 => 0

/-- The augmentation components commute with the native singular differential.

Source: Bredon VI1.1 p.316, ε as explicitly specified there. Proof: only a
degree-one boundary can land in the nonzero degree-zero component. Its two
faces have coefficients +1 and -1, and both are sent to [o], so their sum
is zero. In every other degree either the ε component is zero or the outgoing
degree-zero differential is zero by the complex shape. Check this on the
actual singular generators using SSet.ιChainComplex_d and extend by the
coproduct hom-ext theorem. This covers all off-shape pairs i,j as well. -/
theorem epsilonComponent_comm (M : Model) (o : M.space) (i j : ℕ) :
    epsilonComponent M o i ≫ (chains M).d i j =
      (chains M).d i j ≫ epsilonComponent M o j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have hij' : j + 1 = i := hij
    subst i
    cases j with
    | succ j => simp [epsilonComponent]
    | zero =>
      change 0 ≫ (chains M).d 1 0 = (chains M).d 1 0 ≫ epsilonComponent M o 0
      rw [zero_comp]
      have hι (σ : (TopCat.toSSet.obj M.space).obj (Opposite.op ⦋0⦌)) :
          (TopCat.toSSet.obj M.space).ιChainComplex σ ≫ epsilonComponent M o 0 =
            (TopCat.toSSet.obj M.space).ιChainComplex (baseGenerator M o) := by
        exact ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
          (ModuleCat.of ℚ ℚ) 0).fac (Cofan.mk _ (fun _ ↦
            (TopCat.toSSet.obj M.space).ιChainComplex (R := ModuleCat.of ℚ ℚ)
              (baseGenerator M o))) (Discrete.mk σ)
      symm
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hι]
      simp [Fin.sum_univ_succ]
  · rw [(chains M).shape i j hij]
    simp

/-- Bredon's actual augmentation chain endomorphism, not the positive-degree
map induced by the constant continuous map. -/
def epsilon (M : Model) (o : M.space) : chains M ⟶ chains M where
  f := epsilonComponent M o
  comm' := fun i j _ => epsilonComponent_comm M o i j

/-- The explicit degree-one cone family, zero outside the raising-degree shape. -/
def coneHom (M : Model) (o : M.space) (i j : ℕ) :
    (chains M).X i ⟶ (chains M).X j :=
  if h : i + 1 = j then coneMap M o i ≫ eqToHom (congrArg (chains M).X h)
  else 0

/-- Bredon's cone-face calculation in the exact native chain-homotopy convention.

Source: IV15.5 pp.219–220. Proof: zeroth face of Dσ is σ. Its i-th face
for i>0 is D of face i-1 of σ, by inserting a zero weight in the literal
formula; both sides agree also at the apex. The alternating native boundary
therefore gives ∂Dσ=σ-D∂σ in positive degree, reindexing i>0. For a
zero-simplex x the two endpoints give ∂D[x]=[x]-[o], and the degree-minus-one
term is absent. Extend these generator equalities using the native coproduct
hom-ext theorem. `dNext` is the D∂ term and `prevD` is
the ∂D term; their order is categorical composition order. The result is
id=D∂+∂D+ε, including degree zero. If i+1≠j the explicit hom family is
zero by definition. Constants remain actual degenerate simplices: D[o] is
the constant one-simplex, not zero. Dimensions r=0/s=0 need no exception. -/
theorem coneHom_certificate (M : Model) (o : M.space) :
    (∀ i j, ¬ (ComplexShape.down ℕ).Rel j i → coneHom M o i j = 0) ∧
    (∀ i, (𝟙 (chains M) : chains M ⟶ chains M).f i =
      dNext i (coneHom M o) + prevD i (coneHom M o) +
        (epsilon M o).f i) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact dite_eq_right hij
  · have hface0 (n : ℕ)
        (σ : (TopCat.toSSet.obj M.space).obj (Opposite.op ⦋n⦌)) :
        (TopCat.toSSet.obj M.space).δ 0 (coneGenerator M o σ) = σ := by
      apply (TopCat.toSSetObjEquiv M.space _).injective
      apply ContinuousMap.ext
      intro t
      change coneRaw M o (TopCat.toSSetObjEquiv M.space _ σ)
        (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2))) t) = _
      cases M with
      | simplex r => exact simplexConeRaw_face_zero _ _ _
      | product r s =>
        apply Prod.ext
        · exact simplexConeRaw_face_zero _ _ _
        · exact simplexConeRaw_face_zero _ _ _
    have hfaceSucc (n : ℕ)
        (σ : (TopCat.toSSet.obj M.space).obj (Opposite.op ⦋n + 1⦌))
        (i : Fin (n + 2)) :
        (TopCat.toSSet.obj M.space).δ i.succ (coneGenerator M o σ) =
          coneGenerator M o ((TopCat.toSSet.obj M.space).δ i σ) := by
      apply (TopCat.toSSetObjEquiv M.space _).injective
      apply ContinuousMap.ext
      intro t
      change coneRaw M o (TopCat.toSSetObjEquiv M.space _ σ)
          (Convexity.StdSimplex.map i.succ.succAbove t) = _
      cases M with
      | simplex r => exact simplexConeRaw_face_succ _ _ _ _
      | product r s =>
        apply Prod.ext
        · exact simplexConeRaw_face_succ _ _ _ _
        · exact simplexConeRaw_face_succ _ _ _ _
    have hcone (n : ℕ)
        (σ : (TopCat.toSSet.obj M.space).obj (Opposite.op ⦋n⦌)) :
        (TopCat.toSSet.obj M.space).ιChainComplex σ ≫ coneMap M o n =
          (TopCat.toSSet.obj M.space).ιChainComplex (coneGenerator M o σ) := by
      exact ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
        (ModuleCat.of ℚ ℚ) n).fac (Cofan.mk _ (fun σ =>
          (TopCat.toSSet.obj M.space).ιChainComplex (coneGenerator M o σ)))
          (Discrete.mk σ)
    have hch (n : ℕ) : coneHom M o n (n + 1) = coneMap M o n := by
      simp [coneHom]
    intro i
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, hch]
      simp only [zero_add, HomologicalComplex.id_f]
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [Preadditive.comp_add, ← Category.assoc, hcone, SSet.ιChainComplex_d]
      have hι : (TopCat.toSSet.obj M.space).ιChainComplex σ ≫ (epsilon M o).f 0 =
          (TopCat.toSSet.obj M.space).ιChainComplex (baseGenerator M o) := by
        exact ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
          (ModuleCat.of ℚ ℚ) 0).fac (Cofan.mk _ (fun _ =>
            (TopCat.toSSet.obj M.space).ιChainComplex (baseGenerator M o)))
          (Discrete.mk σ)
      have hlast : (TopCat.toSSet.obj M.space).δ (1 : Fin 2) (coneGenerator M o σ) =
          baseGenerator M o := by
        apply (TopCat.toSSetObjEquiv M.space _).injective
        apply ContinuousMap.ext
        intro t
        change coneRaw M o (TopCat.toSSetObjEquiv M.space _ σ)
          (Convexity.StdSimplex.map (Fin.succAbove (1 : Fin 2)) t) = o
        have ht : t.weights 0 = 1 := by simp
        have hw : (Convexity.StdSimplex.map (Fin.succAbove (1 : Fin 2)) t).weights 0 = 1 := by
          rw [Convexity.StdSimplex.weights_map]
          have hi : (1 : Fin 2).succAbove (0 : Fin 1) = 0 := rfl
          rw [← hi, Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective, ht]
        have hs {r : ℕ} (a : Simplex r) (τ : C(Simplex 0, Simplex r)) :
            simplexConeRaw a τ (Convexity.StdSimplex.map (Fin.succAbove (1 : Fin 2)) t) = a := by
          unfold simplexConeRaw
          apply dite_eq_right
          rw [hw]
          exact lt_irrefl 1
        cases M with
        | simplex r => exact hs _ _
        | product r s => exact Prod.ext (hs _ _) (hs _ _)
      rw [hι, Fin.sum_univ_succ]
      simp [hface0, hlast]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, hch, hch]
      have heps : (epsilon M o).f (n + 1) = 0 := rfl
      rw [heps, add_zero]
      simp only [HomologicalComplex.id_f]
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [Preadditive.comp_add]
      simp only [← Category.assoc]
      rw [hcone, SSet.ιChainComplex_d, SSet.ιChainComplex_d]
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hcone]
      rw [Fin.sum_univ_succ (n := n + 2)]
      simp only [hface0, hfaceSucc, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
        pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, Category.comp_id]
      abel

/-- Bredon's singular cone contraction with explicit data and proof certificates. -/
def contraction (M : Model) (o : M.space) :
    Homotopy (𝟙 (chains M)) (epsilon M o) where
  hom := coneHom M o
  zero := (coneHom_certificate M o).1
  comm := (coneHom_certificate M o).2

/-- The native total tensor complex: its (p,q) differential terms have signs
1 and (-1)^p; its total degree-zero differential is zero. Source: VI1.1. -/
abbrev tensorChains (M N : Model) := HomologicalComplex.tensorObj (chains M) (chains N)

/-- Bredon's E=D_M⊗id+ε_M⊗D_N, constructed by the native bifunctor
homotopy formulas and their additive composition. Their totalDesc maps
carry the Koszul signs, and preserve the actual total tensor carrier. -/
def tensorContraction (M N : Model) (oM : M.space) (oN : N.space) :
    Homotopy
      (HomologicalComplex.tensorHom (𝟙 (chains M)) (𝟙 (chains N)))
      (HomologicalComplex.tensorHom (epsilon M oM) (epsilon N oN)) :=
  (mapBifunctorMapHomotopy₁ (contraction M oM) (𝟙 (chains N))
    (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ)).trans
  (mapBifunctorMapHomotopy₂ (epsilon M oM) (contraction N oN)
    (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ))

/-- The literal coefficient sum of an ordinary zero-chain: every point
generator has coefficient sum one. Source: Bredon VI1.1, p.316. -/
def coefficientSum (M : Model) : (chains M).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
    (ModuleCat.of ℚ ℚ) 0).desc (Cofan.mk _ (fun _ => 𝟙 _))

/-- Coefficient sum in total degree zero. The total coproduct has only the
(0,0) summand; multiply its two ordinary coefficient sums using the native
unit-module unitor. The zero branches merely give well-typed maps on the
impossible positive-degree summands of total degree zero. Source: VI1.1. -/
def tensorCoefficientSum (M N : Model) :
    (tensorChains M N).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  HomologicalComplex₂.totalDesc
    ((((curriedTensor (ModuleCat ℚ)).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (chains M)).obj (chains N))
    (fun p q _ =>
      if hp : p = 0 then if hq : q = 0 then
        ((eqToHom (congrArg (chains M).X hp) ≫ coefficientSum M) ⊗ₘ
          (eqToHom (congrArg (chains N).X hq) ≫ coefficientSum N)) ≫
            (λ_ (ModuleCat.of ℚ ℚ)).hom
      else 0 else 0)

/-- Bredon's signed two-term tensor cone, on every actual tensor summand.

Source: VI1.1, p.316, its written Koszul expansion. Proof: unfold the two
native bifunctor homotopies and Homotopy.trans. The first totalDesc term
raises p to p+1 with sign one and applies D_M⊗id. The second raises q to
q+1 with sign (-1)^p and applies ε_M⊗D_N. This is precisely the down-ℕ
TensorSigns instance. The coproduct inclusion/totalDesc equations compute
each composite on the specified summand; eqToHom only transports the
displayed addition equalities. The second term vanishes for p>0 because
ε_M is zero there. Thus the (0,0) corner has two positive terms, as printed
in the source, and no degree-minus-one term is introduced. -/
theorem tensorContraction_formula (M N : Model) (oM : M.space) (oN : N.space)
    (p q : ℕ) :
    HomologicalComplex.ιTensorObj (chains M) (chains N) p q (p + q) rfl ≫
      (tensorContraction M N oM oN).hom (p + q) (p + q + 1) =
    ((coneMap M oM p ⊗ₘ 𝟙 ((chains N).X q)) ≫
      HomologicalComplex.ιTensorObj (chains M) (chains N)
        (p + 1) q (p + q + 1) (by omega)) +
    (-1 : ℤ) ^ p • (((epsilon M oM).f p ⊗ₘ coneMap N oN q) ≫
      HomologicalComplex.ιTensorObj (chains M) (chains N)
        p (q + 1) (p + q + 1) (by omega)) := by
  change HomologicalComplex.ιTensorObj (chains M) (chains N) p q (p + q) rfl ≫
      (mapBifunctorMapHomotopy.hom₁ (contraction M oM) (𝟙 (chains N))
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) (p + q) (p + q + 1) +
      mapBifunctorMapHomotopy.hom₂ (epsilon M oM) (contraction N oN)
        (curriedTensor (ModuleCat ℚ)) (ComplexShape.down ℕ) (p + q) (p + q + 1)) = _
  rw [Preadditive.comp_add]
  rw [mapBifunctorMapHomotopy.ιMapBifunctor_hom₁
      (contraction M oM) (𝟙 (chains N)) (curriedTensor (ModuleCat ℚ))
      (ComplexShape.down ℕ) (p + 1) p q (p + q) (p + q + 1) rfl (by simp),
    mapBifunctorMapHomotopy.ιMapBifunctor_hom₂
      (epsilon M oM) (contraction N oN) (curriedTensor (ModuleCat ℚ))
      (ComplexShape.down ℕ) p (q + 1) q (p + q) (p + q + 1) rfl (by simp)]
  simp [contraction, coneHom, ιMapBifunctorOrZero_eq,
    ComplexShape.ε₁, ComplexShape.ε₂, ComplexShape.ε, HomologicalComplex.ιTensorObj,
    tensorHom_def, Category.assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Units.smul_def]

/-- Cone and total tensor contractions, with the exact positive-degree and
coefficient-sum-zero filling consequences.

Source: Bredon IV15.5 pp.219–220 and VI1.1 p.316. Full proof: use the
actual cone face identities described in coneHom_certificate. They give
D∂+∂D=id-ε in every degree, and ε is a chain map by the endpoint
coefficient cancellation in epsilonComponent_comm. For a positive cycle z,
D∂z=0 and εz=0, so ∂Dz=z. In degree zero the outgoing differential is
zero, while εz=coefficientSum(z)[o] by the coproduct extension; hence a
zero coefficient sum gives ∂Dz=z. No assertion that all zero-cycles bound
is made.

For tensor chains the native total differential is ∂⊗id+id⊗∂ with the
second term signed (-1)^p on bidegree (p,q). By tensorContraction_formula,
E=D_M⊗id+ε_M⊗D_N in the graded convention. Expanding ∂E+E∂ gives two
mixed D_Ma⊗∂b terms with signs (-1)^(p+1) and (-1)^p; they cancel.
Terms with ∂ε_M and ε_M∂ vanish by augmentation commutation and their
zero differentials. What remains is (∂D_M+D_M∂)a⊗b plus
ε_Ma⊗(∂D_N+D_N∂)b. The latter survives only when p=0, with sign +1.
Substitution yields (a-ε_Ma)⊗b+ε_Ma⊗(b-ε_Nb)=a⊗b-ε_Ma⊗ε_Nb.
At p=q=0 the outgoing differential is absent and the same two endpoint
computations give the identity. The native bifunctor homotopy constructors
and their trans composition certify exactly this equation on the total
coproduct. Tensor-product generation and total coproduct hom-ext extend
the pure-tensor calculation to all chains. The tensor augmentation in degree
zero is tensorCoefficientSum(z)[o_M]⊗[o_N], and is zero in higher degrees.
Apply the tensor identity to cycles as before. All assertions retain ordinary
degenerate simplices, including both zero-dimensional models and point
factors. The chosen points are the only nonemptiness data required. -/
theorem cone_tensor_contraction (M N : Model) (oM : M.space) (oN : N.space) :
    (∀ n, dNext n (coneHom M oM) + prevD n (coneHom M oM) =
      (𝟙 (chains M) : chains M ⟶ chains M).f n - (epsilon M oM).f n) ∧
    (∀ n, dNext n (tensorContraction M N oM oN).hom +
        prevD n (tensorContraction M N oM oN).hom =
      (𝟙 (tensorChains M N) : tensorChains M N ⟶ tensorChains M N).f n -
        (HomologicalComplex.tensorHom (epsilon M oM) (epsilon N oN)).f n) ∧
    (∀ n (z : (chains M).X (n + 1)), (chains M).d (n + 1) n z = 0 →
      (chains M).d (n + 2) (n + 1) (coneMap M oM (n + 1) z) = z) ∧
    (∀ z : (chains M).X 0, coefficientSum M z = 0 →
      (chains M).d 1 0 (coneMap M oM 0 z) = z) ∧
    (∀ n (z : (tensorChains M N).X (n + 1)),
      (tensorChains M N).d (n + 1) n z = 0 →
      (tensorChains M N).d (n + 2) (n + 1)
        ((tensorContraction M N oM oN).hom (n + 1) (n + 2) z) = z) ∧
    (∀ z : (tensorChains M N).X 0, tensorCoefficientSum M N z = 0 →
      (tensorChains M N).d 1 0 ((tensorContraction M N oM oN).hom 0 1 z) = z) := by
  have hM := coneHom_certificate M oM
  have hT := (tensorContraction M N oM oN).comm
  have hid : HomologicalComplex.tensorHom (𝟙 (chains M)) (𝟙 (chains N)) =
      (𝟙 (tensorChains M N) : tensorChains M N ⟶ tensorChains M N) := by
    ext n i
    simp [HomologicalComplex.tensorHom, mapBifunctorMap]
  have heps0 (M : Model) (oM : M.space) : (epsilon M oM).f 0 =
      coefficientSum M ≫ (TopCat.toSSet.obj M.space).ιChainComplex
        (baseGenerator M oM) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    have h₁ := ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) 0).fac (Cofan.mk _ (fun _ =>
        (TopCat.toSSet.obj M.space).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          (baseGenerator M oM))) (Discrete.mk σ)
    have h₂ := ((TopCat.toSSet.obj M.space).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) 0).fac (Cofan.mk _ (fun _ => 𝟙 (ModuleCat.of ℚ ℚ)))
      (Discrete.mk σ)
    change (TopCat.toSSet.obj M.space).ιChainComplex σ ≫ (epsilon M oM).f 0 =
      (TopCat.toSSet.obj M.space).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        (baseGenerator M oM) at h₁
    change (TopCat.toSSet.obj M.space).ιChainComplex σ ≫ coefficientSum M = 𝟙 _ at h₂
    rw [h₁, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have h := hM.2 n
    have h' : (𝟙 (chains M) : chains M ⟶ chains M).f n - (epsilon M oM).f n =
        dNext n (coneHom M oM) + prevD n (coneHom M oM) := by
      rw [h]
      abel
    exact h'.symm
  · intro n
    have h := hT n
    have h' : (HomologicalComplex.tensorHom (𝟙 (chains M)) (𝟙 (chains N))).f n -
        (HomologicalComplex.tensorHom (epsilon M oM) (epsilon N oN)).f n =
        dNext n (tensorContraction M N oM oN).hom +
          prevD n (tensorContraction M N oM oN).hom := by
      rw [h]
      abel
    have hidn := congrArg (fun f => f.f n) hid
    rw [hidn] at h'
    exact h'.symm
  · intro n z hz
    have h := hM.2 (n + 1)
    have hz' := congrArg (fun f => f z) h
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hz'
    simp only [HomologicalComplex.id_f, CategoryStruct.comp, coneHom, dite_true,
      eqToHom_refl] at hz'
    change z = (coneMap M oM n) ((chains M).d (n + 1) n z) +
      (chains M).d (n + 2) (n + 1) ((coneMap M oM (n + 1)) z) +
      (epsilon M oM).f (n + 1) z at hz'
    have heps : (epsilon M oM).f (n + 1) = 0 := by rfl
    rw [hz, map_zero, zero_add, heps] at hz'
    simpa using hz'.symm
  · intro z hz
    have h := hM.2 0
    have hz' := congrArg (fun f => f z) h
    rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hz'
    simp only [HomologicalComplex.id_f, CategoryStruct.comp, coneHom, dite_true,
      eqToHom_refl, zero_add] at hz'
    change z = (chains M).d 1 0 ((coneMap M oM 0) z) + (epsilon M oM).f 0 z at hz'
    rw [heps0 M oM] at hz'
    change z = (chains M).d 1 0 ((coneMap M oM 0) z) +
      ((TopCat.toSSet.obj M.space).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        (baseGenerator M oM)).hom
        ((coefficientSum M).hom z) at hz'
    simpa [hz] using hz'.symm
  · intro n z hz
    have heps : (HomologicalComplex.tensorHom (epsilon M oM) (epsilon N oN)).f
        (n + 1) = 0 := by
      apply mapBifunctor.hom_ext
      intro i j h
      rw [ι_mapBifunctorMap]
      cases i with
      | zero =>
        cases j with
        | zero => simp at h
        | succ j => simp [epsilon, epsilonComponent]
      | succ i => simp [epsilon, epsilonComponent]
    have h := hT (n + 1)
    have hidn := congrArg (fun f => f.f (n + 1)) hid
    rw [hidn] at h
    have hz' := congrArg (fun f => f z) h
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hz'
    simp only [HomologicalComplex.id_f, CategoryStruct.comp, heps] at hz'
    change z = (tensorContraction M N oM oN).hom n (n + 1)
      ((tensorChains M N).d (n + 1) n z) +
      (tensorChains M N).d (n + 2) (n + 1)
        ((tensorContraction M N oM oN).hom (n + 1) (n + 2) z) + 0 at hz'
    simpa [hz] using hz'.symm
  · intro z hz
    let baseTensor := (λ_ (ModuleCat.of ℚ ℚ)).inv ≫
      ((TopCat.toSSet.obj M.space).ιChainComplex (R := ModuleCat.of ℚ ℚ)
        (baseGenerator M oM) ⊗ₘ
        (TopCat.toSSet.obj N.space).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          (baseGenerator N oN)) ≫
      HomologicalComplex.ιTensorObj (chains M) (chains N) 0 0 0 rfl
    have hcoeff : HomologicalComplex.ιTensorObj (chains M) (chains N) 0 0 0 rfl ≫
        tensorCoefficientSum M N =
        (coefficientSum M ⊗ₘ coefficientSum N) ≫ (λ_ (ModuleCat.of ℚ ℚ)).hom := by
      let K := (((curriedTensor (ModuleCat ℚ)).mapBifunctorHomologicalComplex
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj (chains M)).obj (chains N)
      let f : ∀ (p q : ℕ) (_ : ComplexShape.π (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (ComplexShape.down ℕ) (p, q) = 0),
          ((K.X p).X q ⟶ ModuleCat.of ℚ ℚ) := fun p q hpq =>
        if hp : p = 0 then if hq : q = 0 then
          ((eqToHom (congrArg (chains M).X hp) ≫ coefficientSum M) ⊗ₘ
            (eqToHom (congrArg (chains N).X hq) ≫ coefficientSum N)) ≫
              (λ_ (ModuleCat.of ℚ ℚ)).hom
        else 0 else 0
      have hsum : tensorCoefficientSum M N = K.totalDesc f := by rfl
      change K.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫ K.totalDesc f = f 0 0 rfl
      exact K.ι_totalDesc f 0 0 rfl
    have hepsT0 : (HomologicalComplex.tensorHom (epsilon M oM) (epsilon N oN)).f 0 =
        tensorCoefficientSum M N ≫ baseTensor := by
      apply mapBifunctor.hom_ext
      intro p q h
      have hpq : p + q = 0 := by simpa [ComplexShape.π] using h
      have hp : p = 0 := by omega
      have hq : q = 0 := by omega
      subst p; subst q
      rw [ι_mapBifunctorMap]
      conv_rhs => rw [← Category.assoc, hcoeff]
      simp only [curriedTensor_map_app, curriedTensor_obj_map,
        heps0 M oM, heps0 N oN]
      simp only [baseTensor, Category.assoc, Iso.hom_inv_id_assoc,
        tensorHom_def, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
        HomologicalComplex.ιTensorObj]
      simp only [whisker_exchange_assoc]
    have h := hT 0
    have hid0 := congrArg (fun f => f.f 0) hid
    rw [hid0] at h
    have hz' := congrArg (fun f => f z) h
    rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at hz'
    simp only [HomologicalComplex.id_f, CategoryStruct.comp, zero_add, hepsT0] at hz'
    change z = (tensorChains M N).d 1 0
      ((tensorContraction M N oM oN).hom 0 1 z) + baseTensor (tensorCoefficientSum M N z) at hz'
    simpa only [hz, map_zero, add_zero] using hz'.symm

end SingularConvexCone
end HolomorphicAnosov

