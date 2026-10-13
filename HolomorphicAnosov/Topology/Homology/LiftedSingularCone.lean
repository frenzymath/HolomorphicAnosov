import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Monoidal
import HolomorphicAnosov.Topology.Homology.SingularSimplexCone
import HolomorphicAnosov.Topology.Homology.SingularSimplexConeFaces

/-!
# Singular cones on lifted models over an arbitrary commutative ring

Bredon, *Topology and Geometry* (1993), IV Theorem 15.5, pp.219–220,
and VI Lemma 1.1, p.316. Chains are Mathlib's ordinary unnormalized
singular chains with the unit coefficient module R, and tensor products
are Mathlib's total tensor complexes, including their degree-zero corner.
The original continuous cones are transported by ULift.up and ULift.down;
the face and boundary identities are proved for these actual lifted models.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HolomorphicAnosov
namespace LiftedSingularCone
open SingularConvexCone
universe u
variable (R : Type u) [CommRing R]

abbrev space (M : Model) : TopCat.{u} := TopCat.of (ULift.{u} M.space)


open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped Simplicial

/-- Ordinary unnormalized singular chains, with unit coefficients. -/
abbrev chains (M : Model) : ChainComplex (ModuleCat.{u} R) ℕ :=
  (TopCat.toSSet.obj (space M)).chainComplex (ModuleCat.of R R)

/-- The cone simplex as an actual generator of the native singular set. -/
def coneGenerator (M : Model) (o : space M) {n : ℕ}
    (σ : (TopCat.toSSet.obj (space M)).obj (Opposite.op ⦋n⦌)) :
    (TopCat.toSSet.obj (space M)).obj (Opposite.op ⦋n + 1⦌) :=
  (TopCat.toSSetObjEquiv (space M) (Opposite.op ⦋n + 1⦌)).symm
    (ContinuousMap.comp ⟨ULift.up, continuous_uliftUp⟩
      (cone M o.down (ContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩
        (TopCat.toSSetObjEquiv (space M) (Opposite.op ⦋n⦌) σ))))

/-- R-linear extension of the literal cone on simplex generators, by the
native degree coproduct universal property (Bredon IV15.5, p.220). -/
def coneMap (M : Model) (o : space M) (n : ℕ) :
    (chains R M).X n ⟶ (chains R M).X (n + 1) :=
  ((TopCat.toSSet.obj (space M)).isColimitChainComplexXCofan
    (ModuleCat.of R R) n).desc
      (Cofan.mk _ (fun σ =>
        (TopCat.toSSet.obj (space M)).ιChainComplex (coneGenerator M o σ)))

/-- The base point, as an actual singular zero-simplex. -/
def baseGenerator (M : Model) (o : space M) :
    (TopCat.toSSet.obj (space M)).obj (Opposite.op ⦋0⦌) :=
  (TopCat.toSSetObjEquiv (space M) (Opposite.op ⦋0⦌)).symm (ContinuousMap.const _ o)

/-- Bredon's augmentation endomorphism: every zero-generator maps to [o],
and all positive-degree components are zero. -/
def epsilonComponent (M : Model) (o : space M) :
    ∀ n, (chains R M).X n ⟶ (chains R M).X n := fun n => match n with
  | 0 => ((TopCat.toSSet.obj (space M)).isColimitChainComplexXCofan
      (ModuleCat.of R R) 0).desc
      (Cofan.mk _ (fun _ =>
        (TopCat.toSSet.obj (space M)).ιChainComplex (baseGenerator M o)))
  | _ + 1 => 0

/-- The augmentation components commute with the native singular differential.

Source: Bredon VI1.1 p.316, ε as explicitly specified there. Proof: only a
degree-one boundary can land in the nonzero degree-zero component. Its two
faces have coefficients +1 and -1, and both are sent to [o], so their sum
is zero. In every other degree either the ε component is zero or the outgoing
degree-zero differential is zero by the complex shape. Check this on the
actual singular generators using SSet.ιChainComplex_d and extend by the
coproduct hom-ext theorem. This covers all off-shape pairs i,j as well. -/
theorem epsilonComponent_comm (M : Model) (o : space M) (i j : ℕ) :
    epsilonComponent R M o i ≫ (chains R M).d i j =
      (chains R M).d i j ≫ epsilonComponent R M o j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have hij' : j + 1 = i := hij
    subst i
    cases j with
    | succ j => simp [epsilonComponent]
    | zero =>
      change 0 ≫ (chains R M).d 1 0 = (chains R M).d 1 0 ≫ epsilonComponent R M o 0
      rw [zero_comp]
      have hι (σ : (TopCat.toSSet.obj (space M)).obj (Opposite.op ⦋0⦌)) :
          (TopCat.toSSet.obj (space M)).ιChainComplex σ ≫ epsilonComponent R M o 0 =
            (TopCat.toSSet.obj (space M)).ιChainComplex (baseGenerator M o) := by
        exact ((TopCat.toSSet.obj (space M)).isColimitChainComplexXCofan
          (ModuleCat.of R R) 0).fac (Cofan.mk _ (fun _ ↦
            (TopCat.toSSet.obj (space M)).ιChainComplex (R := ModuleCat.of R R)
              (baseGenerator M o))) (Discrete.mk σ)
      symm
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hι]
      simp [Fin.sum_univ_succ]
  · rw [(chains R M).shape i j hij]
    simp

/-- Bredon's actual augmentation chain endomorphism, not the positive-degree
map induced by the constant continuous map. -/
def epsilon (M : Model) (o : space M) : chains R M ⟶ chains R M where
  f := epsilonComponent R M o
  comm' := fun i j _ => epsilonComponent_comm R M o i j

/-- The augmentation sends every zero simplex to its fixed base generator. -/
@[reassoc]
theorem ι_epsilon_zero (M : Model) (o : space M)
    (σ : (TopCat.toSSet.obj (space M)).obj (.op ⦋0⦌)) :
    (TopCat.toSSet.obj (space M)).ιChainComplex σ ≫ (epsilon R M o).f 0 =
      (TopCat.toSSet.obj (space M)).ιChainComplex (baseGenerator M o) :=
  ((TopCat.toSSet.obj (space M)).isColimitChainComplexXCofan
    (ModuleCat.of R R) 0).fac (Cofan.mk _ (fun _ ↦
      (TopCat.toSSet.obj (space M)).ιChainComplex (R := ModuleCat.of R R)
        (baseGenerator M o))) (Discrete.mk σ)

/-- The explicit degree-one cone family, zero outside the raising-degree shape. -/
def coneHom (M : Model) (o : space M) (i j : ℕ) :
    (chains R M).X i ⟶ (chains R M).X j :=
  if h : i + 1 = j then coneMap R M o i ≫ eqToHom (congrArg (chains R M).X h)
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
theorem coneHom_certificate (M : Model) (o : space M) :
    (∀ i j, ¬ (ComplexShape.down ℕ).Rel j i → coneHom R M o i j = 0) ∧
    (∀ i, (𝟙 (chains R M) : chains R M ⟶ chains R M).f i =
      dNext i (coneHom R M o) + prevD i (coneHom R M o) +
        (epsilon R M o).f i) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact dite_eq_right hij
  · have hface0 (n : ℕ)
        (σ : (TopCat.toSSet.obj (space M)).obj (Opposite.op ⦋n⦌)) :
        (TopCat.toSSet.obj (space M)).δ 0 (coneGenerator M o σ) = σ := by
      apply (TopCat.toSSetObjEquiv (space M) _).injective
      apply ContinuousMap.ext
      intro t
      apply ULift.ext
      change coneRaw M o.down (ContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩
        (TopCat.toSSetObjEquiv (space M) _ σ))
        (Convexity.StdSimplex.map (Fin.succAbove (0 : Fin (n + 2))) t) = _
      cases M with
      | simplex r => exact simplexConeRaw_face_zero _ _ _
      | product r s =>
        apply Prod.ext
        · exact simplexConeRaw_face_zero _ _ _
        · exact simplexConeRaw_face_zero _ _ _
    have hfaceSucc (n : ℕ)
        (σ : (TopCat.toSSet.obj (space M)).obj (Opposite.op ⦋n + 1⦌))
        (i : Fin (n + 2)) :
        (TopCat.toSSet.obj (space M)).δ i.succ (coneGenerator M o σ) =
          coneGenerator M o ((TopCat.toSSet.obj (space M)).δ i σ) := by
      apply (TopCat.toSSetObjEquiv (space M) _).injective
      apply ContinuousMap.ext
      intro t
      apply ULift.ext
      change coneRaw M o.down (ContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩
        (TopCat.toSSetObjEquiv (space M) _ σ))
          (Convexity.StdSimplex.map i.succ.succAbove t) = _
      cases M with
      | simplex r => exact simplexConeRaw_face_succ _ _ _ _
      | product r s =>
        apply Prod.ext
        · exact simplexConeRaw_face_succ _ _ _ _
        · exact simplexConeRaw_face_succ _ _ _ _
    have hcone (n : ℕ)
        (σ : (TopCat.toSSet.obj (space M)).obj (Opposite.op ⦋n⦌)) :
        (TopCat.toSSet.obj (space M)).ιChainComplex σ ≫ coneMap R M o n =
          (TopCat.toSSet.obj (space M)).ιChainComplex (coneGenerator M o σ) := by
      exact ((TopCat.toSSet.obj (space M)).isColimitChainComplexXCofan
        (ModuleCat.of R R) n).fac (Cofan.mk _ (fun σ =>
          (TopCat.toSSet.obj (space M)).ιChainComplex (coneGenerator M o σ)))
          (Discrete.mk σ)
    have hch (n : ℕ) : coneHom R M o n (n + 1) = coneMap R M o n := by
      simp [coneHom]
    intro i
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, hch]
      simp only [zero_add, HomologicalComplex.id_f]
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [Preadditive.comp_add, ← Category.assoc, hcone, SSet.ιChainComplex_d]
      have hι : (TopCat.toSSet.obj (space M)).ιChainComplex σ ≫ (epsilon R M o).f 0 =
          (TopCat.toSSet.obj (space M)).ιChainComplex (baseGenerator M o) := by
        exact ((TopCat.toSSet.obj (space M)).isColimitChainComplexXCofan
          (ModuleCat.of R R) 0).fac (Cofan.mk _ (fun _ =>
            (TopCat.toSSet.obj (space M)).ιChainComplex (baseGenerator M o)))
          (Discrete.mk σ)
      have hlast : (TopCat.toSSet.obj (space M)).δ (1 : Fin 2) (coneGenerator M o σ) =
          baseGenerator M o := by
        apply (TopCat.toSSetObjEquiv (space M) _).injective
        apply ContinuousMap.ext
        intro t
        apply ULift.ext
        change coneRaw M o.down (ContinuousMap.comp ⟨ULift.down, continuous_uliftDown⟩
          (TopCat.toSSetObjEquiv (space M) _ σ))
          (Convexity.StdSimplex.map (Fin.succAbove (1 : Fin 2)) t) = o.down
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
      simp only [Fin.sum_univ_succ]
      erw [hface0, hlast]
      simp
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, hch, hch]
      have heps : (epsilon R M o).f (n + 1) = 0 := rfl
      rw [heps, add_zero]
      simp only [HomologicalComplex.id_f]
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [Preadditive.comp_add]
      simp only [← Category.assoc]
      rw [hcone, SSet.ιChainComplex_d, SSet.ιChainComplex_d]
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hcone]
      rw [Fin.sum_univ_succ (n := n + 2)]
      have hs : (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.succ.val •
          (TopCat.toSSet.obj (space M)).ιChainComplex (R := ModuleCat.of R R)
            ((TopCat.toSSet.obj (space M)).δ i.succ (coneGenerator M o σ))) =
          ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.succ.val •
            (TopCat.toSSet.obj (space M)).ιChainComplex (R := ModuleCat.of R R)
              (coneGenerator M o ((TopCat.toSSet.obj (space M)).δ i σ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact congrArg (fun τ ↦ (TopCat.toSSet.obj (space M)).ιChainComplex
          (R := ModuleCat.of R R) τ) (hfaceSucc n σ i)
      erw [hs]
      simp only [hface0 (n + 1) σ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
        pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, Category.comp_id]
      abel

/-- Bredon's singular cone contraction with explicit data and proof certificates. -/
def contraction (M : Model) (o : space M) :
    Homotopy (𝟙 (chains R M)) (epsilon R M o) where
  hom := coneHom R M o
  zero := (coneHom_certificate R M o).1
  comm := (coneHom_certificate R M o).2

/-- The native total tensor complex: its (p,q) differential terms have signs
1 and (-1)^p; its total degree-zero differential is zero. Source: VI1.1. -/
abbrev tensorChains (M N : Model) := HomologicalComplex.tensorObj (chains R M) (chains R N)

/-- Bredon's E=D_M⊗id+ε_M⊗D_N, constructed by the native bifunctor
homotopy formulas and their additive composition. Their totalDesc maps
carry the Koszul signs, and preserve the actual total tensor carrier. -/
def tensorContraction (M N : Model) (oM : space M) (oN : space N) :
    Homotopy
      (HomologicalComplex.tensorHom (𝟙 (chains R M)) (𝟙 (chains R N)))
      (HomologicalComplex.tensorHom (epsilon R M oM) (epsilon R N oN)) :=
  (mapBifunctorMapHomotopy₁ (contraction R M oM) (𝟙 (chains R N))
    (curriedTensor (ModuleCat.{u} R)) (ComplexShape.down ℕ)).trans
  (mapBifunctorMapHomotopy₂ (epsilon R M oM) (contraction R N oN)
    (curriedTensor (ModuleCat.{u} R)) (ComplexShape.down ℕ))


/-- The tensor augmentation has zero positive components. -/
theorem tensor_epsilon_succ (M N : Model) (oM : space M) (oN : space N) (n : ℕ) :
    (HomologicalComplex.tensorHom (epsilon R M oM) (epsilon R N oN)).f (n + 1) = 0 := by
  apply mapBifunctor.hom_ext
  intro i j h
  rw [ι_mapBifunctorMap]
  cases i with
  | zero =>
    cases j with
    | zero => simp at h
    | succ j => simp [epsilon, epsilonComponent]
  | succ i => simp [epsilon, epsilonComponent]

/-- The identity tensor map is the identity on the total complex. -/
theorem tensor_id (M N : Model) :
    HomologicalComplex.tensorHom (𝟙 (chains R M)) (𝟙 (chains R N)) =
      (𝟙 (tensorChains R M N) : tensorChains R M N ⟶ tensorChains R M N) := by
  ext n i
  simp [HomologicalComplex.tensorHom, mapBifunctorMap]

/-- Every positive cycle on a lifted tensor model bounds.
Source: Bredon VI1.1, p.316. Precompose the tensor contraction identity with
the cycle; its dH term vanishes, and its augmentation component is zero in
positive degrees. The remaining term gives the required boundary. -/
theorem tensor_fill_positive (M N : Model) (oM : space M) (oN : space N)
    (n : ℕ) {V : ModuleCat.{u} R} (r : V ⟶ (tensorChains R M N).X (n + 1))
    (hr : r ≫ (tensorChains R M N).d (n + 1) n = 0) :
    (r ≫ (tensorContraction R M N oM oN).hom (n + 1) (n + 2)) ≫
      (tensorChains R M N).d (n + 2) (n + 1) = r := by
  have h := (tensorContraction R M N oM oN).comm (n + 1)
  rw [congrArg (fun f ↦ f.f (n + 1)) (tensor_id R M N), HomologicalComplex.id_f, tensor_epsilon_succ,
    Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, add_zero] at h
  have hh := congrArg (fun f ↦ r ≫ f) h
  simpa only [Category.comp_id, Preadditive.comp_add, ← Category.assoc,
    hr, zero_comp, zero_add] using hh.symm

/-- An augmentation-zero degree-zero tensor chain bounds by the same contraction.
Source: Bredon VI1.1, p.316. The degree-zero contraction identity has only
its Hd and augmentation terms; precompose and cancel the augmentation. -/
theorem tensor_fill_zero (M N : Model) (oM : space M) (oN : space N)
    {V : ModuleCat.{u} R} (r : V ⟶ (tensorChains R M N).X 0)
    (hr : r ≫ (HomologicalComplex.tensorHom (epsilon R M oM) (epsilon R N oN)).f 0 = 0) :
    (r ≫ (tensorContraction R M N oM oN).hom 0 1) ≫
      (tensorChains R M N).d 1 0 = r := by
  have h := (tensorContraction R M N oM oN).comm 0
  rw [congrArg (fun f ↦ f.f 0) (tensor_id R M N), HomologicalComplex.id_f,
    Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
  have hh := congrArg (fun f ↦ r ≫ f) h
  simpa only [Category.comp_id, Preadditive.comp_add, ← Category.assoc,
    hr, add_zero] using hh.symm

end LiftedSingularCone
end HolomorphicAnosov
