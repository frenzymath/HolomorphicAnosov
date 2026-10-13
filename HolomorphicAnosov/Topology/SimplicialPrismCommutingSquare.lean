import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance

/-!
# Naturality of the simplicial chain prism

Source: Hatcher, *Algebraic Topology*, Theorem 2.10, pp.111–113, and
Proposition 2.19, p.118: the same signed prism construction respects maps
and subspace chains. This module states the categorical simplicial-set
form using Mathlib's existing cylinder, combinatorial homotopy, and
chainComplexMap constructions. The preadditive coefficient/category
universes are those of Mathlib's chain construction, not restrictions
printed in Hatcher's topological integer-chain exposition.
DAG node: `topo.simplicial_prism_commuting_square_g8`.
-/

namespace HolomorphicAnosov

universe v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial

/-- A commuting square of simplicial cylinders induces the corresponding
commuting square of every component of the actual chain-prism homotopies.

Source: Hatcher, Theorem 2.10, pp.111–113, and Proposition 2.19, p.118;
Mathlib `SSet.Homotopy.toSimplicialObjectHomotopy` and
`SSet.Homotopy.chainComplexMap` supply the exact existing prism objects.
The hypothesis is the original cylinder-square equality; the conclusion
is its derived chain-component equality, not an assumed chain square.
There is no additional endpoint square, face hypothesis, homology map,
positive-degree requirement, coefficient change, or topology assumption.
The arbitrary degree pair i,j includes the zero-supported components.

Complete natural-language proof (formal proof deferred to Stage3):

SP1. Retain the literal universe-polymorphic data: A,X,B,Y:SSet.{w}; maps f,g:X->Y and f',g':A->B;
homotopies H and H'; maps a:A->X and b:B->Y; and the supplied equality (a whiskerRight Delta[1])
then H.h = H'.h then b. For the chain statement let C:Type u carry Category.{v}, Preadditive C and
HasCoproducts.{w} C, take the unchanged coefficient object R:C, and quantify arbitrary i,j:Nat. No
ModuleCat, integer coefficient, topology, nonempty simplex set or relation among u,v,w is
substituted.

SP2. Fix n:Nat, k:Fin(n+1) and x in A_n. Let y_x:Delta[n]->A be SSet.yonedaEquiv.symm x. The exact
Yoneda composition equation rewrites the representable simplex of a_n(x) as y_x then a. Right
whiskering preserves this composite, so after reassociation the expression defining the k-th
component of H on a_n(x) contains (y_x whiskerRight Delta[1]) then (a whiskerRight Delta[1]) then
H.h. Replace the last two factors using the supplied square, and evaluate at the same
distinguished (n+1)-simplex of Delta[n] tensor Delta[1] used by toSimplicialObjectHomotopy.
Extensionality in x gives a_n then h_k^H = h_k^H' then b_(n+1), with all degrees literal. Unfold
the exact pinned `CategoryTheory.MonoidalCategory.comp_whiskerRight` theorem: for composable
morphisms `f : W ⟶ X` and `g : X ⟶ Y` and an object Z, right whiskering preserves composition, `(f
≫ g) ▷ Z = (f ▷ Z) ≫ (g ▷ Z)`. Here it applies to the literal Yoneda representative and simplicial
map with the same cylinder object; no associator, symmetry, or product comparison premise is
added.

SP3. Apply the actual functor sigmaConst.obj R to the degree-i component equality for every
k:Fin(i+1). Functor.map_comp turns the image of each composite into the corresponding composite of
images. By the definitions of SSet.chainComplexMap and H.chainComplexMap, these images are exactly
the degree-i chain-map components and the mapped prism-simplex components; no coefficient change
or comparison is inserted.

SP4. In the case j=i+1, expand both homotopy components by ToChainHomotopy.hom_eq as the negative
finite sum over k:Fin(i+1) of ((-1:Int)^k) times the mapped prism component. In the preadditive
category, composition on either side commutes with negation, the Finset sum and integer scalar
multiplication. Finset.sum_congr applies the mapped degreewise equality term by term on the
identical Finset.univ. Reassemble the signed sums to obtain (chainComplexMap a R).f i then
K(i,i+1) = K'(i,i+1) then (chainComplexMap b R).f(i+1). At i=0 the index Fin(1) has its single
term, so no positive-degree hypothesis occurs. Unfold the exact pinned preadditive composition
laws: in any category C with `Preadditive C`, composition on either side preserves negation,
integer scalar multiplication, and finite sums: `(-f) ≫ g = -(f ≫ g)`, `f ≫ (-g) = -(f ≫ g)`, both
zsmul laws, and both finite-sum laws. The prism consumer applies these laws to the negative
`Finset.univ` sum over `Fin(i+1)` and the integer coefficients `(-1 : Int)^k`; the index type and
finite set remain arbitrary.

SP5. If i+1 is not j, the support field of each chain homotopy gives K(i,j)=0 and K'(i,j)=0. The
exact CategoryTheory.Limits.comp_zero and CategoryTheory.Limits.zero_comp laws make the two
displayed composites zero. The equality and inequality cases exhaust arbitrary i,j, including i=0
and every universe-compatible coefficient object R. Unfold the exact pinned `HasZeroMorphisms`
laws: in any category with designated zero morphisms, every composable `f` satisfies `f ≫ 0 = 0`
and every composable `g` satisfies `0 ≫ g = 0`, with no preadditivity, additive-functor, limit, or
nonempty hom-set premise. The consumer applies these two laws to the zero support fields of the
chain homotopy, preserving the stated category and universe parameters.
-/
theorem simplicial_prism_commuting_square
    {A X B Y : SSet.{w}} {f g : X ⟶ Y} {f' g' : A ⟶ B}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (a : A ⟶ X) (b : B ⟶ Y)
    (hsquare : (a ▷ Δ[1]) ≫ H.h = H'.h ≫ b)
    {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
    (R : C) (i j : ℕ) :
    (SSet.chainComplexMap a R).f i ≫ (H.chainComplexMap R).hom i j =
      (H'.chainComplexMap R).hom i j ≫ (SSet.chainComplexMap b R).f j := by
  have hprism (n : ℕ) (k : Fin (n + 1)) :
      a.app _ ≫ H.toSimplicialObjectHomotopy.h k =
        H'.toSimplicialObjectHomotopy.h k ≫ b.app _ := by
    ext x
    change ((SSet.yonedaEquiv.symm (a.app _ x) ▷ Δ[1]) ≫ H.h).app _ _ =
      (((SSet.yonedaEquiv.symm x ▷ Δ[1]) ≫ H'.h) ≫ b).app _ _
    rw [← SSet.yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, hsquare,
      ← Category.assoc]
  by_cases hij : i + 1 = j
  · subst j
    change _ ≫ CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
        (H.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj R)) i (i + 1) =
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
        (H'.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj R)) i (i + 1) ≫ _
    simp only [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    change (sigmaConst.obj R).map (a.app _) ≫
        (sigmaConst.obj R).map (H.toSimplicialObjectHomotopy.h k) =
      (sigmaConst.obj R).map (H'.toSimplicialObjectHomotopy.h k) ≫
        (sigmaConst.obj R).map (b.app _)
    simpa only [Functor.map_comp] using congrArg ((sigmaConst.obj R).map) (hprism i k)
  · change _ ≫ CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
        (H.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj R)) i j =
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom
        (H'.toSimplicialObjectHomotopy.whiskerRight (sigmaConst.obj R)) i j ≫ _
    simp only [CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq_zero _ _ _ hij,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]


end HolomorphicAnosov
