import HolomorphicAnosov.Topology.SimplicialPrismCommutingSquare
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Topology.Homotopy.TopCat.ToSSet
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.Algebra.Homology.Homotopy

/-!
# Homotopy invariance of relative singular homology

Source: Hatcher, *Algebraic Topology*, Proposition 2.19, p.118; the prism
calculation in Theorem 2.10 and Proposition 2.12, pp.112–113; relative chains
on p.115; arbitrary abelian coefficients on p.153. The categorical version
uses the same prism and the degreewise cokernels of Mathlib's relative
simplicial chain complex, applied to the actual singular functor on pairs.
-/

namespace HolomorphicAnosov

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped Simplicial

universe u v w

/-- Descend the actual absolute prism through the native degreewise
relative cokernels. Source: Hatcher Proposition 2.19 p.118. The cylinder
square is the all-time preservation of subspace chains, not a chain
homotopy or induced homology equality assumed in advance. -/
noncomputable def relativePrism
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
    {P Q : SSetPair.{u}} {f g : P ⟶ Q}
    (H : SSet.Homotopy f.hom.right g.hom.right)
    (H' : SSet.Homotopy f.hom.left g.hom.left)
    (hsquare : (P.hom ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ H.h =
      H'.h ≫ Q.hom) (R : C) :
    _root_.Homotopy (SSetPair.chainComplexMap f R) (SSetPair.chainComplexMap g R) := by
  classical
  let K := H.chainComplexMap R
  have hzero (i j : ℕ) : (SSet.chainComplexMap P.hom R).f i ≫
      K.hom i j ≫ (Q.chainComplexπ R).f j = 0 := by
    rw [← Category.assoc,
      simplicial_prism_commuting_square H H' P.hom Q.hom hsquare R i j,
      Category.assoc, SSetPair.chainComplex_condition_f, CategoryTheory.Limits.comp_zero]
  let k : ∀ i j, (P.chainComplex R).X i ⟶ (Q.chainComplex R).X j := fun i j ↦
    (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkChainComplexX R i)
      (K.hom i j ≫ (Q.chainComplexπ R).f j) (hzero i j)).1
  have hk (i j : ℕ) : (P.chainComplexπ R).f i ≫ k i j =
      K.hom i j ≫ (Q.chainComplexπ R).f j :=
    (CokernelCofork.IsColimit.desc' (P.isColimitCokernelCoforkChainComplexX R i)
      (K.hom i j ≫ (Q.chainComplexπ R).f j) (hzero i j)).2
  refine { hom := k, zero := ?_, comm := ?_ }
  · intro i j hij
    apply (cancel_epi ((P.chainComplexπ R).f i)).mp
    rw [hk, K.zero i j hij, CategoryTheory.Limits.zero_comp,
      CategoryTheory.Limits.comp_zero]
  · intro i
    apply (cancel_epi ((P.chainComplexπ R).f i)).mp
    have hn (z : P ⟶ Q) :
        (P.chainComplexπ R).f i ≫ (SSetPair.chainComplexMap z R).f i =
          (SSet.chainComplexMap z.hom.right R).f i ≫ (Q.chainComplexπ R).f i := by
      exact (HomologicalComplex.congr_hom (((SSetPair.chainComplexFunctorπ C).app R).naturality z) i).symm
    rw [hn, K.comm i]
    simp only [Preadditive.add_comp, Preadditive.comp_add]
    rw [← dNext_comp_right K.hom (Q.chainComplexπ R) i,
      ← prevD_comp_right K.hom (Q.chainComplexπ R) i,
      ← dNext_comp_left (P.chainComplexπ R) k i,
      ← prevD_comp_left (P.chainComplexπ R) k i, hn]
    simp only [hk]

/-- The singular cylinder comparison respects the actual inclusion square
of a topological pair homotopy. This is functoriality and tensorator
naturality, before any prism or relative quotient is constructed. -/
theorem singular_pair_homotopy_square {P Q : TopPair.{u}} {f g : P ⟶ Q}
    (H : TopPair.Homotopy f g) :
    (TopCat.toSSet.map P.map ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
      H.fst.toSSet.h = H.snd.toSSet.h ≫ TopCat.toSSet.map Q.map := by
  dsimp only [TopCat.Homotopy.toSSet]
  rw [← whisker_exchange_assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.map_comp, H.w, Functor.map_comp]
  simp only [Category.assoc]

/-- Homotopic maps of topological pairs induce chain-homotopic relative singular
chain maps for any coefficient object in a preadditive category with the
required coproducts. Whenever the two complexes have homology in a degree,
the induced homology maps agree in that degree.

For subsets A⊆X and B⊆Y, use `TopPair.ofSubset` with their actual subspace
topologies. The ambient component of `TopPair.Homotopy` is a jointly continuous
homotopy with the given endpoints, and its subspace component and square say
that it maps A into B at every time. Conversely such an ambient homotopy
restricts continuously into B, giving this native pair homotopy. Taking the
coefficient category to be abelian groups or ℤ-modules and its object to be
any abelian group gives ordinary relative singular homology with those
coefficients, including integer coefficients and degree zero.

Source and complete natural-language proof: Hatcher, Proposition 2.19, p.118,
using the signed prism on pp.112–113 and the coefficient discussion on p.153.
For an n-simplex σ, let v_j=(vertex_j,0) and w_j=(vertex_j,1). Its prism
operator is the sum, for i=0,…,n, with sign (−1)^i, of the simplices obtained
by composing H∘(σ×id) with the affine simplex whose ordered vertices are
[v_0,…,v_i,w_i,…,w_n]. Apply each signed simplex map to the same coefficient
object; coproducts define the operator on arbitrary coefficient objects.

In the boundary of prism i, removing v_j has sign (−1)^(i+j), and removing
w_j has sign (−1)^(i+j+1). The shared face removing w_i from prism i equals
the face removing v_(i+1) from prism i+1 and the two signs cancel. The
remaining top and bottom faces give gσ and −fσ. A lateral lower face j<i
corresponds to prism i−1 of face_j σ, and a lateral upper face j>i to prism
i of face_j σ; in both cases its sign is opposite to the corresponding
term in P∂. Thus ∂P+P∂=g_#−f_#. In degree zero the prism is the single
path from fσ to gσ and has that boundary. Negative-degree terms are zero.

If σ takes values in A, every prism simplex takes values in B, by the
all-time pair condition. This shows that the prism on the ambient complexes
commutes with the inclusions of subspace chains and the prism for the
restricted homotopy. In the singular simplicial model, the same square
follows by functoriality of the singular functor and naturality of its
product comparison before applying the finite signed prism construction.
Use the absolute Mathlib chain homotopy with its own sign convention:
its equation has f_#−g_#, so it is the negative of the displayed P. The
inclusion square and the relative descent are unchanged by that sign.

Write q_P and q_Q for the actual relative cokernel projections. In every
degree (i,j), inclusion_A followed by the absolute homotopy component K_ij
followed by q_Q,j is zero, because the inclusion square factors through
inclusion_B. The degreewise cokernel universal property gives a unique
component K̄_ij with q_P,i K̄_ij=K_ij q_Q,j. Where i+1≠j the absolute
component is zero, so uniqueness makes K̄_ij zero as well. Precompose the
required relative homotopy equation with q_P,i. Move projections across
differentials using their chain-map equations, replace the descended
components by their defining equations, and apply the absolute homotopy
equation. Naturality of the relative projection identifies the remaining
endpoint maps. Since each q_P,i is a cokernel projection, cancellation
proves the relative equation itself. These components therefore give the
chain homotopy asserted below.

For any degree with homology in both complexes, a chain homotopy induces
equal maps on homology. Concretely, a relative cycle has zero boundary only
modulo the subspace chains; the descended prism equation makes the
difference of its endpoint images a relative boundary. No absolute-cycle
condition is substituted. The construction uses no closedness, good-pair,
nonemptiness, positive-degree, or nonzero-coefficient hypothesis. Empty
simplex indexing sets give zero coproducts; an empty subspace gives absolute
chains, and a whole subspace gives the zero relative complex.
DAG node: `topo.relative_singular_homotopy_invariance`.
-/
theorem relative_singular_homotopy_invariance
    (C : Type v) [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
    {P Q : TopPair.{u}} {f g : P ⟶ Q} (H : TopPair.Homotopy f g) (R : C) :
    Nonempty (_root_.Homotopy
      (SSetPair.chainComplexMap (singularPairFunctor.map f) R)
      (SSetPair.chainComplexMap (singularPairFunctor.map g) R)) ∧
    ∀ (n : ℕ)
      [((singularPairFunctor.obj P).chainComplex R).HasHomology n]
      [((singularPairFunctor.obj Q).chainComplex R).HasHomology n],
      HomologicalComplex.homologyMap
          (SSetPair.chainComplexMap (singularPairFunctor.map f) R) n =
        HomologicalComplex.homologyMap
          (SSetPair.chainComplexMap (singularPairFunctor.map g) R) n := by
  let K := relativePrism
    (P := singularPairFunctor.obj P) (Q := singularPairFunctor.obj Q)
    (f := singularPairFunctor.map f) (g := singularPairFunctor.map g)
    H.fst.toSSet H.snd.toSSet
    (singular_pair_homotopy_square H) R
  exact ⟨⟨K⟩, fun n ↦ K.homologyMap_eq n⟩


end HolomorphicAnosov
