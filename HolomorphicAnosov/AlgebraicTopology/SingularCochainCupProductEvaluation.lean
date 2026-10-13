import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

/-!
# Evaluation of the singular cup cochain

Source: Hatcher, *Algebraic Topology*, front/back formula, p.206.
DAG node: `topo.singular_cochain_cup_product_evaluation_g6`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

/-- On a free singular generator, the cup cochain is the product of its front
and back evaluations. Source: Hatcher, *Algebraic Topology*, p.206. The native
coproduct injection followed by the defining `Sigma.desc` selects that summand;
its multiplication map evaluated at coefficient one is the stated product. -/
theorem cup_simplex_value (R : Type u) [CommRing R] (X : TopCat.{u}) {p q : ℕ}
    (a : cochains R X p) (b : cochains R X q)
    (σ : (TopCat.toSSet.obj X) _⦋p + q⦌) :
    simplexValue R X (cupCochain R X a b) σ =
      simplexValue R X a ((TopCat.toSSet.obj X).map (cupFront p q).op σ) *
        simplexValue R X b ((TopCat.toSSet.obj X).map (cupBack p q).op σ) := by
  change (((TopCat.toSSet.obj X).ιChainComplex σ) ≫ cupCochain R X a b).hom 1 = _
  simp [SSet.ιChainComplex, cupCochain]

end HolomorphicAnosov.SingularCochain
