import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

/-!
# Naturality of the singular cup cochain

Source: Hatcher, *Algebraic Topology*, Proposition 3.10, p. 210. This is the
cochain identity before passage to ordinary or relative cohomology.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- The front/back singular cup cochain commutes with pullback.

Source: Hatcher, *Algebraic Topology*, Proposition 3.10, p. 210. Evaluate
on each free singular generator. The chain map takes that generator to the
postcomposed simplex. Its front and back faces are the postcompositions of
the original front and back faces, so both sides evaluate to the same product.
This holds for arbitrary cochains, including degree zero and the zero ring. -/
theorem pullback_cupCochain (R : Type u) [CommRing R]
    {X Y : TopCat.{u}} (f : X ⟶ Y) {p q : ℕ}
    (a : cochains R Y p) (b : cochains R Y q) :
    (pullback R f).f (p + q) (cupCochain R Y a b) =
      cupCochain R X ((pullback R f).f p a) ((pullback R f).f q b) := by
  change (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f (p + q) ≫
      cupCochain R Y a b = _
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  simp only [cupCochain, SSet.ιChainComplex, Sigma.ι_comp_desc]
  congr 2
  congr 1
  · change (a.hom (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of R R)
        ((TopCat.toSSet.obj Y).map (cupFront p q).op
          ((TopCat.toSSet.map f).app _ σ))).hom 1)) =
      (((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (cupFront p q).op σ) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f p) ≫ a).hom 1
    rw [SSet.ι_chainComplexMap_f]
    rfl
  · change (b.hom (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of R R)
        ((TopCat.toSSet.obj Y).map (cupBack p q).op
          ((TopCat.toSSet.map f).app _ σ))).hom 1)) =
      (((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).map (cupBack p q).op σ) ≫
          (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f q) ≫ b).hom 1
    rw [SSet.ι_chainComplexMap_f]
    rfl

end HolomorphicAnosov.SingularCochain
