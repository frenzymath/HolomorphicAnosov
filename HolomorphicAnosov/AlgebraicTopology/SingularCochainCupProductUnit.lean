import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

/-!
# The constant-one unit for the singular cochain cup formula

Source: Hatcher, *Algebraic Topology*, front/back formula p.206 and
constant-one unit p.207. DAG node: `topo.singular_cochain_cup_product_unit_g6`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- The constant-one cochain is a two-sided unit for the actual front/back formula.

Source: Hatcher, *Algebraic Topology*, front/back formula p.206 and unit p.207.
Evaluate the right product on a free singular simplex: its front face is the
whole simplex, and its back factor is one. For the left product, the back face
is the whole simplex after identifying 0+p with p, and the front factor is one.
These evaluations determine the linear cochains because the free chain module
is the coproduct of copies of R, each determined by its coefficient-one element.
The explicit degree isomorphism is equality transport, not a new cohomology map.
This argument also covers degree zero, the empty space, and the zero ring. -/
theorem cupCochain_unit (R : Type u) [CommRing R]
    (X : TopCat.{u}) {p : ℕ} (a : cochains R X p) :
    cupCochain R X a (oneCochain R X) = a ∧
      ((complex R X).XIsoOfEq (Nat.zero_add p)).hom
        (cupCochain R X (oneCochain R X) a) = a := by
  constructor
  · apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    ext
    change (((TopCat.toSSet.obj X).ιChainComplex σ) ≫
      cupCochain R X a (oneCochain R X)).hom 1 = _
    simp only [cupCochain, SSet.ιChainComplex, Sigma.ι_comp_desc]
    have hf : cupFront p 0 = 𝟙 ⦋p⦌ := by ext i; rfl
    have hu : simplexValue R X (oneCochain R X)
        ((TopCat.toSSet.obj X).map (cupBack p 0).op σ) = 1 := by
      change (((TopCat.toSSet.obj X).ιChainComplex _) ≫ oneCochain R X).hom 1 = 1
      simp [SSet.ιChainComplex, oneCochain]
    simp only [ModuleCat.hom_ofHom, LinearMap.mulLeft_apply, mul_one]
    change simplexValue R X a ((TopCat.toSSet.obj X).map (cupFront p 0).op σ) *
      simplexValue R X (oneCochain R X)
        ((TopCat.toSSet.obj X).map (cupBack p 0).op σ) = simplexValue R X a σ
    rw [hu, mul_one]
    simp [hf]
  · apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    ext
    change simplexValue R X (((complex R X).XIsoOfEq (Nat.zero_add p)).hom
        (cupCochain R X (oneCochain R X) a)) σ = simplexValue R X a σ
    have htransport : ∀ {m n : ℕ} (h : m = n) (b : cochains R X m)
        (τ : (TopCat.toSSet.obj X) _⦋n⦌),
        simplexValue R X (((complex R X).XIsoOfEq h).hom b) τ =
          simplexValue R X b ((TopCat.toSSet.obj X).map
            (eqToHom (congrArg SimplexCategory.mk h)).op τ) := by
      intro m n h b τ
      subst h
      simp [HomologicalComplex.XIsoOfEq]
    rw [htransport]
    let τ := (TopCat.toSSet.obj X).map
      (eqToHom (congrArg SimplexCategory.mk (Nat.zero_add p))).op σ
    change (((TopCat.toSSet.obj X).ιChainComplex τ) ≫
      cupCochain R X (oneCochain R X) a).hom 1 = _
    simp only [cupCochain, SSet.ιChainComplex, Sigma.ι_comp_desc]
    have hu : simplexValue R X (oneCochain R X)
        ((TopCat.toSSet.obj X).map (cupFront 0 p).op τ) = 1 := by
      change (((TopCat.toSSet.obj X).ιChainComplex _) ≫ oneCochain R X).hom 1 = 1
      simp [SSet.ιChainComplex, oneCochain]
    simp only [ModuleCat.hom_ofHom, LinearMap.mulLeft_apply, mul_one]
    change simplexValue R X (oneCochain R X)
        ((TopCat.toSSet.obj X).map (cupFront 0 p).op τ) *
        simplexValue R X a ((TopCat.toSSet.obj X).map (cupBack 0 p).op τ) = _
    rw [hu, one_mul]
    have hb : cupBack 0 p ≫ eqToHom (congrArg SimplexCategory.mk (Nat.zero_add p)) =
        𝟙 ⦋p⦌ := by
      ext k
      simp [cupBack, SimplexCategory.eqToHom_toOrderHom]
    dsimp [τ]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hb]
    simp

end HolomorphicAnosov.SingularCochain
