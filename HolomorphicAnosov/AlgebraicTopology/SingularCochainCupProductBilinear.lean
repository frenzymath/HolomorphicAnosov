import HolomorphicAnosov.AlgebraicTopology.SingularCochainCupProductDefinition

/-!
# Bilinearity of the singular cup cochain

Source: Hatcher, *Algebraic Topology*, pp.206–207, the front/back formula
and its distributivity. Scalar linearity follows from the same formula.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain

set_option backward.isDefEq.respectTransparency false in
/-- The actual front/back cup formula is bilinear on singular cochains.

Source: Hatcher, *Algebraic Topology*, pp.206–207. On each free singular
generator the formula is the product of the front and back evaluations.
Evaluation is linear, so distributivity proves additivity in each factor,
and commutativity of the coefficient ring allows a scalar to be taken outside
either factor. Equality on generators proves all four linear-map identities.
No cocycle, topological, or nonzero-ring assumption is needed.
-/
theorem cupCochain_bilinear (R : Type u) [CommRing R]
    (X : TopCat.{u}) (p q : ℕ) :
    ∃ μ : cochains R X p →ₗ[R] cochains R X q →ₗ[R] cochains R X (p + q),
      ∀ a b, μ a b = cupCochain R X a b := by
  refine ⟨{
    toFun := fun a ↦ {
      toFun := fun b ↦ cupCochain R X a b
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }, fun _ _ ↦ rfl⟩
  · rename_i a
    intro b c
    dsimp [cochains, complex, cochainFunctor, dualFunctor, CategoryTheory.linearYoneda] at *
    apply SSet.chainComplex_hom_ext
    intro σ
    simp only [cupCochain, SSet.ιChainComplex, Sigma.ι_comp_desc,
      Preadditive.comp_add]
    apply ModuleCat.hom_ext
    ext
    simp [simplexValue, ModuleCat.hom_add, SSet.ιChainComplex, mul_add]
  · rename_i a
    intro r b
    dsimp [cochains, complex, cochainFunctor, dualFunctor, CategoryTheory.linearYoneda] at *
    apply SSet.chainComplex_hom_ext
    intro σ
    simp only [cupCochain, SSet.ιChainComplex, Sigma.ι_comp_desc,
      Linear.comp_smul]
    apply ModuleCat.hom_ext
    ext
    simp [simplexValue, ModuleCat.hom_smul, SSet.ιChainComplex,
      mul_left_comm, mul_comm]
  · intro a b
    ext c
    change cupCochain R X (a + b) c = cupCochain R X a c + cupCochain R X b c
    dsimp [cochains, complex, cochainFunctor, dualFunctor, CategoryTheory.linearYoneda] at *
    apply SSet.chainComplex_hom_ext
    intro σ
    simp only [cupCochain, SSet.ιChainComplex, Sigma.ι_comp_desc,
      Preadditive.comp_add]
    apply ModuleCat.hom_ext
    ext
    simp [simplexValue, ModuleCat.hom_add, SSet.ιChainComplex, add_mul]
  · intro r a
    ext b
    change cupCochain R X (r • a) b = r • cupCochain R X a b
    dsimp [cochains, complex, cochainFunctor, dualFunctor, CategoryTheory.linearYoneda] at *
    apply SSet.chainComplex_hom_ext
    intro σ
    simp only [cupCochain, SSet.ιChainComplex, Sigma.ι_comp_desc,
      Linear.comp_smul]
    apply ModuleCat.hom_ext
    ext
    simp [simplexValue, ModuleCat.hom_smul, SSet.ιChainComplex,
      mul_assoc, mul_comm]

end HolomorphicAnosov.SingularCochain
