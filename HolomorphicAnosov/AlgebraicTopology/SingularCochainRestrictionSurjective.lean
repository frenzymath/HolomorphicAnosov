import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Topology.Category.TopCat.EpiMono
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false
/-- Restriction of singular cochains to a subspace is surjective in every degree.
Source: Hatcher, *Algebraic Topology*, printed p.199 (relative cochains).
Proof: the inclusion identifies the subspace simplices with a subset of ambient
simplices. Assign the prescribed cochain value on this subset and zero elsewhere,
and extend using the chain module coproduct. Injectivity of simplex inclusion
makes this assignment agree with the original cochain upon restriction. -/
theorem singular_cochain_restriction_surjective (R : Type u) [CommRing R] (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    Function.Surjective ((pullback R (subspaceInclusion X A)).f n) := by
  classical
  let f := (TopCat.toSSet.map (subspaceInclusion X A)).app (op ⦋n⦌)
  have hinj : Function.Injective f := by
    have : Mono (subspaceInclusion X A) := (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    exact (CategoryTheory.mono_iff_injective f).mp inferInstance
  intro a
  let v := fun σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌) =>
    if h : ∃ τ, f τ = σ then
      (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex h.choose ≫ a
    else 0
  let b : cochains R X n := Sigma.desc v
  refine ⟨b, ?_⟩
  apply SSet.chainComplex_hom_ext
  intro τ
  change (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (subspaceInclusion X A)) (ModuleCat.of R R)).f n ≫ b = _
  rw [SSet.ι_chainComplexMap_f_assoc]
  change Sigma.ι _ (f τ) ≫ Sigma.desc v = _
  rw [Sigma.ι_comp_desc]
  dsimp only [v]
  rw [dite_eq_left ⟨τ, rfl⟩]
  exact congrArg (fun t => (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex t ≫ a)
    (hinj (Exists.choose_spec (⟨τ, rfl⟩ : ∃ t, f t = f τ)))
end HolomorphicAnosov.SingularCochain

