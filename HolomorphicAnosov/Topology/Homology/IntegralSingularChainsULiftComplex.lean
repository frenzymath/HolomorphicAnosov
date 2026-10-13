import HolomorphicAnosov.Topology.Homology.IntegralSingularChainsULiftDegree
import HolomorphicAnosov.Topology.Homology.IntegralSingularChainsULiftBoundary
import Mathlib.Algebra.Category.ModuleCat.Ulift


noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
namespace HolomorphicAnosov
universe u

/-- The degreewise canonical ULift comparison is an isomorphism of chain complexes. -/
theorem singular_chains_ulift_integral_complex_comparison (X : TopCat.{0}) :
    let Y := TopCat.of (ULift.{u} X)
    let C := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)
    let D := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
    let F := ModuleCat.uliftFunctor.{u, 0} ℤ
    let idx (n : ℕ) := (Y.toSSetObjEquiv (op ⦋n⦌)).trans
      ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
        (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
          (X.toSSetObjEquiv (op ⦋n⦌)).symm)
    ∃ e : D ≅ (F.mapHomologicalComplex (.down ℕ)).obj C,
      ∀ n (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} ℤ),
        ((e.hom.f n) (((TopCat.toSSet.obj Y).ιChainComplex
          (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) a)).down =
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (idx n σ)) a.down := by
  classical
  dsimp only
  let Y := TopCat.of (ULift.{u} X)
  let C := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)
  let D := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
  let F := ModuleCat.uliftFunctor.{u, 0} ℤ
  let FC := (F.mapHomologicalComplex (.down ℕ)).obj C
  choose e he using (fun n ↦ singular_chains_ulift_integral_degree_comparison.{u} X n)
  have hd := singular_chains_ulift_integral_boundary.{u} X
    (fun n ↦ (e n).toLinearMap) he
  let ei (n : ℕ) : D.X n ≅ FC.X n :=
    ((e n).trans (ULift.moduleEquiv.symm : C.X n ≃ₗ[ℤ] FC.X n)).toModuleIso
  have hc : ∀ i j, (ComplexShape.down ℕ).Rel i j →
      (ei i).hom ≫ FC.d i j = D.d i j ≫ (ei j).hom := by
    intro i j hij
    have hij' : j + 1 = i := hij
    subst i
    ext z
    exact congrArg ULift.up (hd j z).symm
  refine ⟨HomologicalComplex.Hom.isoOfComponents ei hc, ?_⟩
  intro n σ a
  exact he n σ a
end HolomorphicAnosov
