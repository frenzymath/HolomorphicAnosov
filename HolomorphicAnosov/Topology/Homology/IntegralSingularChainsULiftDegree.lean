import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Finsupp.LSum



open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov

/-- The native integral singular chains of the universe-lifted space, with universe-lifted integral coefficients, are linearly equivalent to the original native chains in every degree.  -/
theorem singular_chains_ulift_integral_degree_comparison (X : TopCat.{0}) (n : ℕ) :
    let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
    let idx : (TopCat.toSSet.obj Y) _⦋n⦌ ≃ (TopCat.toSSet.obj X) _⦋n⦌ :=
      (Y.toSSetObjEquiv (op ⦋n⦌)).trans
        ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
          (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
            (X.toSSetObjEquiv (op ⦋n⦌)).symm)
    ∃ e : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of (ℤ) (ULift.{u} ℤ))).X n ≃ₗ[ℤ]
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of (ℤ) (ℤ))).X n,
      ∀ (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} ℤ),
        e (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of (ℤ) (ULift.{u} ℤ)) σ) a) =
          ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of (ℤ) (ℤ)) (idx σ)) a.down := by
  classical
  dsimp only
  let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
  let idx : (TopCat.toSSet.obj Y) _⦋n⦌ ≃ (TopCat.toSSet.obj X) _⦋n⦌ :=
    (Y.toSSetObjEquiv (op ⦋n⦌)).trans
      ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
        (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
          (X.toSSetObjEquiv (op ⦋n⦌)).symm)
  let cy := (TopCat.toSSet.obj Y).isColimitChainComplexXCofan
    (ModuleCat.of (ℤ) (ULift.{u} ℤ)) n
  let fy := ModuleCat.finsuppCoconeIsColimit (R := ℤ) (M := ULift.{u} ℤ)
    ((TopCat.toSSet.obj Y) _⦋n⦌)
  let cx := (TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of (ℤ) (ℤ)) n
  let fx := ModuleCat.finsuppCoconeIsColimit (R := ℤ) (M := ℤ)
    ((TopCat.toSSet.obj X) _⦋n⦌)
  let ey := (cy.coconePointUniqueUpToIso fy).toLinearEquiv
  let ex := (cx.coconePointUniqueUpToIso fx).toLinearEquiv
  let reindex := Finsupp.lcongr idx (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] (ℤ))
  refine ⟨(ey.trans reindex).trans ex.symm, ?_⟩
  intro σ a
  have hy := congrArg (fun k ↦ k.hom a)
    (cy.comp_coconePointUniqueUpToIso_hom fy ⟨σ⟩)
  change ey (((TopCat.toSSet.obj Y).ιChainComplex
    (R := ModuleCat.of (ℤ) (ULift.{u} ℤ)) σ) a) = Finsupp.single σ a at hy
  have hx := congrArg (fun k ↦ k.hom a.down)
    (cx.comp_coconePointUniqueUpToIso_hom fx ⟨idx σ⟩)
  change ex (((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of (ℤ) (ℤ)) (idx σ)) a.down) = Finsupp.single (idx σ) a.down at hx
  change ex.symm (reindex (ey (((TopCat.toSSet.obj Y).ιChainComplex
    (R := ModuleCat.of (ℤ) (ULift.{u} ℤ)) σ) a))) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of (ℤ) (ℤ)) (idx σ)) a.down
  apply ex.symm_apply_eq.mpr
  rw [hy]
  exact (Finsupp.lcongr_single idx (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] (ℤ)) σ a).trans hx.symm

end HolomorphicAnosov
