import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Universe comparison for native mod-two singular chains

Source: Hatcher, *Algebraic Topology*, §2.1 p.108, finite sums of singular
simplex generators. The universe and coefficient transport is the explicit
agent-written comparison recorded in `topo.singular_chains_ulift_modtwo_degree_comparison_g1`.
The theorem is degreewise; it makes no boundary or homology naturality assertion.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov

/-- The native mod-two singular chains of the universe-lifted space, with
universe-lifted mod-two coefficients, are linearly equivalent to the original
native chains in every degree. The equivalence sends every simplex generator
to its down-projected simplex and its down-projected mod-two coefficient.

Source: Hatcher, Algebraic Topology, §2.1 p.108, singular chains as finite sums
of simplex generators; explicit universe comparison for the torus Lefschetz
calculation. This is an agent-written expansion of that model identification.

Proof: In each universe use the native singular-chain colimit cofan and the
explicit finitely-supported-function colimit cofan. Their unique comparison
isomorphism sends each coproduct summand to the corresponding single function.
Use the actual singular-simplex continuous-map equivalences and postcompose by
the canonical up/down homeomorphism to identify the simplex index sets. Reindex
finitely supported functions by this equivalence and apply ULift.moduleEquiv
to each coefficient. Compose with the inverse small-universe colimit
comparison. The two cocone factorization equations and Finsupp.lcongr_single
prove the displayed generator formula. This uses separately constructed
coproducts in their own universes; it assumes no preservation of arbitrary
coproducts by ModuleCat.uliftFunctor. Empty spaces and degree zero are included.
-/
theorem singular_chains_ulift_modtwo_degree_comparison (X : TopCat.{0}) (n : ℕ) :
    let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
    let idx : (TopCat.toSSet.obj Y) _⦋n⦌ ≃ (TopCat.toSSet.obj X) _⦋n⦌ :=
      (Y.toSSetObjEquiv (op ⦋n⦌)).trans
        ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
          (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
            (X.toSSetObjEquiv (op ⦋n⦌)).symm)
    ∃ e : ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).X n ≃ₗ[ZMod 2]
        ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))).X n,
      ∀ (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} (ZMod 2)),
        e (((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a) =
          ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of (ZMod 2) (ZMod 2)) (idx σ)) a.down := by
  classical
  dsimp only
  let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
  let idx : (TopCat.toSSet.obj Y) _⦋n⦌ ≃ (TopCat.toSSet.obj X) _⦋n⦌ :=
    (Y.toSSetObjEquiv (op ⦋n⦌)).trans
      ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
        (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
          (X.toSSetObjEquiv (op ⦋n⦌)).symm)
  let cy := (TopCat.toSSet.obj Y).isColimitChainComplexXCofan
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) n
  let fy := ModuleCat.finsuppCoconeIsColimit (R := ZMod 2) (M := ULift.{u} (ZMod 2))
    ((TopCat.toSSet.obj Y) _⦋n⦌)
  let cx := (TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of (ZMod 2) (ZMod 2)) n
  let fx := ModuleCat.finsuppCoconeIsColimit (R := ZMod 2) (M := ZMod 2)
    ((TopCat.toSSet.obj X) _⦋n⦌)
  let ey := (cy.coconePointUniqueUpToIso fy).toLinearEquiv
  let ex := (cx.coconePointUniqueUpToIso fx).toLinearEquiv
  let reindex := Finsupp.lcongr idx (ULift.moduleEquiv : ULift.{u} (ZMod 2) ≃ₗ[ZMod 2] (ZMod 2))
  refine ⟨(ey.trans reindex).trans ex.symm, ?_⟩
  intro σ a
  have hy := congrArg (fun k ↦ k.hom a)
    (cy.comp_coconePointUniqueUpToIso_hom fy ⟨σ⟩)
  change ey (((TopCat.toSSet.obj Y).ιChainComplex
    (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a) = Finsupp.single σ a at hy
  have hx := congrArg (fun k ↦ k.hom a.down)
    (cx.comp_coconePointUniqueUpToIso_hom fx ⟨idx σ⟩)
  change ex (((TopCat.toSSet.obj X).ιChainComplex
    (R := ModuleCat.of (ZMod 2) (ZMod 2)) (idx σ)) a.down) = Finsupp.single (idx σ) a.down at hx
  change ex.symm (reindex (ey (((TopCat.toSSet.obj Y).ιChainComplex
    (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a))) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of (ZMod 2) (ZMod 2)) (idx σ)) a.down
  apply ex.symm_apply_eq.mpr
  rw [hy]
  exact (Finsupp.lcongr_single idx (ULift.moduleEquiv : ULift.{u} (ZMod 2) ≃ₗ[ZMod 2] (ZMod 2)) σ a).trans hx.symm

end HolomorphicAnosov
