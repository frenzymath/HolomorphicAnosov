import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift

/-!
# Boundary compatibility of the rational singular-chain universe comparison

Source: Hatcher, *Algebraic Topology*, §2.1 p.108, the signed face formula for
singular boundaries. The universe transport is an agent-written expansion of
the native singular-chain model comparison in the torus Lefschetz calculation.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov

/-- Every degreewise linear comparison with the canonical down-projected generator
formula commutes with the singular boundary.

Source: Hatcher §2.1 p.108. The continuous-map identification of singular simplices
shows that down-projection commutes with each face restriction. Apply the signed
face formula to a simplex generator and use linearity of the comparison, which
preserves the integer signs. Equality on generators extends to all chains by
the coproduct universal property. For that last argument only, lift the small
output module to the large universe and then cancel the injective coefficient
lift. No preservation of coproducts by a universe-lift functor is assumed.
Empty spaces, degree zero as the target of the first boundary, and arbitrary
universe lifts are included. The statement does not assume boundary compatibility.
-/
theorem singular_chains_ulift_boundary (X : TopCat.{0}) :
    let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
    let idx := fun n : ℕ ↦
      (Y.toSSetObjEquiv (op ⦋n⦌)).trans
        ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
          (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
            (X.toSSetObjEquiv (op ⦋n⦌)).symm)
    let CY := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ (ULift.{u} ℚ))
    let CX := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)
    ∀ e : ∀ n, CY.X n →ₗ[ℚ] CX.X n,
      (∀ n (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} ℚ),
        e n (((TopCat.toSSet.obj Y).ιChainComplex
          (R := ModuleCat.of ℚ (ULift.{u} ℚ)) σ) a) =
          ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℚ ℚ) (idx n σ)) a.down) →
      ∀ n (c : CY.X (n + 1)), e n (CY.d (n + 1) n c) = CX.d (n + 1) n (e (n + 1) c) := by
  classical
  dsimp only
  intro e he n
  let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
  let SY := TopCat.toSSet.obj Y
  let SX := TopCat.toSSet.obj X
  let CY := SY.chainComplex (ModuleCat.of ℚ (ULift.{u} ℚ))
  let CX := SX.chainComplex (ModuleCat.of ℚ ℚ)
  let idx := fun k : ℕ ↦
    (Y.toSSetObjEquiv (op ⦋k⦌)).trans
      ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
        (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
          (X.toSSetObjEquiv (op ⦋k⦌)).symm)
  have hface (σ : SY _⦋n + 1⦌) (i : Fin (n + 2)) :
      idx n (SY.δ i σ) = SX.δ i (idx (n + 1) σ) := by
    apply (X.toSSetObjEquiv (op ⦋n⦌)).injective
    ext z
    simp [idx, SY, SX, Y, TopCat.toSSetObjEquiv_δ_apply]
    rfl
  let up : CX.X n →ₗ[ℚ] ULift.{u} (CX.X n) := ULift.moduleEquiv.symm.toLinearMap
  let f : CY.X (n + 1) ⟶ ModuleCat.of ℚ (ULift.{u} (CX.X n)) :=
    ModuleCat.ofHom (up.comp ((e n).comp (CY.d (n + 1) n).hom))
  let g : CY.X (n + 1) ⟶ ModuleCat.of ℚ (ULift.{u} (CX.X n)) :=
    ModuleCat.ofHom (up.comp ((CX.d (n + 1) n).hom.comp (e (n + 1))))
  have hfg : f = g := by
    apply SY.chainComplex_hom_ext
    intro σ
    ext a
    change e n (CY.d (n + 1) n ((SY.ιChainComplex
      (R := ModuleCat.of ℚ (ULift.{u} ℚ)) σ) a)) =
      CX.d (n + 1) n (e (n + 1) ((SY.ιChainComplex
        (R := ModuleCat.of ℚ (ULift.{u} ℚ)) σ) a))
    have hdy := congrArg (fun k ↦ k.hom a) (SY.ιChainComplex_d
      (R := ModuleCat.of ℚ (ULift.{u} ℚ)) σ)
    have hdx := congrArg (fun k ↦ k.hom a.down) (SX.ιChainComplex_d
      (R := ModuleCat.of ℚ ℚ) (idx (n + 1) σ))
    simp only [CategoryTheory.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_smul,
      LinearMap.sum_apply, LinearMap.smul_apply] at hdy hdx
    rw [hdy, map_sum, he, hdx]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_zsmul]
    congr 1
    have hi := he n (SY.δ i σ) a
    change e n ((SY.ιChainComplex (R := ModuleCat.of ℚ (ULift.{u} ℚ))
      (SY.δ i σ)).hom a) =
      (SX.ιChainComplex (R := ModuleCat.of ℚ ℚ) (idx n (SY.δ i σ))).hom a.down at hi
    rw [hface] at hi
    exact hi
  intro c
  exact congrArg ULift.down (congrArg (fun k ↦ k.hom c) hfg)

end HolomorphicAnosov
