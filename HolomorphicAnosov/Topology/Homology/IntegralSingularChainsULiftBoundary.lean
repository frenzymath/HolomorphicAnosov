import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift



open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov

private def intULiftEquiv {M : Type} [AddCommGroup M] [Module ℤ M] :
    ULift.{u} M ≃ₗ[ℤ] M where
  toFun := ULift.down
  invFun := ULift.up
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by
    intro a x
    change (a • x).down =
      (Module.toDistribMulAction (self := inferInstance) : DistribMulAction ℤ M).smul a x.down
    exact (ULift.smul_down x a).trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ M) a x.down).symm

/-- Every degreewise linear comparison with the canonical down-projected generator formula commutes with the singular boundary. -/
theorem singular_chains_ulift_integral_boundary (X : TopCat.{0}) :
    let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
    let idx := fun n : ℕ ↦
      (Y.toSSetObjEquiv (op ⦋n⦌)).trans
        ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
          (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans
            (X.toSSetObjEquiv (op ⦋n⦌)).symm)
    let CY := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of (ℤ) (ULift.{u} ℤ))
    let CX := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of (ℤ) (ℤ))
    ∀ e : ∀ n, CY.X n →ₗ[ℤ] CX.X n,
      (∀ n (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} ℤ),
        e n (((TopCat.toSSet.obj Y).ιChainComplex
          (R := ModuleCat.of (ℤ) (ULift.{u} ℤ)) σ) a) =
          ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of (ℤ) (ℤ)) (idx n σ)) a.down) →
      ∀ n (c : CY.X (n + 1)), e n (CY.d (n + 1) n c) = CX.d (n + 1) n (e (n + 1) c) := by
  classical
  dsimp only
  intro e he n
  let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
  let SY := TopCat.toSSet.obj Y
  let SX := TopCat.toSSet.obj X
  let CY := SY.chainComplex (ModuleCat.of (ℤ) (ULift.{u} ℤ))
  let CX := SX.chainComplex (ModuleCat.of (ℤ) (ℤ))
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
  let up : CX.X n →ₗ[ℤ] ULift.{u} (CX.X n) := intULiftEquiv.symm.toLinearMap
  let f : CY.X (n + 1) ⟶ ModuleCat.of (ℤ) (ULift.{u} (CX.X n)) :=
    ModuleCat.ofHom (up.comp ((e n).comp (CY.d (n + 1) n).hom))
  let g : CY.X (n + 1) ⟶ ModuleCat.of (ℤ) (ULift.{u} (CX.X n)) :=
    ModuleCat.ofHom (up.comp ((CX.d (n + 1) n).hom.comp (e (n + 1))))
  have hfg : f = g := by
    apply SY.chainComplex_hom_ext
    intro σ
    ext a
    change e n (CY.d (n + 1) n ((SY.ιChainComplex
      (R := ModuleCat.of (ℤ) (ULift.{u} ℤ)) σ) a)) =
      CX.d (n + 1) n (e (n + 1) ((SY.ιChainComplex
        (R := ModuleCat.of (ℤ) (ULift.{u} ℤ)) σ) a))
    have hdy := congrArg (fun k ↦ k.hom a) (SY.ιChainComplex_d
      (R := ModuleCat.of (ℤ) (ULift.{u} ℤ)) σ)
    have hdx := congrArg (fun k ↦ k.hom a.down) (SX.ιChainComplex_d
      (R := ModuleCat.of (ℤ) (ℤ)) (idx (n + 1) σ))
    simp only [CategoryTheory.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_smul,
      LinearMap.sum_apply, LinearMap.smul_apply] at hdy hdx
    rw [hdy, map_sum, he, hdx]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_zsmul]
    congr 1
    have hi := he n (SY.δ i σ) a
    change e n ((SY.ιChainComplex (R := ModuleCat.of (ℤ) (ULift.{u} ℤ))
      (SY.δ i σ)).hom a) =
      (SX.ιChainComplex (R := ModuleCat.of (ℤ) (ℤ)) (idx n (SY.δ i σ))).hom a.down at hi
    rw [hface] at hi
    exact hi
  intro c
  exact congrArg ULift.down (congrArg (fun k ↦ k.hom c) hfg)

end HolomorphicAnosov
