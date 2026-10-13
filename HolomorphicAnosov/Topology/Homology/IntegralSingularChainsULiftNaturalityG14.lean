import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
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

/-- Generator-preserving integral singular-chain comparisons commute with the chain maps induced by a continuous map and its canonical universe lift. -/
theorem singular_chains_ulift_integral_naturality_g14 (X Z : TopCat.{0}) (f : C(X, Z)) (n : ℕ) :
    let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
    let W : TopCat.{u} := TopCat.of (ULift.{u} Z)
    let idxX := (Y.toSSetObjEquiv (op ⦋n⦌)).trans
      ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
        (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans (X.toSSetObjEquiv (op ⦋n⦌)).symm)
    let idxZ := (W.toSSetObjEquiv (op ⦋n⦌)).trans
      ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
        (Homeomorph.ulift : ULift.{u} Z ≃ₜ Z)).trans (Z.toSSetObjEquiv (op ⦋n⦌)).symm)
    let upf : C(Y, W) := ⟨fun x ↦ ULift.up (f x.down),
      (Homeomorph.ulift : ULift.{u} Z ≃ₜ Z).symm.continuous.comp
        (f.continuous.comp (Homeomorph.ulift : ULift.{u} X ≃ₜ X).continuous)⟩
    let CY := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
    let CW := (TopCat.toSSet.obj W).chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
    let CX := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)
    let CZ := (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of ℤ ℤ)
    ∀ (eX : CY.X n →ₗ[ℤ] CX.X n) (eZ : CW.X n →ₗ[ℤ] CZ.X n),
      (∀ (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} ℤ),
        eX (((TopCat.toSSet.obj Y).ιChainComplex
          (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) a) =
          ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (idxX σ)) a.down) →
      (∀ (σ : (TopCat.toSSet.obj W) _⦋n⦌) (a : ULift.{u} ℤ),
        eZ (((TopCat.toSSet.obj W).ιChainComplex
          (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) a) =
          ((TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of ℤ ℤ) (idxZ σ)) a.down) →
      ∀ c : CY.X n,
        eZ ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom upf))
          (ModuleCat.of ℤ (ULift.{u} ℤ))).f n c) =
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
          (ModuleCat.of ℤ ℤ)).f n (eX c) := by
  classical
  dsimp only
  intro eX eZ heX heZ
  let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
  let W : TopCat.{u} := TopCat.of (ULift.{u} Z)
  let SY := TopCat.toSSet.obj Y
  let SW := TopCat.toSSet.obj W
  let SX := TopCat.toSSet.obj X
  let SZ := TopCat.toSSet.obj Z
  let CY := SY.chainComplex (ModuleCat.of ℤ (ULift.{u} ℤ))
  let CZ := SZ.chainComplex (ModuleCat.of ℤ ℤ)
  let idxX := (Y.toSSetObjEquiv (op ⦋n⦌)).trans
    ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
      (Homeomorph.ulift : ULift.{u} X ≃ₜ X)).trans (X.toSSetObjEquiv (op ⦋n⦌)).symm)
  let idxZ := (W.toSSetObjEquiv (op ⦋n⦌)).trans
    ((Homeomorph.continuousMapCongr (Homeomorph.refl _)
      (Homeomorph.ulift : ULift.{u} Z ≃ₜ Z)).trans (Z.toSSetObjEquiv (op ⦋n⦌)).symm)
  let upf : C(Y, W) := ⟨fun x ↦ ULift.up (f x.down),
    (Homeomorph.ulift : ULift.{u} Z ≃ₜ Z).symm.continuous.comp
      (f.continuous.comp (Homeomorph.ulift : ULift.{u} X ≃ₜ X).continuous)⟩
  let F := TopCat.toSSet.map (TopCat.ofHom upf)
  let G := TopCat.toSSet.map (TopCat.ofHom f)
  let CF := SSet.chainComplexMap F (ModuleCat.of ℤ (ULift.{u} ℤ))
  let CG := SSet.chainComplexMap G (ModuleCat.of ℤ ℤ)
  have hidx (σ : SY _⦋n⦌) : idxZ (F.app (op ⦋n⦌) σ) = G.app (op ⦋n⦌) (idxX σ) := by
    apply (Z.toSSetObjEquiv (op ⦋n⦌)).injective
    ext z
    rfl
  let up : CZ.X n →ₗ[ℤ] ULift.{u} (CZ.X n) := intULiftEquiv.symm.toLinearMap
  let lhs : CY.X n ⟶ ModuleCat.of ℤ (ULift.{u} (CZ.X n)) :=
    ModuleCat.ofHom (up.comp (eZ.comp (CF.f n).hom))
  let rhs : CY.X n ⟶ ModuleCat.of ℤ (ULift.{u} (CZ.X n)) :=
    ModuleCat.ofHom (up.comp ((CG.f n).hom.comp eX))
  have heq : lhs = rhs := by
    apply SY.chainComplex_hom_ext
    intro σ
    ext a
    change eZ (CF.f n ((SY.ιChainComplex
      (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) a)) =
      CG.f n (eX ((SY.ιChainComplex (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ) a))
    have hy := congrArg (fun k ↦ k.hom a)
      (SSet.ι_chainComplexMap_f (X := SY) (Y := SW) (f := F)
        (R := ModuleCat.of ℤ (ULift.{u} ℤ)) σ)
    have hx := congrArg (fun k ↦ k.hom a.down)
      (SSet.ι_chainComplexMap_f (X := SX) (Y := SZ) (f := G)
        (R := ModuleCat.of ℤ ℤ) (idxX σ))
    simp only [CategoryTheory.comp_apply] at hy hx
    rw [hy, heZ, heX, hx]
    change (SZ.ιChainComplex (R := ModuleCat.of ℤ ℤ) (idxZ (F.app (op ⦋n⦌) σ))) a.down =
      (SZ.ιChainComplex (R := ModuleCat.of ℤ ℤ) (G.app (op ⦋n⦌) (idxX σ))) a.down
    rw [hidx]
  intro c
  exact congrArg ULift.down (congrArg (fun k ↦ k.hom c) heq)

end HolomorphicAnosov
