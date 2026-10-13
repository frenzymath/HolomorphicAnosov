import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import HolomorphicAnosov.Topology.Homology.ModTwoSingularChainsULiftDegree

/-!
# Naturality of the mod-two singular-chain universe comparison

Source: Hatcher, *Algebraic Topology*, §2.1 pp.111–112, the chain map induced
by postcomposition of singular simplices. The universe and coefficient
identification is an agent-written expansion for the torus Lefschetz calculation.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
noncomputable section
namespace HolomorphicAnosov

/-- Generator-preserving mod-two singular-chain comparisons commute with the chain
maps induced by a continuous map and its canonical universe lift.

Source: Hatcher §2.1 pp.111–112. A lifted simplex followed by the lifted continuous
map and then down-projected equals its down-projection followed by the original
continuous map, by evaluation on every point of the standard simplex. The native
chain-map formula on summand inclusions therefore makes the comparison square
commute on every simplex generator and coefficient. Lift the small target module
into the larger universe, apply coproduct uniqueness there, and cancel this lift.
No invertibility, nonempty-space, or positive-degree assumption is used. The two
linear comparisons need only satisfy their generator formulas; their existence
and bijectivity are supplied separately by the degree-comparison theorem.
-/
theorem singular_chains_ulift_modtwo_naturality (X Z : TopCat.{0}) (f : C(X, Z)) (n : ℕ) :
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
    let CY := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
    let CW := (TopCat.toSSet.obj W).chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
    let CX := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))
    let CZ := (TopCat.toSSet.obj Z).chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))
    ∀ (eX : CY.X n →ₗ[(ZMod 2)] CX.X n) (eZ : CW.X n →ₗ[(ZMod 2)] CZ.X n),
      (∀ (σ : (TopCat.toSSet.obj Y) _⦋n⦌) (a : ULift.{u} (ZMod 2)),
        eX (((TopCat.toSSet.obj Y).ιChainComplex
          (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a) =
          ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of (ZMod 2) (ZMod 2)) (idxX σ)) a.down) →
      (∀ (σ : (TopCat.toSSet.obj W) _⦋n⦌) (a : ULift.{u} (ZMod 2)),
        eZ (((TopCat.toSSet.obj W).ιChainComplex
          (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a) =
          ((TopCat.toSSet.obj Z).ιChainComplex (R := ModuleCat.of (ZMod 2) (ZMod 2)) (idxZ σ)) a.down) →
      ∀ c : CY.X n,
        eZ ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom upf))
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).f n c) =
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
          (ModuleCat.of (ZMod 2) (ZMod 2))).f n (eX c) := by
  classical
  dsimp only
  intro eX eZ heX heZ
  let Y : TopCat.{u} := TopCat.of (ULift.{u} X)
  let W : TopCat.{u} := TopCat.of (ULift.{u} Z)
  let SY := TopCat.toSSet.obj Y
  let SW := TopCat.toSSet.obj W
  let SX := TopCat.toSSet.obj X
  let SZ := TopCat.toSSet.obj Z
  let CY := SY.chainComplex (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
  let CZ := SZ.chainComplex (ModuleCat.of (ZMod 2) (ZMod 2))
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
  let CF := SSet.chainComplexMap F (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
  let CG := SSet.chainComplexMap G (ModuleCat.of (ZMod 2) (ZMod 2))
  have hidx (σ : SY _⦋n⦌) : idxZ (F.app (op ⦋n⦌) σ) = G.app (op ⦋n⦌) (idxX σ) := by
    apply (Z.toSSetObjEquiv (op ⦋n⦌)).injective
    ext z
    rfl
  let up : CZ.X n →ₗ[(ZMod 2)] ULift.{u} (CZ.X n) := ULift.moduleEquiv.symm.toLinearMap
  let lhs : CY.X n ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (CZ.X n)) :=
    ModuleCat.ofHom (up.comp (eZ.comp (CF.f n).hom))
  let rhs : CY.X n ⟶ ModuleCat.of (ZMod 2) (ULift.{u} (CZ.X n)) :=
    ModuleCat.ofHom (up.comp ((CG.f n).hom.comp eX))
  have heq : lhs = rhs := by
    apply SY.chainComplex_hom_ext
    intro σ
    ext a
    change eZ (CF.f n ((SY.ιChainComplex
      (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a)) =
      CG.f n (eX ((SY.ιChainComplex (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ) a))
    have hy := congrArg (fun k ↦ k.hom a)
      (SSet.ι_chainComplexMap_f (X := SY) (Y := SW) (f := F)
        (R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) σ)
    have hx := congrArg (fun k ↦ k.hom a.down)
      (SSet.ι_chainComplexMap_f (X := SX) (Y := SZ) (f := G)
        (R := ModuleCat.of (ZMod 2) (ZMod 2)) (idxX σ))
    simp only [CategoryTheory.comp_apply] at hy hx
    rw [hy, heZ, heX, hx]
    change (SZ.ιChainComplex (R := ModuleCat.of (ZMod 2) (ZMod 2)) (idxZ (F.app (op ⦋n⦌) σ))) a.down =
      (SZ.ιChainComplex (R := ModuleCat.of (ZMod 2) (ZMod 2)) (G.app (op ⦋n⦌) (idxX σ))) a.down
    rw [hidx]
  intro c
  exact congrArg ULift.down (congrArg (fun k ↦ k.hom c) heq)

end HolomorphicAnosov
