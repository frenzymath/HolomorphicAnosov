import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

/-! Hatcher pp.109–110,153: the two-point reduced degree-zero computation,
expressed as the kernel of the literal singular coefficient-sum augmentation.
-/
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov
noncomputable section

/-- The coefficient-sum kernel of the actual singular zero-chains of the discrete
two-point space is the fixed mod-two coefficient object.

Source: Hatcher, Algebraic Topology, Propositions 2.6–2.8 pp.109–110 and the
coefficient extension p.153. Singular zero-simplices correspond to the two
points. Their coefficient coproduct is the pair module, and coefficient sum
becomes (a,b)↦a+b. Its kernel consists exactly of pairs (a,-a); first projection
and a↦(a,-a) are inverse linear maps. Transport this kernel isomorphism through
the two actual zero-chain coordinate changes.
The explicit categorical kernel construction is agent-written, filling the
two-point base-case algebra omitted from the sphere profile in Hatcher p.153. -/
theorem modTwoTwoPointAugmentationKernel :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let L := TopCat.toSSet.obj (TopCat.of Bool)
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    Nonempty (kernel ε ≅ R0) := by
  dsimp only
  let R : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let X := TopCat.of Bool
  let ε : ((TopCat.toSSet.obj X).chainComplex R).X 0 ⟶ R :=
    Sigma.desc (fun _ ↦ 𝟙 R)
  let e0 : ((TopCat.toSSet.obj X).chainComplex R).X 0 ≅ ∐ fun _ : Bool ↦ R :=
    (sigmaConst.obj R).mapIso
      ((TopCat.toSSetIsoConst X).app (Opposite.op (SimplexCategory.mk 0)))
  have he0 : e0.hom ≫ Sigma.desc (fun _ : Bool ↦ 𝟙 R) = ε := by
    apply SSet.chainComplex_hom_ext
    intro σ
    simp [e0, sigmaConst, SSet.ιChainComplex, ε]
  let ep : (∐ fun _ : Bool ↦ R) ≅ ModuleCat.of (ZMod 2) (R × R) :=
    { hom := Sigma.desc (fun b ↦ ModuleCat.ofHom
        (if b then LinearMap.inr (ZMod 2) R R else LinearMap.inl (ZMod 2) R R))
      inv := ModuleCat.ofHom
        (((Sigma.ι (fun _ : Bool ↦ R) false).hom).comp (LinearMap.fst (ZMod 2) R R) +
          ((Sigma.ι (fun _ : Bool ↦ R) true).hom).comp (LinearMap.snd (ZMod 2) R R))
      hom_inv_id := by
        apply Sigma.hom_ext
        intro b
        cases b <;> ext x <;> simp
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        rintro ⟨a, b⟩
        simp }
  let l : R × R →ₗ[ZMod 2] R := LinearMap.fst (ZMod 2) R R + LinearMap.snd (ZMod 2) R R
  have hep : ep.hom ≫ ModuleCat.ofHom l = Sigma.desc (fun _ : Bool ↦ 𝟙 R) := by
    apply Sigma.hom_ext
    intro b
    cases b <;> ext x <;> simp [ep, l]
  let ek : l.ker ≃ₗ[ZMod 2] R :=
    { toFun := fun x ↦ x.val.1
      invFun := fun a ↦ ⟨(a, -a), by simp [l]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have h : x.val.1 + x.val.2 = 0 := x.property
          exact neg_eq_of_add_eq_zero_right h
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact ⟨kernel.mapIso _ _ e0 (Iso.refl _) (by simpa using he0.symm) ≪≫
    kernel.mapIso _ _ ep (Iso.refl _) (by simpa using hep.symm) ≪≫
      ModuleCat.kernelIsoKer (ModuleCat.ofHom l) ≪≫ ek.toModuleIso⟩

end
end HolomorphicAnosov
