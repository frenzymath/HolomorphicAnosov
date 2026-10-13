import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- A homeomorphism preserves homology of the literal augmented mod-two
singular complex, in every augmented degree including zero.

Source: Hatcher, Algebraic Topology, functoriality pp.110–111 and coefficients
p.153. The ordinary singular-chain isomorphism induced by the homeomorphism
extends by identity on the augmentation coefficient object. Its augmentation
square commutes because postcomposition preserves the coefficient sum on each
zero-simplex generator; all other squares are the ordinary chain squares.
This is an isomorphism of augmented complexes and thus induces the stated
homology isomorphism, for arbitrary boundary-zero witnesses. Empty spaces
are included, with identity on their added coefficient objects. -/
theorem modTwoAugmentedHomeomorphIso {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let LX := TopCat.toSSet.obj (TopCat.of X)
    let LY := TopCat.toSSet.obj (TopCat.of Y)
    let KX := LX.chainComplex R0
    let KY := LY.chainComplex R0
    let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ : LX _⦋0⦌ ↦ 𝟙 R0)
    let εY : KY.X 0 ⟶ R0 := Sigma.desc (fun _ : LY _⦋0⦌ ↦ 𝟙 R0)
    ∀ (wX : KX.d 1 0 ≫ εX = 0) (wY : KY.d 1 0 ≫ εY = 0) (q : ℕ),
      Nonempty ((ChainComplex.augment KX εX wX).homology q ≅
        (ChainComplex.augment KY εY wY).homology q) := by
  dsimp only
  intro wX wY q
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let LX := TopCat.toSSet.obj (TopCat.of X)
  let LY := TopCat.toSSet.obj (TopCat.of Y)
  let KX := LX.chainComplex R0
  let KY := LY.chainComplex R0
  let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let εY : KY.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let RX := ChainComplex.augment KX εX wX
  let RY := ChainComplex.augment KY εY wY
  let f : KX ≅ KY := ((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).obj R0).mapIso
    (TopCat.toSSet.mapIso (TopCat.isoOfHomeo e))
  let g : ∀ n, RX.X n ≅ RY.X n := fun n ↦ match n with
    | 0 => Iso.refl R0
    | n + 1 => HomologicalComplex.Hom.isoApp f n
  have hg : ∀ i j, (ComplexShape.down ℕ).Rel i j →
      (g i).hom ≫ RY.d i j = RX.d i j ≫ (g j).hom := by
    intro i j hij
    have hi : i = j + 1 := hij.symm
    subst i
    cases j with
    | zero =>
      change (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.isoOfHomeo e).hom) R0).f 0 ≫
        εY = εX ≫ 𝟙 R0
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [← Category.assoc, SSet.ι_chainComplexMap_f]
      simp only [εX, εY, SSet.ιChainComplex, Category.comp_id, Sigma.ι_comp_desc]
    | succ j => exact f.hom.comm (j + 1) j
  exact ⟨HomologicalComplex.homologyMapIso (HomologicalComplex.Hom.isoOfComponents g hg) q⟩

end HolomorphicAnosov
