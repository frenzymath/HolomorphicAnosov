import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

/-- The augmented mod-two singular complex of a nonempty space has zero
homology in augmented index zero (reduced degree minus one).

Source: Hatcher, Algebraic Topology, pp.110,118,153. A constant zero-simplex
at any chosen point gives a right inverse to coefficient sum. The incoming
augmentation is therefore epic; the outgoing differential is zero, so the
index-zero cycle/boundary short complex is exact. Nonemptiness is essential. -/
theorem modTwoAugmentedDegreeZero (X : TopCat.{0}) [Nonempty X] :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let L := TopCat.toSSet.obj X
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    ∀ (w : K.d 1 0 ≫ ε = 0),
      IsZero ((ChainComplex.augment K ε w).homology 0) := by
  dsimp only
  intro w
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let L := TopCat.toSSet.obj X
  let K := L.chainComplex R0
  let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let A := ChainComplex.augment K ε w
  let σ : L _⦋0⦌ := (TopCat.toSSetObjEquiv X _).symm
    (ContinuousMap.const _ (Classical.choice (inferInstance : Nonempty X)))
  have hε : Epi ε := epi_of_epi_fac (show L.ιChainComplex (R := R0) σ ≫ ε = 𝟙 _ by
    simp [ε, SSet.ιChainComplex])
  apply (ShortComplex.exact_iff_isZero_homology _).mp
  apply (ShortComplex.exact_iff_epi _ (by
    change A.d 0 ((ComplexShape.down ℕ).next 0) = 0
    exact A.shape _ _ (by simp))).mpr
  change Epi (A.d ((ComplexShape.down ℕ).prev 0) 0)
  have hprev : (ComplexShape.down ℕ).prev 0 = 1 :=
    (ComplexShape.down ℕ).prev_eq' (by simp)
  rw [hprev]
  exact hε

end HolomorphicAnosov
