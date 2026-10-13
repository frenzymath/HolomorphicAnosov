import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

/-!
Public reusable helper extracted from `HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus`.
Source: Ghys, *Holomorphic Anosov systems* (1995), proof of Theorem B, p.598;
expanded with the cited Hatcher results recorded in the parent module.
-/

namespace HolomorphicAnosov

universe u v

open CategoryTheory in
/-- Hatcher 2.10–2.11: actual continuous inverse homotopies induce inverse
maps on the native singular homology objects with the same coefficient object. -/
noncomputable def homotopyEquiv_mod2_homology_iso
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (k : ℕ) :
    (TopCat.toSSet.obj (TopCat.of X)).homology
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k ≅
      (TopCat.toSSet.obj (TopCat.of Y)).homology
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k := by
  let R : ModuleCat.{u} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} (ZMod 2)) k).obj R
  change F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y)
  refine ⟨F.map (TopCat.ofHom e.toFun), F.map (TopCat.ofHom e.invFun), ?_, ?_⟩
  · rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (g := 𝟙 (TopCat.of X))
      e.left_inv.some R k
  · rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (g := 𝟙 (TopCat.of Y))
      e.right_inv.some R k

end HolomorphicAnosov
