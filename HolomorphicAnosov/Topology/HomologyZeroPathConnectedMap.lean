import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace HolomorphicAnosov

/-- Hatcher, Proposition 2.7 p.109: a map from a nonempty space to a
path-connected space surjects on ordinary H₀. Choose a source vertex. Its
image class generates target H₀ via the inverse augmentation. Thus the
composite coefficient-to-source-to-target map is onto, forcing the homology
map itself onto. -/
theorem singular_homology_zero_map_epi_of_pathConnected
    {A : Type u} [Ring A] {X Y : TopCat.{u}}
    [Nonempty X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (R : ModuleCat.{u} A) :
    Epi (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} A) 0).obj R).map f) := by
  classical
  have hY : IsIso (Y.singularHomology₀ε (C := ModuleCat.{u} A) R) := inferInstance
  let K := (TopCat.toSSet.obj X).chainComplex R
  let x : X := Classical.arbitrary X
  let σ : (TopCat.toSSet.obj X) _⦋0⦌ :=
    (TopCat.toSSetObjEquiv X _).symm (ContinuousMap.const _ x)
  let i : R ⟶ K.homology 0 :=
    K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex σ) 0 (by simp) (by simp) ≫ K.homologyπ 0
  let h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} A) 0).obj R).map f
  have he : i ≫ h ≫ Y.singularHomology₀ε (C := ModuleCat.{u} A) R = 𝟙 R := by
    change K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex σ) 0 _ _ ≫
      K.homologyπ 0 ≫ HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) R) 0 ≫
          (TopCat.toSSet.obj Y).homology₀ε R = 𝟙 R
    rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap, SSet.ι_chainComplexMap_f]
    exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ R _
  have : Epi (i ≫ h ≫ Y.singularHomology₀ε (C := ModuleCat.{u} A) R) := by
    rw [he]; infer_instance
  have : Epi (h ≫ Y.singularHomology₀ε (C := ModuleCat.{u} A) R) := epi_of_epi i _
  exact (epi_comp_iff_of_isIso _ _).mp this

/-- Hatcher, Algebraic Topology, Proposition 2.7 p.109: every continuous map
between nonempty path-connected spaces induces an isomorphism on ordinary H₀
with any module of coefficients. Choose a vertex of the source. Its class map
from the coefficient module is inverse to augmentation, since the source is
path-connected. Naturality sends this class to the image vertex class in the
target; that class map is likewise inverse to target augmentation. The given
homology map is therefore a composite of these two isomorphisms. -/
theorem singular_homology_zero_map_isIso_of_pathConnected
    {A : Type u} [Ring A] {X Y : TopCat.{u}}
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : X ⟶ Y) (R : ModuleCat.{u} A) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} A) 0).obj R).map f) := by
  classical
  have hX : IsIso (X.singularHomology₀ε (C := ModuleCat.{u} A) R) := inferInstance
  have hY : IsIso (Y.singularHomology₀ε (C := ModuleCat.{u} A) R) := inferInstance
  let K := (TopCat.toSSet.obj X).chainComplex R
  let L := (TopCat.toSSet.obj Y).chainComplex R
  let x : X := Classical.arbitrary X
  let σ : (TopCat.toSSet.obj X) _⦋0⦌ := (TopCat.toSSetObjEquiv X _).symm (ContinuousMap.const _ x)
  let i : R ⟶ K.homology 0 :=
    K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex σ) 0 (by simp) (by simp) ≫ K.homologyπ 0
  have hi : i ≫ X.singularHomology₀ε (C := ModuleCat.{u} A) R = 𝟙 R := by
    exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ R σ
  have hiIso : IsIso i := by
    have : IsIso (i ≫ X.singularHomology₀ε (C := ModuleCat.{u} A) R) := by rw [hi]; infer_instance
    exact IsIso.of_isIso_comp_right i (X.singularHomology₀ε (C := ModuleCat.{u} A) R)
  let h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} A) 0).obj R).map f
  have he : i ≫ h ≫ Y.singularHomology₀ε (C := ModuleCat.{u} A) R = 𝟙 R := by
    change K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex σ) 0 _ _ ≫
      K.homologyπ 0 ≫ HomologicalComplex.homologyMap
        (SSet.chainComplexMap (TopCat.toSSet.map f) R) 0 ≫
          (TopCat.toSSet.obj Y).homology₀ε R = 𝟙 R
    rw [HomologicalComplex.homologyπ_naturality_assoc, ← Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap, SSet.ι_chainComplexMap_f]
    exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ R _
  have : IsIso (i ≫ h ≫ Y.singularHomology₀ε (C := ModuleCat.{u} A) R) := by rw [he]; infer_instance
  have : IsIso (h ≫ Y.singularHomology₀ε (C := ModuleCat.{u} A) R) := IsIso.of_isIso_comp_left i _
  exact IsIso.of_isIso_comp_right h (Y.singularHomology₀ε (C := ModuleCat.{u} A) R)

end HolomorphicAnosov

