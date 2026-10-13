import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.ULift



noncomputable section

namespace HolomorphicAnosov

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

/-- The integral coefficient module.  -/
abbrev reducedSingularIntegralCoefficients : ModuleCat.{u} ℤ :=
  ModuleCat.of ℤ (ULift.{u} ℤ)

/-- The coefficient-sum augmentation of ordinary singular zero-chains.  -/
def integralSingularAugmentation (X : TopCat.{u}) :
    ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients).X 0 ⟶
      reducedSingularIntegralCoefficients :=
  Sigma.desc (fun _ ↦ 𝟙 reducedSingularIntegralCoefficients)

/-- The actual augmented integral singular complex.  -/
def augmentedIntegralSingularChains (X : TopCat.{u}) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  ChainComplex.augment
    ((TopCat.toSSet.obj X).chainComplex reducedSingularIntegralCoefficients)
    (integralSingularAugmentation X) (by
      apply SSet.chainComplex_hom_ext
      intro σ
      rw [← Category.assoc, SSet.ιChainComplex_d]
      simp [integralSingularAugmentation,
        SSet.ιChainComplex, Fin.sum_univ_two])

/-- The map of augmented integral singular complexes induced by a continuous map.  -/
def augmentedIntegralSingularChainsMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    augmentedIntegralSingularChains X ⟶ augmentedIntegralSingularChains Y :=
  ChainComplex.ofHom
    (fun n ↦ match n with
      | 0 => 𝟙 reducedSingularIntegralCoefficients
      | n + 1 =>
        (SSet.chainComplexMap (TopCat.toSSet.map f)
          reducedSingularIntegralCoefficients).f n)
    (fun n ↦ by
      cases n with
      | zero =>
        change (SSet.chainComplexMap (TopCat.toSSet.map f)
          reducedSingularIntegralCoefficients).f 0 ≫ integralSingularAugmentation Y =
          integralSingularAugmentation X ≫ 𝟙 _
        apply SSet.chainComplex_hom_ext
        intro σ
        rw [← Category.assoc, SSet.ι_chainComplexMap_f]
        simp [integralSingularAugmentation, SSet.ιChainComplex]
      | succ n =>
        exact (SSet.chainComplexMap (TopCat.toSSet.map f)
          reducedSingularIntegralCoefficients).comm (n + 1) n)

/-- The functor of actual augmented integral singular complexes.  -/
def augmentedIntegralSingularChainsFunctor :
    TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ where
  obj := augmentedIntegralSingularChains
  map := augmentedIntegralSingularChainsMap
  map_id X := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n <;> simp [augmentedIntegralSingularChainsMap, SSet.chainComplexMap] <;> rfl
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n <;> simp [augmentedIntegralSingularChainsMap, SSet.chainComplexMap] <;> rfl

/-- Reduced integral singular homology in nonnegative mathematical degree `n`, as a functor with values in integer modules (hence abelian groups).  -/
def integralReducedSingularHomologyFunctor (n : ℕ) : TopCat.{u} ⥤ ModuleCat.{u} ℤ :=
  augmentedIntegralSingularChainsFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) (n + 1)

/-- The reduced integral singular homology module of `X` in degree `n ≥ 0`. -/
abbrev integralReducedSingularHomology (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} ℤ :=
  (integralReducedSingularHomologyFunctor n).obj X

/-- The induced reduced homology map, for the original continuous map and integer module structures. -/
abbrev integralReducedSingularHomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralReducedSingularHomology X n ⟶ integralReducedSingularHomology Y n :=
  (integralReducedSingularHomologyFunctor n).map f

/-- The canonical concrete kernel/image quotient model of reduced integral homology.  -/
def integralReducedSingularHomologyQuotientIso (X : TopCat.{u}) (n : ℕ) :
    integralReducedSingularHomology X n ≅
      ((augmentedIntegralSingularChains X).sc (n + 1)).moduleCatLeftHomologyData.H :=
  ((augmentedIntegralSingularChains X).sc (n + 1)).moduleCatHomologyIso

/-- Mathematical degree −1 reduced integral homology, namely homology at augmented index zero, or the cokernel of the coefficient-sum augmentation.  -/
def integralReducedSingularHomologyMinusOneFunctor : TopCat.{u} ⥤ ModuleCat.{u} ℤ :=
  augmentedIntegralSingularChainsFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 0

/-- Reduced integral singular homology in every integer mathematical degree.  -/
def integralReducedSingularHomologyDegreeFunctor (k : ℤ) :
    TopCat.{u} ⥤ ModuleCat.{u} ℤ :=
  if -1 ≤ k then
    augmentedIntegralSingularChainsFunctor ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
        (k + 1).toNat
  else
    (Functor.const TopCat.{u}).obj (ModuleCat.of ℤ (ULift.{u} PUnit))

end HolomorphicAnosov
