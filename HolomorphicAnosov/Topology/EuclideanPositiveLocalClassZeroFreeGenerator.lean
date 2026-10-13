import HolomorphicAnosov.Topology.EuclideanPositiveLocalClass
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.ULift

/-!
# The coefficient-one Euclidean local class in dimension zero

Source: Hatcher, *Algebraic Topology*, Propositions 2.7–2.8 pp.109–110,
and relative quotient chains p.115. DAG node:
`topo.euclidean_positive_local_class_zero_free_generator_g15`.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- Integer multiples of the prescribed positive point class biject with
ordinary integral local homology of zero-dimensional Euclidean space.

Source: Hatcher, Propositions 2.7–2.8 pp.109–110 and relative chains p.115.
The ambient space is a point and its punctured subspace is empty. Evaluating
any hypothetical singular zero-simplex in that subspace at a vertex gives
a contradiction. Thus the native relative chain projection is an isomorphism.
The ordinary H₀ augmentation is an isomorphism and sends the coefficient-one
point simplex class to one. Consequently its class map from the lifted integer
coefficient module is the inverse augmentation. Compose it with the homology
isomorphism of the relative projection. Naturality of cycle lifts and homology
projection identifies its value at one with the exact quotient-based
`euclideanPositiveLocalClass 0`. Composing with the integer universe-lift
linear equivalence gives the displayed scalar-multiplication map, hence
bijectivity. No reduced degree-zero homology or chosen generator is used. -/
theorem euclideanPositiveLocalClass_zero_free_generator : Function.Bijective
    (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveLocalClass 0)) := by
  let X := TopCat.of (EuclideanSpace ℝ (Fin 0))
  let A : Set X := ({0} : Set _)ᶜ
  let P := singularSubspacePair X A
  let R := reducedSingularIntegralCoefficients
  let K := (TopCat.toSSet.obj X).chainComplex R
  let L := P.chainComplex R
  have : IsEmpty A := ⟨fun a ↦ a.property (Subsingleton.elim a.val 0)⟩
  have : IsIso (P.chainComplexπ R) := by
    have : P.left.HasDimensionLT 0 := by
      apply (SSet.notNonempty_iff_hasDimensionLT_zero _).mp
      rintro ⟨τ⟩
      exact isEmptyElim (((TopCat.of A).toSSetObjEquiv _ τ)
        (Convexity.StdSimplex.single 0))
    infer_instance
  let σ := (X.toSSetObjEquiv (op ⦋0⦌)).symm (euclideanPositiveSimplex 0)
  let f := K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) 0
    (by simp) (by simp) ≫ K.homologyπ 0
  have hf : f ≫ X.singularHomology₀ε R = 𝟙 R :=
    by simpa only [f, K, Category.assoc, TopCat.singularHomology₀ε] using
      SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε (TopCat.toSSet.obj X) R σ
  have : IsIso f := by
    have : IsIso (f ≫ X.singularHomology₀ε R) := by rw [hf]; infer_instance
    exact IsIso.of_isIso_comp_right f (X.singularHomology₀ε R)
  let g := f ≫ HomologicalComplex.homologyMap (P.chainComplexπ R) 0
  have : IsIso g := inferInstance
  have hg : Function.Bijective g := (ConcreteCategory.isIso_iff_bijective g).mp inferInstance
  have hclass : g (ULift.up (1 : ℤ)) = euclideanPositiveLocalClass 0 := by
    change (K.liftCycles ((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) 0
      (by simp) (by simp) ≫ K.homologyπ 0 ≫
      HomologicalComplex.homologyMap (P.chainComplexπ R) 0) (ULift.up (1 : ℤ)) = _
    rw [HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
    change L.homologyπ 0
      (L.liftCycles (A := R) _ 0 _ _ (ULift.up (1 : ℤ))) = _
    change L.homologyπ 0 (L.liftCycles (A := R) _ 0 _ _ (ULift.up (1 : ℤ))) =
      ((L.sc 0).moduleCatLeftHomologyData.π ≫ (L.sc 0).moduleCatHomologyIso.inv)
        ⟨euclideanPositiveLocalChain 0, euclideanPositiveLocalChain_cycle 0⟩
    rw [← ShortComplex.moduleCatCyclesIso_inv_π]
    change (L.sc 0).homologyπ _ = (L.sc 0).homologyπ _
    congr 1
    apply (ModuleCat.mono_iff_injective (L.sc 0).iCycles).mp inferInstance
    change (L.liftCycles (A := R) _ 0 _ _ ≫ L.iCycles 0) (ULift.up (1 : ℤ)) =
      ((L.sc 0).moduleCatCyclesIso.inv ≫ (L.sc 0).iCycles)
        ⟨euclideanPositiveLocalChain 0, euclideanPositiveLocalChain_cycle 0⟩
    rw [HomologicalComplex.liftCycles_i, ShortComplex.moduleCatCyclesIso_inv_iCycles]
    rfl
  have heq : (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveLocalClass 0)) =
      g.hom.comp (ULift.moduleEquiv.symm.toLinearMap) := by
    apply LinearMap.ext_ring
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    change euclideanPositiveLocalClass 0 = g (ULift.up (1 : ℤ))
    exact hclass.symm
  rw [heq]
  exact hg.comp ULift.moduleEquiv.symm.bijective

end HolomorphicAnosov

