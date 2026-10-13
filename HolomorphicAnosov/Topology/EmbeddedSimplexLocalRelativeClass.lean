import HolomorphicAnosov.Topology.EmbeddedSimplexInteriorPreimage
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The native local chain and class of a simplex

DAG node: `topo.embedded_simplex_local_class_generator_g20`.
Source: Hatcher, *Algebraic Topology*, Example 2.23 p.125, Theorem 2.20
pp.119–124, and the relative exact sequence pp.115–118.
The chain and its cycle certificate below are explicit. Only the geometric
primitivity theorem at the end remains a named obligation.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- The literal coefficient-one chain of a continuous simplex, projected to
relative chains of Euclidean space modulo its punctured subspace.
Source: Hatcher pp.108,115. No generator is selected in this definition. -/
def simplexLocalRelativeChain (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 1)), EuclideanSpace ℝ (Fin n))) :
    ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ).chainComplex
      reducedSingularIntegralCoefficients).X n :=
  ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ).chainComplexπ
    reducedSingularIntegralCoefficients).f n
      (((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin n)))).ιChainComplex
        (R := reducedSingularIntegralCoefficients)
        (((TopCat.of (EuclideanSpace ℝ (Fin n))).toSSetObjEquiv _).symm s)) (ULift.up 1))

/-- A simplex whose faces avoid zero is a relative cycle. Every face factors
through the punctured subspace, so its chain is killed by the relative quotient;
the alternating boundary formula then gives zero. Source: Hatcher pp.108,115. -/
theorem simplexLocalRelativeChain_cycle (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hfaces : ∀ (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))),
      s (Convexity.StdSimplex.map i.succAbove t) ≠ 0) :
    let K := (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({0} : Set _)ᶜ).chainComplex reducedSingularIntegralCoefficients
    (K.sc (n + 1)).g.hom (simplexLocalRelativeChain (n + 1) s) = 0 := by
  classical
  dsimp only
  let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
  let A : Set X := ({0} : Set _)ᶜ
  let P := singularSubspacePair X A
  let R := reducedSingularIntegralCoefficients
  let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm s
  have hface (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
      X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t ∈ A := hfaces i t
  have hkill (i : Fin (n + 2)) :
      (TopCat.toSSet.obj X).ιChainComplex (R := R) ((TopCat.toSSet.obj X).δ i σ) ≫
        (P.chainComplexπ R).f n = 0 := by
    let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), A) :=
      ⟨fun t ↦ ⟨X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t, hface i t⟩,
        (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ)).continuous.subtype_mk _⟩
    let α := ((TopCat.of A).toSSetObjEquiv (op ⦋n⦌)).symm τ
    have hα : (TopCat.toSSet.map (singularSubspaceInclusion X A)).app _ α =
        (TopCat.toSSet.obj X).δ i σ := by
      apply (X.toSSetObjEquiv _).injective
      ext t
      rfl
    rw [← hα, ← SSet.ι_chainComplexMap_f]
    rw [Category.assoc]
    change _ ≫ (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0
    rw [P.chainComplex_condition_f]
    simp
  change (P.chainComplex R).d (n + 1) ((ComplexShape.down ℕ).next (n + 1))
    ((P.chainComplexπ R).f (n + 1) (((TopCat.toSSet.obj X).ιChainComplex (R := R) σ) (ULift.up 1))) = 0
  rw [ChainComplex.next_nat_succ]
  have hm : (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      (P.chainComplexπ R).f (n + 1) ≫ (P.chainComplex R).d (n + 1) n = 0 := by
    rw [(P.chainComplexπ R).comm]
    change (TopCat.toSSet.obj X).ιChainComplex (R := R) σ ≫
      ((TopCat.toSSet.obj X).chainComplex R).d (n + 1) n ≫ (P.chainComplexπ R).f n = 0
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, hkill, smul_zero, Finset.sum_const_zero]
  exact congrArg (fun f ↦ f.hom (ULift.up 1)) hm

/-- The native relative homology class of the specified coefficient-one simplex.
The proof argument is only its face-avoidance certificate, not a chosen class.
Source: Hatcher pp.108,115–118. -/
def simplexLocalRelativeClass (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hfaces : ∀ (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))),
      s (Convexity.StdSimplex.map i.succAbove t) ≠ 0) :
    (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({0} : Set _)ᶜ).homology (C := ModuleCat ℤ) reducedSingularIntegralCoefficients (n + 1) :=
  let K := (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
    ({0} : Set _)ᶜ).chainComplex reducedSingularIntegralCoefficients
  (K.sc (n + 1)).moduleCatHomologyIso.inv
    ((K.sc (n + 1)).moduleCatLeftHomologyData.π
      ⟨simplexLocalRelativeChain (n + 1) s, simplexLocalRelativeChain_cycle n s hfaces⟩)

end HolomorphicAnosov

