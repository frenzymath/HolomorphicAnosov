import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.EuclideanPositiveLocalChain
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Data.Finsupp.Basic

/-!
# The positive Euclidean local class of the specified affine simplex

DAG node: `topo.euclidean_positive_local_class_g10`.
Source: Hatcher, *Algebraic Topology*, singular boundaries and cycle classes p.108,
relative chains and homology pp.115–118, and ordered edge-basis orientation p.269;
Dold, *Fixed point index and fixed point theorem for Euclidean neighborhood retracts*,
Topology 4 (1965), §1.1 p.1. The particular affine simplex is the coordinate choice
already constructed in `EuclideanPositiveSimplex`; it is not a formula printed in Hatcher.

The class below belongs to the actual unaugmented relative singular homology of
`(ℝⁿ, ℝⁿ \ {0})` with integral coefficients. Its data are the canonical quotient
image of the existing coefficient-one chain, rather than an independently chosen
generator or a supplied orientation. The named cycle certificate is proved below.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace HolomorphicAnosov

/-- The coefficient-one positive local chain has zero outgoing relative boundary.

Source: Hatcher, *Algebraic Topology*, p.108, the alternating singular boundary;
p.115, the quotient boundary on relative chains; p.269, the ordered simplex convention.
This is the construction certificate in `topo.euclidean_positive_local_class_g10`.
The actual chain is `euclideanPositiveLocalChain n`; the pair and the coefficient object
are the same as in that definition. The coefficient object is `ULift ℤ` in `ModuleCat ℤ`.
Its name mentions reduced homology, but no augmentation is used in this relative complex.

Complete natural-language proof of the current node's cycle assertion:

For `n > 0`, write `σₙ(t)ⱼ = tⱼ₊₁ - t₀` for the prescribed simplex. If its value is zero,
then all the barycentric weights equal `t₀`. Since their sum is one, each weight is
`1/(n+1)`, which is strictly positive. A codimension-one face has its omitted vertex's
weight zero, so no such face contains a preimage of zero. Therefore each face of `σₙ`
has image in the punctured Euclidean space. The continuous face map, equipped with this
pointwise nonzero certificate, factors continuously through the punctured subspace by
`Continuous.subtype_mk`. Its singular chain is consequently in the image of the actual
subspace chain map. The relative complex is the native cokernel of that map, so its
quotient projection kills each face chain. Apply `SSet.ιChainComplex_d`, the alternating
boundary formula, to the coefficient-one summand. The chain-map equation for the relative
projection identifies the relative boundary of the prescribed projected chain with the
projected alternating sum of its faces. Every summand vanishes, so that boundary is zero.
For `n = 0`, the ordinary natural-number-indexed chain complex has no outgoing negative
degree differential; the outgoing map of its degree-zero short complex is zero. Thus
the same zero-boundary conclusion holds for the coefficient-one point chain. In this
dimension Euclidean space is a point and its punctured subspace is empty.

The singular-subspace adapter supplies the exact subspace and quotient identifications;
its lower comparison obligations remain separate. The argument needs neither an assumed
homology generator nor a preexisting Euclidean orientation structure. The zero preimage
and face calculation are elementary consequences of the explicit simplex coordinates;
the formula, quotient boundary and cycle interpretation are Hatcher's constructions.
-/
theorem euclideanPositiveLocalChain_cycle (n : ℕ) :
    let K :=
      (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
        ({0} : Set _)ᶜ).chainComplex reducedSingularIntegralCoefficients
    (K.sc n).g.hom (euclideanPositiveLocalChain n) = 0 := by
  classical
  dsimp only
  cases n with
  | zero =>
    simp [HomologicalComplex.sc, HomologicalComplex.shape]
  | succ n =>
    let X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))
    let A : Set X := ({0} : Set _)ᶜ
    let P := singularSubspacePair X A
    let R := reducedSingularIntegralCoefficients
    let σ := (X.toSSetObjEquiv (op ⦋n + 1⦌)).symm (euclideanPositiveSimplex (n + 1))
    have hface (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))) :
        X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i σ) t ∈ A := by
      change euclideanPositiveSimplex (n + 1) (Convexity.StdSimplex.map i.succAbove t) ≠ 0
      -- Expand only this prescribed face; its missing weight is zero by Mathlib.
      intro hz
      let u := Convexity.StdSimplex.map i.succAbove t
      have hconstant (j : Fin (n + 2)) : u.weights j = u.weights 0 := by
        refine Fin.cases rfl (fun k ↦ ?_) j
        have hk := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ x k) hz
        exact sub_eq_zero.mp hk
      have hi : u.weights i = 0 := by
        dsimp only [u]
        rw [Convexity.StdSimplex.weights_map]
        exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
      apply Convexity.StdSimplex.weights_ne_zero u
      ext j
      exact (hconstant j).trans ((hconstant i).symm.trans hi)
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

/-- The positive local class `ωₙ` is the class of the specified coefficient-one affine simplex.

Source: Hatcher, *Algebraic Topology*, pp.108,115–118, cycles modulo boundaries;
p.269, positive orientation determined by the ordered edge basis; Dold §1.1 p.1,
the positive point-relative class underlying the Euclidean fundamental class.
This is the data definition in `topo.euclidean_positive_local_class_g10`.

The simplex has ordered vertices `(-1,…,-1), e₁,…,eₙ` and edge matrix `I + 11ᵀ`, whose
determinant is `n+1 > 0`, so the coordinate choice is positive in Hatcher's convention.
Uniform barycentric weights map to zero, strictly inside the simplex. No arbitrary
orientation or generator is an input. Membership in the cycle kernel is supplied only
by the named certificate above, which concerns the already specified chain.

For the native short complex of relative chains, `moduleCatLeftHomologyData.π` is the
literal quotient of the kernel of the outgoing differential by the incoming boundaries.
`moduleCatHomologyIso.inv` transports that quotient element to the homology of the same
complex. Thus the displayed body defines precisely its cycle class, with no choice of
an unrelated class or homology carrier. Changing the cycle membership proof does not
change the kernel element or its class, by proof irrelevance. In dimension zero this
is the coefficient-one point class in ordinary `H₀(point,empty;ℤ)`; it is never an
augmented or reduced degree-zero group. Primitivity and the homology-group computation
are separate assertions, not assumptions hidden in this definition.
-/
def euclideanPositiveLocalClass (n : ℕ) :
    (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ).homology (C := ModuleCat ℤ) reducedSingularIntegralCoefficients n :=
  let K :=
    (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0} : Set _)ᶜ).chainComplex reducedSingularIntegralCoefficients
  (K.sc n).moduleCatHomologyIso.inv
    ((K.sc n).moduleCatLeftHomologyData.π
      ⟨euclideanPositiveLocalChain n, euclideanPositiveLocalChain_cycle n⟩)

end HolomorphicAnosov

