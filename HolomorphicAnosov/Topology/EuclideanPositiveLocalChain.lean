import HolomorphicAnosov.Topology.EuclideanPositiveSimplex
import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology

/-!
# The coefficient-one positive Euclidean local relative chain

Source: Hatcher, *Algebraic Topology*, singular chains p.108, relative quotient
p.115 and ordered affine-simplex orientation p.269; Dold, *Fixed point index and
fixed point theorem for Euclidean neighborhood retracts*, §1.1, p.1.
DAG node: `topo.euclidean_positive_local_chain_g10`.

The simplex and the singular subspace pair are the shared concrete definitions.
The relative chain is obtained by inserting the integer coefficient one into
the specified simplex summand, then applying the native relative chain quotient.
No cycle, homology generator or fixed-point-index certificate is asserted here.
-/

noncomputable section

namespace HolomorphicAnosov

/-- The coefficient-one singular chain of `σₙ(t)ⱼ = tⱼ₊₁ − t₀`, projected to
`Cₙ(ℝⁿ, ℝⁿ \ {0}; ℤ)`. Source: Hatcher pp.108,115,269 and Dold §1.1 p.1.
`SSet.ιChainComplex` inserts the canonical lifted integer one, and
`SSetPair.chainComplexπ` is the actual quotient by chains in the punctured
Euclidean subspace. The coefficient object is a universe lift of the integers,
not rational coefficients or reduced chains. When `n = 0`, the simplex is the
ordinary point simplex and the punctured subspace is empty. -/
def euclideanPositiveLocalChain (n : ℕ) :
    ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ).chainComplex
      reducedSingularIntegralCoefficients).X n :=
  ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ).chainComplexπ
    reducedSingularIntegralCoefficients).f n
      (((TopCat.toSSet.obj (TopCat.of (EuclideanSpace ℝ (Fin n)))).ιChainComplex
        (R := reducedSingularIntegralCoefficients)
        (((TopCat.of (EuclideanSpace ℝ (Fin n))).toSSetObjEquiv _).symm
          (euclideanPositiveSimplex n))) (ULift.up 1))

end HolomorphicAnosov
