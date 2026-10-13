import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.Analysis.Complex.Circle

/-!
# Singular chain and cochain data for the circle winding theorem

Source: Hatcher, *Algebraic Topology*, Example 0.3 p. 6, Example 2.2 p. 105,
and pp. 197–201. These are the actual singular chain complex, its linear dual,
and their kernel/image quotients. The positive simplex is the exponential loop
with parameter increasing from zero to one. Definitions are extracted unchanged
from the winding theorem module so its supporting lemmas can import them.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- The actual complex unit circle with its usual topology. Source: Hatcher, Example0.3 p.6, realized by Mathlib Circle. -/
abbrev circleSpace : TopCat := TopCat.of Circle
/-- The one-point space. Source: Hatcher, pp.105 and 197–198. -/
abbrev pointSpace : TopCat := TopCat.of PUnit
/-- The actual singular simplicial set. Source: Hatcher pp.105 and 197–198; Mathlib TopCat.toSSet. -/
abbrev singularSet (X : TopCat) := TopCat.toSSet.obj X
/-- The unaugmented singular K-chain complex. Source: Hatcher pp.197–198 and the imported singular cochain definition. -/
abbrev chain (K : Type) [Field K] (X : TopCat) := (SingularCochain.chainFunctor K).obj X
/-- The degreewise K-linear dual singular cochain complex. Source: Hatcher pp.197–198 and the imported singular cochain definition. -/
abbrev cochain (K : Type) [Field K] (X : TopCat) := SingularCochain.complex K X
/-- The literal outgoing kernel of the singular boundary. Source: Hatcher p.105; Mathlib short-complex module kernel. -/
abbrev chainCycles (K : Type) [Field K] (X : TopCat) (n : ℕ) :=
  LinearMap.ker ((chain K X).sc n).g.hom
/-- The actual singular homology quotient of cycles by boundaries. Source: Hatcher p.105; Mathlib moduleCatLeftHomologyData. -/
abbrev chainClass (K : Type) [Field K] (X : TopCat) (n : ℕ) :=
  ((chain K X).sc n).moduleCatLeftHomologyData.H
/-- Ordinary singular cohomology, the actual kernel/image quotient. Source: Hatcher p.198 and the imported singular cochain definition. -/
abbrev cohomology (K : Type) [Field K] (X : TopCat) (n : ℕ) :=
  SingularCochain.cohomology K X n
/-- The literal kernel of the cochain coboundary. Source: Hatcher p.198 and the imported singular cochain definition. -/
abbrev cocycles (K : Type) [Field K] (X : TopCat) (n : ℕ) :=
  SingularCochain.cycles K (cochain K X) n
/-- The canonical quotient class of a singular cycle. Source: Hatcher p.105; Mathlib moduleCatLeftHomologyData.π. -/
abbrev cycleClass (K : Type) [Field K] (X : TopCat) (n : ℕ)
    (z : chainCycles K X n) : chainClass K X n :=
  ((chain K X).sc n).moduleCatLeftHomologyData.π z
/-- The canonical quotient class of a singular cocycle. Source: Hatcher p.198; Mathlib moduleCatLeftHomologyData.π. -/
abbrev cocycleClass (K : Type) [Field K] (X : TopCat) (n : ℕ)
    (a : cocycles K X n) : cohomology K X n :=
  ((cochain K X).sc n).moduleCatLeftHomologyData.π a

/-- The positive characteristic loop t↦exp(2πit). Source: Hatcher, Example0.3 p.6 and Example2.2 p.105. Mathlib TopCat.I is the canonical universe lift of the unit interval. -/
def positiveLoop : TopCat.I ⟶ circleSpace :=
  TopCat.ofHom ⟨fun t => Circle.exp (2 * Real.pi * (t.down : ℝ)), by fun_prop⟩

/-- The positive loop as the actual singular1-simplex. Source: Hatcher Example2.2 p.105; Mathlib toSSetObj₁Equiv. -/
def positiveSimplex : singularSet circleSpace _⦋1⦌ :=
  TopCat.toSSetObj₁Equiv.symm positiveLoop

/-- The coefficient-one singular simplex generator in the actual chain coproduct. Source: Hatcher p.105; Mathlib SSet.ιChainComplex. -/
abbrev simplexChain (K : Type) [Field K] (X : TopCat) (n : ℕ)
    (σ : singularSet X _⦋n⦌) : (chain K X).X n :=
  ((singularSet X).ιChainComplex (R := ModuleCat.of K K) σ) 1

/-- Actual K-linear cochain evaluation on a chain, without an abstract pairing assumption. Source: Hatcher pp.197–201; the native linearYoneda object is the corresponding ModuleCat morphism. -/
abbrev cocycleEval (K : Type) [Field K] (X : TopCat) (n : ℕ)
    (a : cocycles K X n) (z : (chain K X).X n) : K :=
  (show (chain K X).X n ⟶ ModuleCat.of K K from a.val) z

end
end HolomorphicAnosov.CircleSingularCohomology
