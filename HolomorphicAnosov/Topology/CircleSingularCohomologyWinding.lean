import HolomorphicAnosov.Topology.CirclePositiveCycleValG10
import HolomorphicAnosov.Topology.CirclePositiveSimplexCycleG10
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.Algebra.Homology.FieldChainKroneckerEvaluation
import HolomorphicAnosov.AlgebraicTopology.CharacteristicCellCohomologyComparison
import HolomorphicAnosov.AlgebraicTopology.SingularCupProductLaws
import HolomorphicAnosov.AlgebraicTopology.SingularRelativeCohomologyPairTheorems
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Basis.Defs
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingExplicitBase
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingCoreG11
import HolomorphicAnosov.Topology.Homology.ConstantFirstCohomologyPullbackG10

/-!
# Ordinary singular field-coefficient cohomology of the circle

Source: Hatcher, *Algebraic Topology*, Example0.3 p.6, Example2.2 p.105,
cochains/field coefficients pp.197–198, relative connecting evaluation
pp.199–201, Proposition3.17 p.217 and AppendixA.2 p.521.
The chain and cochain types below are Mathlib's actual singular complex and
its literal dual kernel/image quotient, defined in the imported definition
node. No cellular group, winding proxy or unspecified homology object is used.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- The ordinary singular field-coefficient circle profile, normalized by the
positive once-around singular cycle.

Source: Hatcher, Example0.3 p.6, Example2.2 p.105, pp.197–201,
Proposition3.17 p.217 and AppendixA.2 p.521.

The singleton-index bases assert that the listed actual quotient classes are
basis vectors. `Subsingleton` of a module says precisely that it is the zero
module. `a` and `u` are cocycles, not arbitrary cochain functions. The unit
cocycle has value1 on every0-simplex. The normalized evaluation uses the
actual positive chain, and uniqueness is stated for every cocycle class.
The last witness is the cup square: its value on a2-simplex is the product
of the values of `a` on face2 ([0,1]) and face0 ([1,2]), exactly Hatcher's
ordinary singular cup formula. Thus its zero quotient class is `a∪a=0`,
not a separately assumed cup operation.

Proof: A point has one singular simplex in every degree. Its alternating
boundary is zero in odd degree and identity in positive even degree, so H₀=K
and higher homology vanishes, including in characteristic2. Taking the
K-linear dual gives the point's stated cohomology and constant unit.
For (I,{0,1}), the relative cohomology sequence identifies H¹ with the
cokernel of c↦(c,c); all other relative groups vanish. The connecting image
of the endpoint cochain (0,1) evaluates to1 on the increasing interval,
since its boundary is [1]−[0].

The exponential loop gives the circle its one-vertex, one-edge CW structure.
The AddCircle quotient and its (0,1) chart identify the characteristic edge
with the actual Circle carrier and positive orientation. Characteristic-cell
comparison identifies H¹(S¹,{1};K) with the preceding relative interval
class. The circle is path connected; its ordinary H⁰ consists of constant
cocycles. In the pair sequence the degree0 restriction is an isomorphism,
so relative-to-absolute comparison is an isomorphism in positive degrees.
This gives the circle profile and its normalized positive class.

The positive edge has equal endpoints and is therefore a cycle. Relative
representative evaluation gives1, with no sign ambiguity. Field Kronecker
evaluation identifies H¹ with the dual of H₁. If a homology vector were
outside the line spanned by this cycle, a linear functional on their span
with values0,1 would extend to H₁, contradicting the one-dimensional dual.
Thus the cycle is a basis, and evaluation1 uniquely specifies the H¹ basis.
A constant map factors through the point, proving pullback vanishing for
every source, including the empty source. The literal singular cup formula
descends to cohomology; its square lies in the zero H² group, hence vanishes
also in characteristic2 without division by2.
-/
theorem circle_singular_cohomology_winding (K : Type) [Field K] :
    ∃ (z : chainCycles K circleSpace 1)
      (a : cocycles K circleSpace 1) (u : cocycles K circleSpace 0)
      (up : cocycles K pointSpace 0)
      (B₁ : Module.Basis Unit K (chainClass K circleSpace 1))
      (Bcoh1 : Module.Basis Unit K (cohomology K circleSpace 1))
      (Bcoh0 : Module.Basis Unit K (cohomology K circleSpace 0))
      (Bp : Module.Basis Unit K (cohomology K pointSpace 0)),
      z.val = simplexChain K circleSpace 1 positiveSimplex ∧
      B₁ () = cycleClass K circleSpace 1 z ∧
      Bcoh1 () = cocycleClass K circleSpace 1 a ∧
      Bcoh0 () = cocycleClass K circleSpace 0 u ∧
      Bp () = cocycleClass K pointSpace 0 up ∧
      (∀ σ : singularSet circleSpace _⦋0⦌,
        cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1) ∧
      (∀ σ : singularSet pointSpace _⦋0⦌,
        cocycleEval K pointSpace 0 up (simplexChain K pointSpace 0 σ) = 1) ∧
      cocycleEval K circleSpace 1 a z.val = 1 ∧
      (∀ a' : cocycles K circleSpace 1,
        cocycleEval K circleSpace 1 a' z.val = 1 →
          cocycleClass K circleSpace 1 a' = cocycleClass K circleSpace 1 a) ∧
      (∀ n : ℕ, 2 ≤ n → Subsingleton (cohomology K circleSpace n)) ∧
      (∀ n : ℕ, 0 < n → Subsingleton (cohomology K pointSpace n)) ∧
      (∀ (Z : TopCat) (b : Circle),
        (SingularCochain.cohomologyPullback K
          (TopCat.ofHom (ContinuousMap.const Z b)) 1)
          (cocycleClass K circleSpace 1 a) = 0) ∧
      (∃ c : cocycles K circleSpace 2,
        (∀ σ : singularSet circleSpace _⦋2⦌,
          cocycleEval K circleSpace 2 c (simplexChain K circleSpace 2 σ) =
            cocycleEval K circleSpace 1 a
              (simplexChain K circleSpace 1 ((singularSet circleSpace).δ 2 σ)) *
            cocycleEval K circleSpace 1 a
              (simplexChain K circleSpace 1 ((singularSet circleSpace).δ 0 σ))) ∧
        cocycleClass K circleSpace 2 c = 0) := by
  obtain ⟨z, u, up, hz, hu, hup⟩ := circle_winding_explicit_base K
  obtain ⟨a, B₁, Bcoh1, Bcoh0, hB₁, hBcoh1, hBcoh0, hEval, huniq, hhigh⟩ :=
    circle_degree_one_profile_core K z u hz hu
  obtain ⟨Bp, hBp⟩ := point_degree_zero_basis_core K up hup
  obtain ⟨c, hcup, hcupClass⟩ := circle_cup_square_core K a hhigh
  refine ⟨z, a, u, up, B₁, Bcoh1, Bcoh0, Bp, hz, hB₁, hBcoh1,
    hBcoh0, hBp, hu, hup, hEval, huniq, hhigh, ?_, ?_, ⟨c, hcup, hcupClass⟩⟩
  · exact point_positive_cohomology_core K
  · intro Z b
    exact SingularCochain.constant_first_cohomology_pullback_eq_zero K Z circleSpace b
      (cocycleClass K circleSpace 1 a)

end
end HolomorphicAnosov.CircleSingularCohomology
