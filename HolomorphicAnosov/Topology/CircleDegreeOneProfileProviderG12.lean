import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingExplicitBase
import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import Mathlib.LinearAlgebra.Basis.Defs
import HolomorphicAnosov.Topology.CircleDegreeOneProfileWitnessG12

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- Source-backed one-cell calculation for the normalized degree-one circle
class. Hatcher Example 2.2 pp.197--201 and Proposition 3.17 p.217 identify the
relative interval class, evaluate it on the positive cycle, and show all higher
circle cohomology groups vanish. -/
theorem circle_degree_one_profile_provider (K : Type) [Field K]
    (z : chainCycles K circleSpace 1) (u : cocycles K circleSpace 0)
    (hz : z.val = simplexChain K circleSpace 1 positiveSimplex)
    (hu : ∀ σ : singularSet circleSpace _⦋0⦌,
      cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1) :
    ∃ (a : cocycles K circleSpace 1)
      (B₁ : Module.Basis Unit K (chainClass K circleSpace 1))
      (Bcoh1 : Module.Basis Unit K (cohomology K circleSpace 1))
      (Bcoh0 : Module.Basis Unit K (cohomology K circleSpace 0)),
      B₁ () = cycleClass K circleSpace 1 z ∧
      Bcoh1 () = cocycleClass K circleSpace 1 a ∧
      Bcoh0 () = cocycleClass K circleSpace 0 u ∧
      cocycleEval K circleSpace 1 a z.val = 1 ∧
      (∀ a' : cocycles K circleSpace 1,
        cocycleEval K circleSpace 1 a' z.val = 1 →
          cocycleClass K circleSpace 1 a' = cocycleClass K circleSpace 1 a) ∧
      (∀ n : ℕ, 2 ≤ n → Subsingleton (cohomology K circleSpace n)) := by
  obtain ⟨⟨a, B₁, Bcoh1, Bcoh0, hB₁, hBcoh1, hBcoh0, hEval, huniq, hhigh⟩, _⟩ :=
    circle_degree_one_profile_witness K z u hz hu
  exact ⟨a, B₁, Bcoh1, Bcoh0, hB₁, hBcoh1, hBcoh0, hEval, huniq, hhigh⟩

end
end HolomorphicAnosov.CircleSingularCohomology

