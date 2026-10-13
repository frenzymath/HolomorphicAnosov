import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- Once the two-point base calculation and the literal disk-pair shifts have
been supplied, Hatcher's dimension induction covers ALL nonnegative degrees.
This internal assembly is not a substitute for either geometric premise. -/
theorem sphereProfile_induction
    (H : ℕ → ℕ → ModuleCat ℤ) (R : ModuleCat ℤ)
    (hbase : Nonempty (H 0 0 ≅ R))
    (hbaseoff : ∀ q, q ≠ 0 → IsZero (H 0 q))
    (hzero : ∀ k, IsZero (H (k + 1) 0))
    (hshift : ∀ k q, Nonempty (H (k + 1) (q + 1) ≅ H k q)) :
    ∀ k, Nonempty (H k k ≅ R) ∧ ∀ q, q ≠ k → IsZero (H k q) := by
  intro k
  induction k with
  | zero => exact ⟨hbase, hbaseoff⟩
  | succ k ih =>
    obtain ⟨e⟩ := hshift k k
    obtain ⟨a⟩ := ih.1
    refine ⟨⟨e ≪≫ a⟩, ?_⟩
    intro q hq
    cases q with
    | zero => exact hzero k
    | succ q =>
      obtain ⟨b⟩ := hshift k q
      exact IsZero.of_iso (ih.2 q (by omega)) b

end HolomorphicAnosov.Topology.Homology
