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

/-- The degree-zero tail is surjective from a zero module. It cannot be
obtained by interpreting a natural predecessor as a negative sphere degree. -/
theorem zeroOfSurjectiveFromZero {L M : ModuleCat ℤ} (q : L ⟶ M)
    (hL : IsZero L) (hq : Function.Surjective q) : IsZero M := by
  have hz : q = 0 := hL.eq_of_src _ _
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨y, rfl⟩ := hq x
  rw [hz]
  rfl

end HolomorphicAnosov.Topology.Homology
