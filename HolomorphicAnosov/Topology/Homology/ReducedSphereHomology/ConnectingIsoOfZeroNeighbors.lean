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

/-- The exact-sequence step of Hatcher Corollary 2.14: a connecting
morphism with zero neighbors is an isomorphism of the actual integer modules. -/
def connectingIsoOfZeroNeighbors {L M N P : ModuleCat ℤ}
    (i : L ⟶ M) (δ : M ⟶ N) (j : N ⟶ P)
    (hL : IsZero L) (hP : IsZero P)
    (hleft : Function.Exact i δ) (hright : Function.Exact δ j) : M ≅ N := by
  have hi : i = 0 := hL.eq_of_src _ _
  have hj : j = 0 := hP.eq_of_tgt _ _
  have hinj : Function.Injective δ := by
    rw [hi] at hleft
    exact (LinearMap.exact_zero_iff_injective L δ.hom).mp hleft
  have hsurj : Function.Surjective δ := by
    rw [hj] at hright
    exact (LinearMap.exact_zero_iff_surjective P δ.hom).mp hright
  exact (LinearEquiv.ofBijective δ.hom ⟨hinj, hsurj⟩).toModuleIso

end HolomorphicAnosov.Topology.Homology
