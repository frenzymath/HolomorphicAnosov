import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroOfSurjectiveFromZero
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ConnectingIsoOfZeroNeighbors

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The GOOD-PAIR provider supplies the original quotient and actual connecting
map. With the disk acyclicity input established geometrically, this is exactly
Hatcher's positive-degree shift and separate reduced-degree-zero tail. -/
theorem goodPair_shift_of_acyclic (X : TopCat) (A V : Set X)
    (hA : A.Nonempty) (hclosed : IsClosed A) (hAV : A ⊆ V)
    (hneighborhood : A ⊆ interior V)
    (d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV)
    (hzero : ∀ n, IsZero (integralReducedSingularHomology X n)) :
    IsZero (integralReducedSingularHomology (TopCat.of (GoodPair.Collapsed A)) 0) ∧
    ∀ n, Nonempty (integralReducedSingularHomology
      (TopCat.of (GoodPair.Collapsed A)) (n + 1) ≅
      integralReducedSingularHomology (TopCat.of A) n) := by
  obtain ⟨base, δ, _, _, _, hleft, hright, hsurj, _⟩ :=
    GoodPair.good_pair_reduced_homology_exact_sequence X A V hA hclosed hAV hneighborhood d
  refine ⟨zeroOfSurjectiveFromZero _ (hzero 0) hsurj, ?_⟩
  intro n
  exact ⟨connectingIsoOfZeroNeighbors _ (δ n) _ (hzero (n + 1)) (hzero n)
    (hleft n) (hright n)⟩

end HolomorphicAnosov.Topology.Homology
