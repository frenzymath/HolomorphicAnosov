import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.AppendEuclidean

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

def appendEuclideanLinear (m : ℕ) :
    (EuclideanSpace ℝ (Fin m) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)) where
  toFun p := appendEuclidean m p.1 p.2
  map_add' p q := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [appendEuclidean]
  map_smul' a p := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [appendEuclidean]

end HolomorphicAnosov.Topology.Homology
