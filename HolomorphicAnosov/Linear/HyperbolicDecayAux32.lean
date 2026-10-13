import HolomorphicAnosov.Linear.HyperbolicDecayAux31

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov
noncomputable section
set_option maxRecDepth 2000
namespace RealDecayDescent
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The complexified automorphism expressed in the coordinates of a finite real basis. -/
def complexified (A : V ≃L[ℝ] V) : CoordinateSpace (V := V) ≃L[ℂ] CoordinateSpace (V := V) :=
  ((tensorCoordinates.symm.trans (A.toLinearEquiv.baseChange ℝ ℂ)).trans
    tensorCoordinates).toContinuousLinearEquiv

end RealDecayDescent
end
end HolomorphicAnosov
