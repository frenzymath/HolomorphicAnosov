import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov.FranksPointedTransport

/-- Composition of the actual pointed fundamental-group maps, retaining the
specified endpoint equalities. This is the functoriality used in the pointed
square of Franks Proposition (2.1), pp.70–71. -/
theorem mapOfEq_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) := by
  ext p
  simp only [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast,
    Path.Homotopic.Quotient.map_comp]

end HolomorphicAnosov.FranksPointedTransport
