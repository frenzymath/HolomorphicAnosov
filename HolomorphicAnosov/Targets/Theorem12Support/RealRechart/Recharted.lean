import Mathlib.Geometry.Manifold.ChartedSpace

/-! A type copy with the topology of the original space permits a separate atlas. (Zhang, §3, p. 11) -/

universe u

namespace HolomorphicAnosov.Theorem12SupportW2

/-- A type copy of `X` for equipping its points with a different atlas. (Zhang, §3, p. 11) -/
def Recharted (X : Type u) := X

/-- The topology on `Recharted X` inherited from `X`. (Zhang, §3, p. 11) -/
instance rechartedTopologicalSpace {X : Type u} [TopologicalSpace X] :
    TopologicalSpace (Recharted X) := inferInstanceAs (TopologicalSpace X)

end HolomorphicAnosov.Theorem12SupportW2

