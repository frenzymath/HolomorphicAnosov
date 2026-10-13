import HolomorphicAnosov.Topology.Franks.CoverPullbackAtlas
import HolomorphicAnosov.Geometry.ComplexModel

namespace HolomorphicAnosov

universe u v

open scoped ContDiff

variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
  [TopologicalSpace Y]

omit [ChartedSpace (ComplexModel d) X] in
/-- On the lifted transition domain, the transition of sheet charts agrees with the corresponding downstairs transition. (Lee, Prop. 1.15, p. 9). -/
theorem coverPullbackTransition (p : Y → X)
    (e e' : OpenPartialHomeomorph Y X)
    (z z' : OpenPartialHomeomorph X (ComplexModel d))
    (he : Set.EqOn e p e.source) (he' : Set.EqOn e' p e'.source)
    {x : ComplexModel d} (hx : x ∈ ((e.trans z).symm.trans (e'.trans z')).source) :
    x ∈ (z.symm.trans z').source ∧
      ((e.trans z).symm.trans (e'.trans z')) x = (z.symm.trans z') x := by
  exact AbstractCoverPullback.transition p e e' z z' he he' hx


end HolomorphicAnosov
