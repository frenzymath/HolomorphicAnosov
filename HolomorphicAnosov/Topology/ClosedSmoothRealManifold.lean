import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Closed smooth real manifolds

This sandbox module records the concrete Stage-2 interface audited for
`topo.def_closed_smooth_manifold`.  It packages the topological and smooth
manifold structures needed by the higher-dimensional homotopy-torus premise;
it does not assert any classification result.
-/

namespace HolomorphicAnosov

universe u

open scoped ContDiff

/--
A closed smooth real `n`-manifold with a fixed, actual Euclidean atlas.

The topology and `ChartedSpace` are explicit typeclass parameters so every
later map on `M` uses this same selected structure.  The model is the whole
space `EuclideanSpace ℝ (Fin n)`, hence the canonical
`modelWithCornersSelf_boundaryless` instance supplies the boundaryless
convention.  Compactness, Hausdorffness, second countability, and smoothness
are retained as typeclass fields.  No connectedness or orientation is part of
this interface.

Source: the reviewed interface in
`dag/nodes/topo.def_closed_smooth_manifold.json`, based on Mathlib's
`ChartedSpace`, `CompactSpace`, `T2Space`, `SecondCountableTopology`, and
`IsManifold` declarations.
-/
class ClosedSmoothRealManifold (n : outParam ℕ) (M : Type u)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop where
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  [secondCountableTopology : SecondCountableTopology M]
  [isManifold :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]

end HolomorphicAnosov
