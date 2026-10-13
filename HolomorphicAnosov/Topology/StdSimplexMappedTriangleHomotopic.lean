import HolomorphicAnosov.Topology.StdSimplexPathsHomotopic

open Convexity
universe u v
namespace HolomorphicAnosov.Topology

/-- The two-edge route across a simplex is homotopic to its direct route after
mapping all three vertices to one basepoint. Source: Hatcher, Algebraic
Topology, Theorem 2A.1 proof p.167, the nullhomotopic boundary of each triangle.
Interpolate the two routes within the simplex, postcompose with the triangle
map, and change the endpoint indices using the given exact vertex equalities.
All path parametrizations and endpoint casts are retained explicitly. -/
theorem stdSimplex_mapped_triangle_homotopic {ι : Type u} [Finite ι]
    {X : Type v} [TopologicalSpace X] {a b c : StdSimplex ℝ ι}
    (p : Path a b) (q : Path b c) (r : Path a c)
    (f : C(StdSimplex ℝ ι, X)) (x : X)
    (ha : x = f a) (hb : x = f b) (hc : x = f c) :
    (((p.map f.continuous).cast ha hb).trans ((q.map f.continuous).cast hb hc)).Homotopic
      ((r.map f.continuous).cast ha hc) := by
  have h := ((stdSimplex_paths_homotopic (p.trans q) r).map f).pathCast ha hc
  rw [Path.map_trans, Path.cast_trans _ _ ha hb hc] at h
  exact h

end HolomorphicAnosov.Topology
