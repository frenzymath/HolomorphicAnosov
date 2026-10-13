import HolomorphicAnosov.Topology.RootedEdgeLoopCollapse

namespace HolomorphicAnosov
universe u v w

/-- The rooted edge-loop calculation for an assigned one-skeleton map.
Source: Hatcher, Algebraic Topology, Proposition 1A.2 pp.84–85 and Proposition 1B.9
pp.90–91. If every rooted vertex path is sent constantly to the target basepoint, then
the image of each root-path/edge/root-path loop is exactly the endpoint-fixed class of
the selected edge image. The final hypothesis identifies that edge image with the
assigned representative, so the computation is literal in Mathlib's
`FundamentalGroup.mapOfEq` convention and retains the displayed path casts. -/
theorem cw_assigned_edge_generator_g6
    {X : Type u} {Y : Type v} {V : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (o : X) (y₀ : Y)
    (ha : f o = y₀)
    (pt : V → X) (q : ∀ v : V, Path o (pt v))
    (hpt : ∀ v, f (pt v) = y₀)
    (hq : ∀ v t, f (q v t) = y₀)
    (u v : W → V) (edge : ∀ e : W, Path (pt (u e)) (pt (v e)))
    (ell : ∀ _e : W, Path y₀ y₀)
    (hell : ∀ e,
      ((edge e).map f.continuous).cast (hpt (u e)).symm (hpt (v e)).symm = ell e) :
    ∀ e : W,
      FundamentalGroup.mapOfEq f ha
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (((q (u e)).trans (edge e)).trans (q (v e)).symm))) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ell e)) := by
  intro e
  have hcalc := Topology.mapOfEq_rooted_edge_loop_of_constant_root_paths
    f o (pt (u e)) (pt (v e)) y₀ ha (hpt (u e)) (hpt (v e))
    (q (u e)) (q (v e)) (edge e) (hq (u e)) (hq (v e))
  exact hcalc.trans (by rw [hell e])

end HolomorphicAnosov
