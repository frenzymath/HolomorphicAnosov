import HolomorphicAnosov.Topology.PointOneCocycleZeroG10

/-!
# First singular cohomology of a point

Source: Hatcher, *Algebraic Topology*, Proposition 2.8, p.110, and the dual cochain
construction, pp.197–198. DAG node: `topo.point_first_cohomology_zero_g10`.
-/

namespace HolomorphicAnosov.SingularCochain

/-- The actual quotient singular cohomology H¹(point;R) is a subsingleton.
Source: Hatcher, *Algebraic Topology*, Proposition 2.8, p.110, and pp.197–198.
Every degree-one cocycle is zero by `point_one_cocycle_eq_zero`; hence the kernel
of the outgoing coboundary is a subsingleton. Its quotient by the incoming
boundary range is therefore a subsingleton. This quotient is definitionally
`cohomology R (TopCat.of PUnit) 1`; no replacement cohomology model is used.
The argument includes the zero ring and rings of arbitrary characteristic. -/
theorem point_first_cohomology_subsingleton (R : Type) [CommRing R] :
    Subsingleton (cohomology R (TopCat.of PUnit) 1) := by
  let : Subsingleton (cycles R (complex R (TopCat.of PUnit)) 1) :=
    ⟨fun a b ↦ (point_one_cocycle_eq_zero R a).trans
      (point_one_cocycle_eq_zero R b).symm⟩
  change Subsingleton
    (cycles R (complex R (TopCat.of PUnit)) 1 ⧸
      boundaries R (complex R (TopCat.of PUnit)) 1)
  infer_instance

end HolomorphicAnosov.SingularCochain

