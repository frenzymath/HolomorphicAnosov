import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
# Finiteness of quotient vertex classes

Source: Hatcher, *Algebraic Topology*, p.167: finitely many triangle vertices
remain finitely many vertex classes after the paired-face quotient. -/

/-- The set of quotient vertex classes is finite. -/
theorem vertexClass_finite {m : ℕ}
    (pair : Occurrence m → Occurrence m) :
    (VertexClass pair).Finite := by
  exact Set.finite_range (fun v : Fin m × Fin 3 ↦ vertex pair v)


end HolomorphicAnosov.RelativeTriangleRealization
