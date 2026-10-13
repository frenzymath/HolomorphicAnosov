import HolomorphicAnosov.Topology.RelativeTriangleRealization.VertexClassStratum
import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-- An interior point of a quotient triangle cannot be a vertex class.

Source: Hatcher, *Algebraic Topology*, pp.103--104 and p.167: strictly
positive barycentric coordinates are disjoint from the singleton vertex
strata. The quotient vertex-classification theorem transports this coordinate
separation through the paired-triangle relation. -/
theorem triangleInterior_ne_vertex {m : ℕ}
    (pair : Occurrence m → Occurrence m) (hinv : Function.Involutive pair)
    (i : Fin m) (t : interior 2) :
    triangle pair i t.val ∉ VertexClass pair := by
  intro h
  obtain ⟨v, hv⟩ := h
  have hv' : vertex pair v = Quotient.mk _ (i, t.val) := hv
  obtain ⟨w, hw⟩ := vertexClass_classifies pair hinv v (i, t.val) hv'
  have hwt := congrArg Prod.snd hw
  have hwcoord := congrArg (fun z : Simplex 2 => z.weights w.2) hwt
  have hwpos := t.property w.2
  have hwindex : w.2 = 0 ∨ w.2 = 1 ∨ w.2 = 2 := by omega
  rcases hwindex with h0 | h1 | h2
  · have hzero := congrArg (fun z : Simplex 2 => z.weights 1) hwt
    have hpos := t.property 1
    simp [Convexity.StdSimplex.weights_single, h0] at hzero
    linarith
  · have hzero := congrArg (fun z : Simplex 2 => z.weights 0) hwt
    have hpos := t.property 0
    simp [Convexity.StdSimplex.weights_single, h1] at hzero
    linarith
  · have hzero := congrArg (fun z : Simplex 2 => z.weights 0) hwt
    have hpos := t.property 0
    simp [Convexity.StdSimplex.weights_single, h2] at hzero
    linarith


end HolomorphicAnosov.RelativeTriangleRealization
