import HolomorphicAnosov.Topology.CWComplex.AttachmentTower
import Mathlib.Topology.Compactness.Compact

/-! Compactness of finite disk-attachment towers, following Hatcher,
*Algebraic Topology*, Appendix p.520. -/

universe u

namespace HolomorphicAnosov.FiniteCellAdjunction

/-- A finite disk-attachment tower has a compact endpoint.

Source: Hatcher, *Algebraic Topology*, Appendix p.520: attaching a cell preserves
compactness. Induct on the tower. The finite initial space is compact. At each
successor, the old space and the finite disjoint union of compact Euclidean disks
are compact; their disjoint union is compact, and so is its quotient. The argument
uses the given quotient topology and needs no separation or nonemptiness hypothesis.
-/
theorem tower_compactSpace {d : ℕ} {X : TopCat.{u}} (T : Tower d X) : CompactSpace X := by
  induction T with
  | points X finite discrete =>
    let := finite
    infer_instance
  | attach T k a ih =>
    let := ih
    unfold adjunction
    infer_instance


end HolomorphicAnosov.FiniteCellAdjunction
