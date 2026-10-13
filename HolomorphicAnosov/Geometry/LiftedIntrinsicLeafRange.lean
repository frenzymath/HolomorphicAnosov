import Mathlib.Topology.Path

/-! Path-lift ranges of intrinsic leaves. -/

universe u v w

namespace HolomorphicAnosov

/-- Endpoints of paths in Y which project to intrinsic paths of the marked leaf (Franks§1 Proposition(1.1), p.65, Corollary(1.3), p.66, and Hatcher Proposition1.30, p.60, with path uniqueness Proposition1.34, p.62).-/
def liftedIntrinsicLeafRange {X : Type u} {Y : Type v} {L : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace L]
    (p : Y → X) (j : L → X) (a : L) (y : Y) : Set Y :=
  {z | ∃ (b : L) (γ : Path a b) (η : Path y z),
    ∀ t, p (η t) = j (γ t)}

end HolomorphicAnosov
