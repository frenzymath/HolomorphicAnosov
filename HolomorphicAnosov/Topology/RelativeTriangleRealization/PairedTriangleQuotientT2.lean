import HolomorphicAnosov.Topology.RelativeTriangleRealization.Basic
import HolomorphicAnosov.Topology.RelativeTriangleRealization.PairedTriangleQuotientT2Construction

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-!
# Hausdorffness of the paired-triangle quotient

Source: Hatcher, *Algebraic Topology*, pp.103--104 and p.167, together with
Appendix A.3 pp.521--522. The finite ordered-triangle quotient is compact and
Hausdorff because the only identifications are the closed paired faces and the
finite vertex classes.
-/

/-- The finite paired-face quotient is Hausdorff.

The source proof stratifies each simplex into its interior, its three open
faces, and its vertices. Interior points have singleton classes; an open-face
class contains only the point and its paired point; and vertex classes are
finite. These strata make the generated relation closed in the compact finite
disjoint union of closed simplices. The compact quotient by this closed
relation is Hausdorff. The theorem is intentionally named so the
quotient-separation step is reusable by the classical CW assembly. -/
theorem pairedTriangle_quotient_t2 {m : ℕ}
    (pair : Occurrence m → Occurrence m)
    (hinv : Function.Involutive pair) :
    T2Space (Space pair) := by
  exact pairedTriangle_quotient_t2_construction pair hinv trivial


end HolomorphicAnosov.RelativeTriangleRealization
