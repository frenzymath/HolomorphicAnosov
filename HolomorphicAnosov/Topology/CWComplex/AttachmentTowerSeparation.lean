import HolomorphicAnosov.Topology.CWComplex.AdjunctionHausdorff
import HolomorphicAnosov.Topology.CWComplex.AttachmentTowerCompact

/-! Separation for finite disk-attachment towers. Source: Hatcher, Appendix
Proposition A.3 p.522, specialized to finite towers. -/

open TopCat
open scoped TopCat
universe u
namespace HolomorphicAnosov.FiniteCellAdjunction

/-- Every finite attachment tower is Hausdorff. Start with its discrete space;
at a successor use compactness of the preceding tower and the closed-relation
Hausdorff theorem for the one-step adjunction. -/
theorem tower_t2Space {d : ℕ} {X : TopCat.{u}} (T : Tower d X) : T2Space X := by
  induction T with
  | points X finite discrete =>
    let := discrete
    infer_instance
  | attach T k a ih =>
    let := ih
    let := tower_compactSpace T
    exact adjunction_t2Space

/-- Every finite attachment tower is normal: the tower is compact Hausdorff,
and the standard compact-Hausdorff separation theorem applies. -/
theorem tower_normalSpace {d : ℕ} {X : TopCat.{u}} (T : Tower d X) : NormalSpace X := by
  let := tower_t2Space T
  let := tower_compactSpace T
  infer_instance

end HolomorphicAnosov.FiniteCellAdjunction
