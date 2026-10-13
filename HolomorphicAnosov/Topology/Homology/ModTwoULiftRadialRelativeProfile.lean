import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoULiftRadialRelativeAtRadius
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Radial relative profile for a universe-lifted Euclidean point

Source: Hatcher, *Algebraic Topology*, pp.109–118 and p.153.  The radial
retraction of a punctured Euclidean space onto a positive sphere, followed by
the disk/sphere relative long exact sequence, gives the local point profile.
The theorem records the coefficient-universe descent that remains specific to
the lifted ambient carrier.
-/

namespace HolomorphicAnosov.Topology.Homology

universe u
noncomputable section

/-- The radial disk/sphere calculation supplies a positive radius and the full
mod-two profile for a point in `ULift (EuclideanSpace ...)`.

Proof plan: translate `x` to the origin, choose a positive radius, and use the
radial homotopy outside the point to identify the complement with the radius-r
sphere.  The relative long exact sequence of the closed ball and its sphere,
combined with the mod-two sphere profile and the two-point reduced H0 base case,
gives one class in degree `n` and subsingleton groups off that degree.  The
public ULift degree/boundary bridges then identify the lifted native chains;
`ULift.moduleEquiv` cancels the coefficient lift.  This statement is separate
from the final provider so the omitted radial/LES argument has one honest node.

Source obligation: Hatcher pp.109–118 and p.153; the cross-universe relative
pair descent is the remaining admitted step.
-/
theorem modTwo_ulift_euclidean_point_radial_profile (n : ℕ)
    (x : ULift.{u} (EuclideanSpace ℝ (Fin n))) :
    ∃ r : ℝ, 0 < r ∧
      (Nonempty (modTwoSupportHomology
        (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} n ≃ₗ[ZMod 2] ZMod 2) ∧
        ∀ k : ℕ, k ≠ n →
          Subsingleton (modTwoSupportHomology
            (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} k)) := by
  refine ⟨1, zero_lt_one, ?_⟩
  exact modTwo_ulift_euclidean_point_radial_profile_at_radius n x 1 zero_lt_one


end
end HolomorphicAnosov.Topology.Homology
