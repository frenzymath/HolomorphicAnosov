import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.ModTwoULiftRadialRelativeProfile
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Point relative profile in a universe-lifted Euclidean chart

Source: Hatcher, *Algebraic Topology*, pp.109–118 and p.153: the reduced sphere
calculation, the disk-boundary connecting map, and coefficient chains.  The
universe-lifted statement records the exact profile needed by chart transport;
its proof is intentionally a named Stage3 handoff while the relative pair
construction is completed.
-/

namespace HolomorphicAnosov.Topology.Homology

universe u
noncomputable section

/-- The mod-two support pair of a point in a universe-lifted Euclidean space has
one local class in the ambient dimension and no other classes.  This is the
point-profile interface used after the chart/excision comparison.

Proof plan: identify the point support pair with the Euclidean pair
`(ULift E, ULift E \ {x})`; use the radial deformation to a positive sphere,
the relative long exact sequence of the disk/sphere pair, and the reduced
sphere profile with the coefficient object `ULift (ZMod 2)`.  Transport the
result along the canonical ULift homeomorphism and cancel the coefficient
universe lift with `ULift.moduleEquiv`.  The zero-dimensional case uses the
augmentation kernel of the two-point sphere.  Empty complements and all
higher degrees are handled by the same relative sequence.

Source obligation: Hatcher pp.109–118, 153; the explicit cross-universe
relative-chain descent is not yet available as a public theorem.
-/
theorem modTwo_ulift_point_relative_profile (n : ℕ)
    (x : ULift.{u} (EuclideanSpace ℝ (Fin n))) :
    Nonempty (modTwoSupportHomology
      (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} n ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ k : ℕ, k ≠ n →
        Subsingleton (modTwoSupportHomology
          (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} k) := by
  obtain ⟨r, hr, hprofile⟩ := modTwo_ulift_euclidean_point_radial_profile n x
  exact hprofile


end
end HolomorphicAnosov.Topology.Homology
