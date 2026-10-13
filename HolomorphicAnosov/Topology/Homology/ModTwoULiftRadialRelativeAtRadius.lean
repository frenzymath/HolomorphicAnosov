import HolomorphicAnosov.Topology.Homology.ModTwoEuclideanPointPositiveProfile
import HolomorphicAnosov.Topology.Homology.ModTwoEuclideanPointZeroProfile
import HolomorphicAnosov.Topology.Homology.ModTwoULiftSupportCoefficientTransport
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Fixed-radius radial profile for a universe-lifted Euclidean point

Source: Hatcher, *Algebraic Topology*, pp.109–118 and p.153.  The radial
retraction of a punctured Euclidean space onto any positive-radius sphere,
followed by the disk/sphere relative long exact sequence, gives the local
point profile.  The fixed-radius form is reusable when several local charts
must use one common radius.

The proof is intentionally isolated because the supplied formal library has
not yet packaged the radial deformation, relative long exact sequence, and
cross-universe singular-chain comparison into one theorem.  The omitted proof
must translate the chosen point to the origin, identify the complement of the
point with the chosen radius sphere by the radial homotopy, apply the
mod-two disk/sphere relative sequence (including reduced H₀ in dimension zero),
and transport the resulting native chain statement across `ULift` using the
public degree and boundary comparisons and `ULift.moduleEquiv`.  No extra
hypothesis beyond positivity of the radius is used.
-/

namespace HolomorphicAnosov.Topology.Homology

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u
noncomputable section

private theorem ulift_point_profile_of_native (n : ℕ)
    (x : ULift.{u} (EuclideanSpace ℝ (Fin n)))
    (h : Nonempty (modTwoSupportHomology (EuclideanSpace ℝ (Fin n)) {x.down}
      n ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ q : ℕ, q ≠ n → Subsingleton
        (modTwoSupportHomology (EuclideanSpace ℝ (Fin n)) {x.down} q)) :
    Nonempty (modTwoSupportHomology (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x}
      n ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ q : ℕ, q ≠ n → Subsingleton
        (modTwoSupportHomology (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} q) := by
  have hset : Set.ofPred (fun y : ULift.{u} (EuclideanSpace ℝ (Fin n)) ↦ y.down ∈ ({x.down} : Set _)) =
      ({x} : Set _) := by
    ext y
    simp only [Set.mem_singleton_iff]
    exact ULift.down_injective.eq_iff
  have hc (q : ℕ) : Nonempty
      (modTwoSupportHomology (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} q ≃ₗ[ZMod 2]
        modTwoSupportHomology (EuclideanSpace ℝ (Fin n)) {x.down} q) := by
    have hc := modTwo_ulift_support_coefficient_transport.{u}
      (EuclideanSpace ℝ (Fin n)) {x.down} q
    rw [hset] at hc
    exact hc
  obtain ⟨a⟩ := hc n
  obtain ⟨b⟩ := h.1
  refine ⟨⟨a.trans b⟩, ?_⟩
  intro q hq
  obtain ⟨a⟩ := hc q
  exact a.toEquiv.subsingleton_congr.mpr (h.2 q hq)

/-- At every positive radius, the radial disk/sphere calculation gives the full
mod-two local profile of a point in a universe-lifted Euclidean space.

Source obligation: Hatcher, *Algebraic Topology*, pp.109–118 and p.153; the
radial/relative-LES and cross-universe chain descent are the omitted formal
step recorded by this named theorem. -/
theorem modTwo_ulift_euclidean_point_radial_profile_at_radius (n : ℕ)
    (x : ULift.{u} (EuclideanSpace ℝ (Fin n))) (r : ℝ) (_hr : 0 < r) :
    Nonempty (modTwoSupportHomology
      (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} n ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ k : ℕ, k ≠ n →
        Subsingleton (modTwoSupportHomology
          (ULift.{u} (EuclideanSpace ℝ (Fin n))) {x} k) := by
  apply ulift_point_profile_of_native n x
  cases n with
  | zero => exact modTwo_euclidean_point_zero_profile x.down
  | succ d => exact modTwo_euclidean_point_positive_profile d x.down


end
end HolomorphicAnosov.Topology.Homology
