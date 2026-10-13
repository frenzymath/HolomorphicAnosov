import HolomorphicAnosov.Topology.EuclideanPositiveLocalConnecting
import Mathlib.Algebra.Module.Submodule.Equiv

noncomputable section
namespace HolomorphicAnosov

/-- Algebraic transport of a local coefficient equivalence to the explicit
punctured boundary class.  The connecting isomorphism and its chain-level
normalization are already proved in `EuclideanPositiveLocalConnecting`; this
helper only packages the inverse of the boundary span map.
Source: Hatcher pp.116--118; integer-module algebra.
-/
theorem euclideanPositiveBoundaryClass_coefficient_equiv_from_local_generator
    (n : ℕ)
    (hlocal : Function.Bijective (LinearMap.toSpanSingleton ℤ _
      (euclideanPositiveLocalClass (n + 1)))) :
    ∃ e : integralReducedSingularHomology
        (TopCat.of ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)) n ≃ₗ[ℤ] ℤ,
      e (euclideanPositiveBoundaryClass n) = 1 := by
  have hboundary : Function.Bijective (LinearMap.toSpanSingleton ℤ _
      (euclideanPositiveBoundaryClass n)) :=
    (euclideanPositiveLocalClass_free_generator_iff_boundary n).mp hlocal
  let e : integralReducedSingularHomology
      (TopCat.of ↥(({0} : Set (EuclideanSpace ℝ (Fin (n + 1))))ᶜ)) n ≃ₗ[ℤ] ℤ :=
    (LinearEquiv.ofBijective
      (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveBoundaryClass n)) hboundary).symm
  refine ⟨e, ?_⟩
  let L := LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton ℤ _ (euclideanPositiveBoundaryClass n)) hboundary
  change L.symm (euclideanPositiveBoundaryClass n) = 1
  simpa [L, LinearMap.toSpanSingleton_apply] using L.symm_apply_apply (1 : ℤ)

end HolomorphicAnosov

