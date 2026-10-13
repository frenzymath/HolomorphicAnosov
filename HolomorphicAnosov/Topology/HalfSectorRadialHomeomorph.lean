import HolomorphicAnosov.Topology.HalfSectorCompactRadialHomeomorph
import HolomorphicAnosov.Topology.HalfSectorRadialNormalization
import Mathlib.Analysis.Complex.Circle

/-!
# Complex radial front homeomorphism

This is the explicit C2 interface for Cairns' half-sector construction.  The
parent geometry supplies compactness and injectivity of the front's radial
directions; this module supplies the exact complex normalization and invokes
the compact-to-Hausdorff theorem.  No geometric injectivity is inferred here.
-/

namespace HolomorphicAnosov

open Set

/-- A compact complex front avoiding its apex is homeomorphic to its angular
normalization image whenever the normalization is injective on that front. -/
theorem halfSector_radial_homeomorph_of_injective
    (M : ℂ) (L : Set ℂ) (hL : IsCompact L)
    (hM : ∀ Q ∈ L, Q ≠ M)
    (hinj : Set.InjOn (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) L) :
    ∃ h : L ≃ₜ
        (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) '' L,
      ∀ x : L, (h x : ℂ) = (x.1 - M) / (‖x.1 - M‖ : ℂ) := by
  apply halfSector_compact_radial_homeomorph L
    (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) hL
  · exact Topology.continuousOn_radial_normalization M L hM
  · exact hinj

end HolomorphicAnosov
