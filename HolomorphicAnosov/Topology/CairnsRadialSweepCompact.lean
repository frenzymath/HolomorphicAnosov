import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.Circle

namespace HolomorphicAnosov
open Set

/-- The closed radial sweep over a compact front is compact.

Source: Cairns (1951), §4(A), pp.863--864.  The displayed sweep is the image
of the compact product `ν × [0,1]` under the continuous affine radial map.
This provider isolates the compactness input used when identifying the closure
of the strict radial star with the closed sweep. -/
theorem cairns_radial_sweep_compact
    {N : ℂ} {L : Set ℂ} (hL : IsCompact L) :
    IsCompact {z : ℂ | ∃ Q ∈ L, ∃ t ∈ Icc (0 : ℝ) 1,
      z = (1 - t) • N + t • Q} := by
  let : CompactSpace L := isCompact_iff_compactSpace.mp hL
  let f : L × Icc (0 : ℝ) 1 → ℂ :=
    fun w ↦ (1 - (w.2 : ℝ)) • N + (w.2 : ℝ) • (w.1 : ℂ)
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hprod : IsCompact (Set.univ : Set (L × Icc (0 : ℝ) 1)) := isCompact_univ
  have himage : IsCompact (f '' (Set.univ : Set (L × Icc (0 : ℝ) 1))) :=
    hprod.image hcont
  have heq : f '' (Set.univ : Set (L × Icc (0 : ℝ) 1)) =
      {z : ℂ | ∃ Q ∈ L, ∃ t ∈ Icc (0 : ℝ) 1,
        z = (1 - t) • N + t • Q} := by
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩
      exact ⟨w.1, w.1.property, w.2, w.2.property, rfl⟩
    · rintro ⟨Q, hQ, t, ht, rfl⟩
      exact ⟨(⟨Q, hQ⟩, ⟨t, ht⟩), Set.mem_univ _, rfl⟩
  rw [← heq]
  exact himage

end HolomorphicAnosov
