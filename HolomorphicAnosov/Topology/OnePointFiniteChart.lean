import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.PartialHomeomorph.Basic

open Set

namespace HolomorphicAnosov

/-- The finite coordinate induced by a sphere homeomorphism sending `y` to infinity sends `x` to zero and recovers the homeomorphism through the finite embedding. (Conway II, Lemma 5.4) -/
theorem onePoint_finite_chart
    (x y : OnePoint ℂ) (e : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hex : e x = OnePoint.some 0) (hey : e y = OnePoint.infty) :
    ∃ g : OnePoint ℂ → ℂ,
      ContinuousOn g {y}ᶜ ∧
      (∀ z, z ≠ y → (g z = 0 ↔ z = x)) ∧
      (∀ z, z ≠ y → OnePoint.some (g z) = e z) := by
  let c : PartialHomeomorph ℂ (OnePoint ℂ) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toPartialHomeomorph OnePoint.some
  have hrange {z : OnePoint ℂ} (hz : z ≠ y) : e z ∈ Set.range OnePoint.some :=
    OnePoint.ne_infty_iff_exists.mp (fun h ↦ hz (e.injective (h.trans hey.symm)))
  let g : OnePoint ℂ → ℂ := c.symm ∘ e
  have hgval (z : OnePoint ℂ) (hz : z ≠ y) : OnePoint.some (g z) = e z :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toPartialHomeomorph_right_inv
      OnePoint.some (hrange hz)
  have hmap : MapsTo e {y}ᶜ c.symm.source := by
    intro z hz
    simpa [c] using hrange hz
  refine ⟨g, ?_, ?_, hgval⟩
  · exact c.symm.continuousOn.comp e.continuous.continuousOn hmap
  · intro z hz
    constructor
    · intro hgzero
      apply e.injective
      rw [← hgval z hz, hgzero, hex]
    · intro hzx
      apply OnePoint.coe_injective
      rw [hgval z hz, hzx, hex]

end HolomorphicAnosov

