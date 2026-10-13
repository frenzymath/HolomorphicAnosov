import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.HolomorphicBijOnHomeomorph
open Set
noncomputable section
namespace HolomorphicAnosov.Analysis
/-- A holomorphic bijection between open plane regions has nonzero derivative:
its subtype homeomorphism gives an open coordinate homeomorphism, to which the
literal inverse differentiation theorem applies. -/
theorem deriv_ne_zero_bijOn {D Q : Set ℂ} (hD : IsOpen D) (hQ : IsOpen Q)
    {φ : ℂ → ℂ} (hhol : DifferentiableOn ℂ φ D) (hbij : BijOn φ D Q)
    (z : ℂ) (hz : z ∈ D) : deriv φ z ≠ 0 := by
  obtain ⟨e, he⟩ := exists_homeomorph_eq_holomorphic_bijOn hD hhol hbij
  let p := hbij.toPartialEquiv φ D Q
  have heq : p.source.domRestrict p = (Subtype.val : Q → ℂ) ∘ e := by
    funext x
    exact (he x).symm
  have hop : IsOpenMap (p.source.domRestrict p) := by
    rw [heq]
    exact hQ.isOpenEmbedding_subtypeVal.isOpenMap.comp e.isOpenMap
  let E := OpenPartialHomeomorph.ofContinuousOpenRestrict p hhol.continuousOn hop hD
  have hi := (Complex.coordinateInverseDeriv E hhol (hbij.mapsTo hz)).1
  have hf : (E : ℂ → ℂ) = φ := rfl
  have hinv : E.symm (φ z) = z := E.left_inv hz
  simpa [hf, hinv] using hi
end HolomorphicAnosov.Analysis

