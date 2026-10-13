import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.SphereScale
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ReducedHomologyHomeomorphIso

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- Transport the complete profile through the literal radius homeomorphism.
This does not assert the unit-sphere calculation as an extra target premise:
it is the radius part of the source induction, separated for reuse internally. -/
theorem sphereScale_profile {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (htop : Nonempty (integralReducedSingularHomology
      (TopCat.of {x : E // ‖x‖ = 1}) k ≅ reducedSingularIntegralCoefficients))
    (hoff : ∀ q : ℕ, q ≠ k → IsZero (integralReducedSingularHomology
      (TopCat.of {x : E // ‖x‖ = 1}) q)) (r : ℝ) (hr : 0 < r) :
    Nonempty (integralReducedSingularHomology
      (TopCat.of {x : E // ‖x‖ = r}) k ≅ reducedSingularIntegralCoefficients) ∧
    (∀ q : ℕ, q ≠ k → IsZero (integralReducedSingularHomology
      (TopCat.of {x : E // ‖x‖ = r}) q)) ∧
    ∃ e : {x : E // ‖x‖ = 1} ≃ₜ {x : E // ‖x‖ = r},
      (∀ x, (e x).val = r • x.val) ∧
      (∀ y, (e.symm y).val = r⁻¹ • y.val) ∧
      ∀ q : ℕ, ∃ ι : integralReducedSingularHomology
          (TopCat.of {x : E // ‖x‖ = 1}) q ≅
          integralReducedSingularHomology (TopCat.of {x : E // ‖x‖ = r}) q,
        ι.hom = integralReducedSingularHomologyMap (TopCat.ofHom ⟨e, e.continuous⟩) q ∧
        ι.inv = integralReducedSingularHomologyMap
          (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) q := by
  let e := sphereScale r hr (E := E)
  obtain ⟨h⟩ := htop
  refine ⟨⟨(reducedHomologyHomeomorphIso e k).symm ≪≫ h⟩, ?_, e, ?_, ?_, ?_⟩
  · intro q hq
    exact IsZero.of_iso (hoff q hq) (reducedHomologyHomeomorphIso e q).symm
  · intro x
    rfl
  · intro y
    rfl
  · intro q
    exact ⟨reducedHomologyHomeomorphIso e q, rfl, rfl⟩

end HolomorphicAnosov.Topology.Homology
