import HolomorphicAnosov.Topology.CircleSingularCohomologyWinding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackHomeomorph

open CategoryTheory
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- Rational singular cohomology of the additive unit circle has singleton bases in degrees zero and one and is zero in degrees at least two.

Source: Hatcher, Algebraic Topology, circle cohomology pp197–201 and positive winding normalization Theorem 2A.1 pp166–167; Mathlib AddCircle.homeomorphCircle.

Transport the degree-zero and degree-one complex-circle bases through the standard homeomorphism. In every higher degree the inverse cohomology equivalence is injective into a zero module, so all additive-circle classes coincide. -/
theorem additive_circle_profile :
    ∃ (_B₀ : Module.Basis Unit ℚ
    (SingularCochain.cohomology ℚ (TopCat.of UnitAddCircle) 0))
    (_B₁ : Module.Basis Unit ℚ
      (SingularCochain.cohomology ℚ (TopCat.of UnitAddCircle) 1)),
    (∀ q : ℕ, 2 ≤ q →
      Subsingleton (SingularCochain.cohomology ℚ (TopCat.of UnitAddCircle) q)) := by
  classical
  obtain ⟨zc, ac, uc, up, B₁c, Bc1, Bc0, Bp, hz₀, hB₁, hBc1, hBc0,
      hBp, hu, hup, hEval₀, huniq, hz₂, hzp, hconst, hsq⟩ :=
    CircleSingularCohomology.circle_singular_cohomology_winding ℚ
  let e : UnitAddCircle ≃ₜ Circle :=
    AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let E₀ := singularPullbackHomeomorph
    (X := TopCat.of UnitAddCircle) (Y := CircleSingularCohomology.circleSpace) e 0
  let E₁ := singularPullbackHomeomorph
    (X := TopCat.of UnitAddCircle) (Y := CircleSingularCohomology.circleSpace) e 1
  refine ⟨(Bc0.map E₀), (Bc1.map E₁), ?_⟩
  intro q hq
  let Eq := singularPullbackHomeomorph
    (X := TopCat.of UnitAddCircle) (Y := CircleSingularCohomology.circleSpace) e q
  have := hz₂ q hq
  exact ⟨fun x y ↦ Eq.symm.injective (Subsingleton.elim _ _)⟩

end HolomorphicAnosov.TorusRationalCupBasisKronecker
