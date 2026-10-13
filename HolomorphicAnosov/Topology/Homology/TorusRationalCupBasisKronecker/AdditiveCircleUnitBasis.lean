import HolomorphicAnosov.Topology.CircleSingularCohomologyWinding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.SingularPullbackHomeomorph
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.ZeroCochainEqOne
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.PullbackOneCochain
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.QuotientMapRepresentative

open CategoryTheory
open scoped Simplicial
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

set_option backward.isDefEq.respectTransparency false in
/-- The constant-one singular cocycle on the additive unit circle represents the vector of a singleton rational degree-zero cohomology basis.

Source: Hatcher, Algebraic Topology, circle cohomology pp197–201 and positive winding normalization Theorem 2A.1 pp166–167; Mathlib AddCircle.homeomorphCircle.

Transport the complex-circle degree-zero basis through the standard homeomorphism. Its normalized zero-cocycle is the constant-one cochain by equality on every zero-simplex. Pullback preserves the constant-one cochain; the chain-map law supplies its cycle proof, and the quotient representative equation identifies the transported basis vector. -/
theorem additive_circle_unit_basis :
    ∃ B₀ : Module.Basis Unit ℚ
    (SingularCochain.cohomology ℚ (TopCat.of UnitAddCircle) 0),
    ∃ hu : SingularCochain.oneCochain ℚ (TopCat.of UnitAddCircle) ∈
      SingularCochain.cycles ℚ (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 0,
    B₀ () = SingularCochain.cocycleClass ℚ
      (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 0
      ⟨SingularCochain.oneCochain ℚ (TopCat.of UnitAddCircle), hu⟩ := by
  classical
  obtain ⟨zc, ac, uc, up, B₁, Bc1, Bc0, Bp, hz₀, hB₁, hBc1, hBc0,
      hBp, hu, hup, hEval₀, huniq, hz₂, hzp, hconst, hsq⟩ :=
    CircleSingularCohomology.circle_singular_cohomology_winding ℚ
  let e : UnitAddCircle ≃ₜ Circle :=
    AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let f : TopCat.of UnitAddCircle ⟶ CircleSingularCohomology.circleSpace :=
    (TopCat.isoOfHomeo e).hom
  let E₀ := singularPullbackHomeomorph
    (X := TopCat.of UnitAddCircle) (Y := CircleSingularCohomology.circleSpace) e 0
  have hone : (SingularCochain.pullback ℚ f).f 0 uc.val =
      SingularCochain.oneCochain ℚ (TopCat.of UnitAddCircle) := by
    rw [zeroCochain_eq_one _ uc.val hu]
    exact pullback_oneCochain _
  have hcycle : SingularCochain.oneCochain ℚ (TopCat.of UnitAddCircle) ∈
      SingularCochain.cycles ℚ (SingularCochain.complex ℚ (TopCat.of UnitAddCircle)) 0 :=
    hone ▸ FieldChainKronecker.map_cycle_mem (SingularCochain.pullback ℚ f) 0 uc
  refine ⟨Bc0.map E₀, hcycle, ?_⟩
  rw [Module.Basis.map_apply, hBc0]
  exact quotient_map_representative (SingularCochain.pullback ℚ f) 0 uc
    ⟨_, hcycle⟩ hone

end HolomorphicAnosov.TorusRationalCupBasisKronecker
