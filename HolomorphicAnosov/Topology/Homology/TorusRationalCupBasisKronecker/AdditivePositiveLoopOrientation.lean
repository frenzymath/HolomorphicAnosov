import HolomorphicAnosov.Topology.CircleSingularCohomologyWinding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.AdditivePositiveLoop

open CategoryTheory
noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The quotient-circle homeomorphism sends this particular loop to the positive complex-circle
loop, fixing the orientation before any homology transfer. -/
theorem additivePositiveLoop_orientation :
    additivePositiveLoop ≫ (TopCat.isoOfHomeo (AddCircle.homeomorphCircle (T := (1 : ℝ))
      one_ne_zero)).hom = CircleSingularCohomology.positiveLoop := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro t
  change AddCircle.homeomorphCircle one_ne_zero ((t.down : ℝ) : UnitAddCircle) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  simp only [div_one]
  rfl

end HolomorphicAnosov.TorusRationalCupBasisKronecker
