import HolomorphicAnosov.Paper.Ghys.ProjectiveLocalGermsEffectiveCocycle
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-! This file relates the homogeneous projective-line action of complex Möbius transformations to the effective action on the one-point compactification.
-/

noncomputable section

namespace HolomorphicAnosov
open Ghys

/-- The effective one-point permutation associated with a native homogeneous Möbius transformation is well defined. -/
def complexMobiusToMobiusGroup (g : ComplexMobiusTransformation) : MobiusGroup :=
  let m := Classical.choose g.property
  show (MulAction.toPermHom (GL (Fin 2) ℂ) (OnePoint ℂ)).range from
    ⟨MulAction.toPerm m, ⟨m, by rfl⟩⟩

/-- The native homogeneous action and the effective one-point action are intertwined by projectivization. -/
theorem complexMobiusToMobiusGroup_intertwines
    (g : ComplexMobiusTransformation) (p : ComplexProjectiveLine) :
    (OnePoint.equivProjectivization ℂ).symm (g.apply p) =
      Ghys.MobiusGroup.apply (complexMobiusToMobiusGroup g)
        ((OnePoint.equivProjectivization ℂ).symm
          (show Projectivization ℂ (Fin 2 → ℂ) from p)) := by
  apply (OnePoint.equivProjectivization ℂ).injective
  simp only [Equiv.apply_symm_apply]
  change g.val p = (OnePoint.equivProjectivization ℂ)
    ((Classical.choose g.property) • ((OnePoint.equivProjectivization ℂ).symm p))
  rw [OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply]
  exact Classical.choose_spec g.property p

/-- The finite affine representative agrees with the finite point in the one-point compactification under projectivization. -/
theorem complexProjectiveLineFinite_to_onePoint (z : ℂ) :
    (OnePoint.equivProjectivization ℂ).symm (complexProjectiveLineFinite z) =
      (z : OnePoint ℂ) := by
  unfold complexProjectiveLineFinite complexProjectiveLineChartInv
    complexProjectiveLineMk
  rw [OnePoint.equivProjectivization_symm_apply_mk]
  simp [complexProjectiveLineChartVector]

end HolomorphicAnosov
