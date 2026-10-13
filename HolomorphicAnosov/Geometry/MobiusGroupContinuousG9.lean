import HolomorphicAnosov.Geometry.MobiusGroupCarrierG9
import HolomorphicAnosov.Geometry.NativeProjectiveLineTopology
import HolomorphicAnosov.Geometry.ComplexMobiusContinuousG9

noncomputable section
namespace HolomorphicAnosov
open Ghys

/-- Every Möbius transformation of the one-point compactification of `ℂ` is continuous. -/
theorem mobiusGroup_continuous_apply (g : MobiusGroup) :
    Continuous g.apply := by
  let e := NativeProjectiveTopology.nativeProjectiveLineHomeomorphOnePoint
  let h := mobiusGroupToComplexMobius g
  have he_inv : (e.symm : OnePoint ℂ → ComplexProjectiveLine) =
      (OnePoint.equivProjectivization ℂ) := by rfl
  have he_fwd : (e : ComplexProjectiveLine → OnePoint ℂ) =
      (OnePoint.equivProjectivization ℂ).symm := by rfl
  have heq : g.apply = fun z ↦ e (h.apply (e.symm z)) := by
    funext z
    have hh := mobiusGroupToComplexMobius_apply g (e.symm z)
    rw [he_inv] at hh
    rw [he_fwd]
    apply (OnePoint.equivProjectivization ℂ).injective
    rw [Equiv.apply_symm_apply]
    simpa only [h, he_inv, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hh.symm
  rw [heq]
  exact e.continuous.comp (h.continuous_apply.comp e.symm.continuous)

end HolomorphicAnosov
