import HolomorphicAnosov.Topology.EuclideanOpenDimensionInvariance
import HolomorphicAnosov.Topology.Homology.ModTwoPositiveSphereScale
import Mathlib.Topology.Homeomorph.Defs

namespace HolomorphicAnosov.Topology.Homology

noncomputable section

/-- Radial normalization of a punctured normed space to any positive-radius sphere.
This is the rescaled version of Hatcher's punctured radial map; it is used as
an explicit geometric map before the relative-homology argument. -/
noncomputable def positivePuncturedSphereMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) :
    C({x : E // x ≠ 0}, {x : E // ‖x‖ = r}) where
  toFun x := ⟨(r / ‖x.1‖) • x.1, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr (norm_pos_iff.mpr x.2))]
    field_simp [norm_ne_zero_iff.mpr x.2]
  ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hn : Continuous (fun x : {x : E // x ≠ 0} => ‖x.1‖) :=
      continuous_norm.comp continuous_subtype_val
    exact ((continuous_const.div hn (fun x => norm_ne_zero_iff.mpr x.2)).smul
      continuous_subtype_val)

/-- The punctured radial deformation is homotopy equivalent to every
positive-radius sphere, by composing the unit-sphere deformation with scalar
sphere transport. -/
noncomputable def positivePuncturedSphereHomotopyEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) :
    ContinuousMap.HomotopyEquiv {x : E // x ≠ 0} {x : E // ‖x‖ = r} :=
  HolomorphicAnosov.puncturedSphereHomotopyEquiv.trans
    (positiveSphereScaleHomeomorph r hr).toHomotopyEquiv

end
end HolomorphicAnosov.Topology.Homology
