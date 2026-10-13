import HolomorphicAnosov.Topology.GoodPairCollapse
import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.IntegralReducedSingularHomology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.RadialCollar_norm

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HolomorphicAnosov.Topology.Homology

/-- The source disk boundary is a strong deformation retract of its genuine
open radial collar. No local compactness or positive dimension assumption is
needed for this formula; nonemptiness is supplied separately in the disk-pair
application. Source: Hatcher Corollary 2.14, radial good-pair verification. -/
def diskBoundaryCollarRetract {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    let D := {x : E // ‖x‖ ≤ 1}
    let A : Set D := {x | ‖x.val‖ = 1}
    let V : Set D := {x | (1 : ℝ) / 2 < ‖x.val‖}
    let hAV : A ⊆ V := fun x hx ↦ by change (1 : ℝ) / 2 < ‖x.val‖; rw [hx]; norm_num
    HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV := by
  dsimp only
  let D := {x : E // ‖x‖ ≤ 1}
  let A : Set D := {x | ‖x.val‖ = 1}
  let V : Set D := {x | (1 : ℝ) / 2 < ‖x.val‖}
  have hpos (x : V) : 0 < ‖x.val.val‖ := lt_trans (by norm_num) x.property
  let ret : C(V, A) := {
    toFun := fun x ↦ ⟨⟨‖x.val.val‖⁻¹ • x.val.val, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos x)),
        inv_mul_cancel₀ (hpos x).ne']⟩, by
      change ‖‖x.val.val‖⁻¹ • x.val.val‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos x)),
        inv_mul_cancel₀ (hpos x).ne']⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact ((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
        (fun x ↦ (hpos x).ne')).smul (continuous_subtype_val.comp continuous_subtype_val) }
  refine { retraction := ret, retraction_inclusion := ?_, homotopy := ?_ }
  · ext x
    change ‖x.val.val‖⁻¹ • x.val.val = x.val.val
    have hx : ‖x.val.val‖ = 1 := x.property
    simp [hx]
  · refine {
      toFun := fun p ↦ ⟨⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) / ‖p.2.val.val‖) • p.2.val.val,
        ?_⟩, ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
    · rw [radialCollar_norm _ (hpos p.2)]
      have ht0 := p.1.property.1
      have ht1 := p.1.property.2
      have hx := p.2.val.property
      nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hx)]
    · change (1 : ℝ) / 2 < ‖((1 - (p.1 : ℝ)) +
        (p.1 : ℝ) / ‖p.2.val.val‖) • p.2.val.val‖
      rw [radialCollar_norm _ (hpos p.2)]
      have ht0 := p.1.property.1
      have ht1 := p.1.property.2
      have hx : (1 : ℝ) / 2 < ‖p.2.val.val‖ := p.2.property
      have hd := p.2.val.property
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hd)]
    · apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      have hc : Continuous (fun p : unitInterval × V ↦ (p.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      have hx : Continuous (fun p : unitInterval × V ↦ p.2.val.val) :=
        continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
      exact ((continuous_const.sub hc).add (hc.div hx.norm
        (fun p ↦ (hpos p.2).ne'))).smul hx
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      simp
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      change ((1 - (1 : ℝ)) + (1 : ℝ) / ‖x.val.val‖) • x.val.val =
        ‖x.val.val‖⁻¹ • x.val.val
      simp
    · intro t x hx
      apply Subtype.ext
      apply Subtype.ext
      change ‖x.val.val‖ = 1 at hx
      change ((1 - (t : ℝ)) + (t : ℝ) / ‖x.val.val‖) • x.val.val = x.val.val
      simp [hx]

end HolomorphicAnosov.Topology.Homology
