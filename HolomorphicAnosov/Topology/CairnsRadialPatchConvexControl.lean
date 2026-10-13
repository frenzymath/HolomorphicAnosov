import HolomorphicAnosov.Topology.CairnsResidualStarRefinement
import Mathlib.Analysis.Convex.Basic

/-!
# Convex control of Cairns's prescribed radial patch

Source: Cairns (1951), §4, printed pp.863–864, equations (4.1)–(4.2) and
paragraph (A). The front map interpolates the prescribed boundary values on
its gap chords, and the patch map interpolates the target chord midpoint and
that target front. This module checks those exact formulas. The geometric
coverage and confinement of the source front are explicit hypotheses; their
proof is part of the convex-star construction, not asserted here.
-/

namespace HolomorphicAnosov.Topology.Plane

open Set CairnsStar CairnsRefinement

/-- Cairns §4 pp.863–864: the affine front extension followed by the radial
extension stays in every convex set containing the prescribed image arc.
The front consists of contacts in the given arc and points with front-chord
coordinates. The input point is a contact in that arc, the chord midpoint,
or a point with radial coordinates on this front.

Proof: the target midpoint is a convex combination of the two prescribed
endpoint values. A front contact has its prescribed value, and every other
front point is a convex combination of two prescribed arc values. Finally
the radial branch is a convex combination of the midpoint and a front value.
The coverage hypotheses exclude the zero-valued totalization branches.
This is exactly the two successive linear-extension steps of the source. -/
theorem cairns_radial_patch_convex_control
    {σ : Circle → ℂ} {a : Set ℂ} {gap : CairnsCircleGap}
    (b : StarChoice σ a gap) (h : range σ ≃ₜ Circle)
    (C : Set ℂ) (hC : Convex ℝ C)
    (hvalues : ∀ t : I, (h ⟨σ (gap.parameter t), ⟨gap.parameter t, rfl⟩⟩ : ℂ) ∈ C)
    (hcontacts : b.front ∩ range σ ⊆ σ '' range gap.parameter)
    (hfront : ∀ w ∈ b.front, w ∉ range σ → ∃ v, b.FrontCoordinate w v)
    (z : ℂ) (hzcontact : z ∈ range σ → z ∈ σ '' range gap.parameter)
    (hz : z ∈ range σ ∨ z = b.center ∨ ∃ w, b.RadialCoordinate z w) :
    b.patchMap h z ∈ C := by
  classical
  have hcontact (w : ℂ) (hw : w ∈ range σ) (harc : w ∈ σ '' range gap.parameter) :
      (h ⟨w, hw⟩ : ℂ) ∈ C := by
    obtain ⟨t, ⟨u, rfl⟩, rfl⟩ := harc
    exact hvalues u
  have hfirst : (h ⟨σ gap.first, ⟨gap.first, rfl⟩⟩ : ℂ) ∈ C := by
    simpa [CairnsCircleGap.parameter, CairnsCircleGap.first] using hvalues ⟨0, by simp⟩
  have hlast : (h ⟨σ gap.last, ⟨gap.last, rfl⟩⟩ : ℂ) ∈ C := by
    simpa [CairnsCircleGap.parameter, CairnsCircleGap.last] using hvalues ⟨1, by simp⟩
  have hcenter : b.targetCenter h ∈ C := by
    simpa [StarChoice.targetCenter, midpoint_eq_smul_add, Complex.real_smul,
      div_eq_mul_inv, add_mul, mul_add, mul_comm] using hC.midpoint_mem hfirst hlast
  have hfrontvalue (w : ℂ) (hw : w ∈ b.front) : b.frontMap h w ∈ C := by
    unfold StarChoice.frontMap
    split_ifs with hcurve hcoord
    · exact hcontact w hcurve (hcontacts ⟨hw, hcurve⟩)
    · let v := Classical.choose hcoord
      exact hC (hvalues v.1) (hvalues v.2.1) (sub_nonneg.mpr v.2.2.property.2)
        v.2.2.property.1 (sub_add_cancel 1 (v.2.2 : ℝ))
    · exact False.elim (hcoord (hfront w hw hcurve))
  unfold StarChoice.patchMap
  split_ifs with hcurve hmid hrad
  · exact hcontact z hcurve (hzcontact hcurve)
  · exact hcenter
  · let w := Classical.choose hrad
    have hw : b.RadialCoordinate z w := Classical.choose_spec hrad
    exact hC hcenter (hfrontvalue w.1 hw.1) (sub_nonneg.mpr w.2.property.2)
      w.2.property.1 (sub_add_cancel 1 (w.2 : ℝ))
  · exact False.elim (hz.elim hcurve (fun hrem ↦ hrem.elim hmid hrad))

end HolomorphicAnosov.Topology.Plane

