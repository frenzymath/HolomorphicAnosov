import HolomorphicAnosov.Ghys.CurveJetReparametrizationData
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Rational source reparametrization of local holomorphic parametrization germs. (Ghys, §3 p.591)
-/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]
/-- Rational source reparametrization preserves admissibility of a curve germ. (Ghys, p.591) -/
theorem curve_germ_reparametrize_admissible (p : CurveJetReparametrization)
    (γ : CurveParamGerm L) : CurveGermAdmissible L (curveGermReparametrize L p γ.1) := by
  have hw : (p.omega : ℂ) ≠ 0 := Units.ne_zero p.omega
  let r : ℂ → ℂ := p.apply
  let s : ℂ → ℂ := fun w ↦ w / ((p.omega : ℂ) - p.mu * w)
  let U : Set ℂ := {z | 1 + p.mu * z ≠ 0}
  let V : Set ℂ := {w | (p.omega : ℂ) - p.mu * w ≠ 0}
  have hr : ContDiffOn ℂ ∞ r U :=
    (contDiffOn_const.mul contDiffOn_id).div
      (contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id)) (fun _ hz ↦ hz)
  have hs : ContDiffOn ℂ ∞ s V :=
    contDiffOn_id.div (contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id))
      (fun _ hw ↦ hw)
  have hdenr (z : ℂ) (hz : z ∈ U) :
      (p.omega : ℂ) - p.mu * r z = (p.omega : ℂ) / (1 + p.mu * z) := by
    dsimp [r, CurveJetReparametrization.apply]
    field_simp [show 1 + p.mu * z ≠ 0 from hz]
    ring
  have hdens (w : ℂ) (hw' : w ∈ V) :
      1 + p.mu * s w = (p.omega : ℂ) / ((p.omega : ℂ) - p.mu * w) := by
    dsimp [s]
    field_simp [show (p.omega : ℂ) - p.mu * w ≠ 0 from hw']
    ring
  let e : OpenPartialHomeomorph ℂ ℂ :=
    { toFun := r
      invFun := s
      source := U
      target := V
      map_source' := fun z hz ↦ by
        change (p.omega : ℂ) - p.mu * r z ≠ 0
        rw [hdenr z hz]
        exact div_ne_zero hw hz
      map_target' := fun w hw' ↦ by
        change 1 + p.mu * s w ≠ 0
        rw [hdens w hw']
        exact div_ne_zero hw hw'
      left_inv' := fun z hz ↦ by
        change r z / ((p.omega : ℂ) - p.mu * r z) = z
        rw [hdenr z hz]
        dsimp [r, CurveJetReparametrization.apply]
        field_simp [hw, show 1 + p.mu * z ≠ 0 from hz]
        simpa [mul_comm] using mul_div_cancel_right₀ z hz
      right_inv' := fun w hw' ↦ by
        change (p.omega : ℂ) * s w / (1 + p.mu * s w) = w
        rw [hdens w hw']
        dsimp [s]
        field_simp [hw, show (p.omega : ℂ) - p.mu * w ≠ 0 from hw']
        simpa [mul_comm] using mul_div_cancel_right₀ w hw'
      open_source := isOpen_ne_fun (continuous_const.add (continuous_const.mul continuous_id))
        continuous_const
      open_target := isOpen_ne_fun (continuous_const.sub (continuous_const.mul continuous_id))
        continuous_const
      continuousOn_toFun := hr.continuousOn
      continuousOn_invFun := hs.continuousOn }
  obtain ⟨g, hg0, hg, hgs, hge⟩ := γ.2
  refine ⟨e.trans g, ?_, ?_, ?_, ?_⟩
  · exact ⟨by simp [e, U], by simpa [e, r, CurveJetReparametrization.apply] using hg0⟩
  · exact hg.comp ((contMDiffOn_iff_contDiffOn.mpr hr).mono inter_subset_left)
      (fun z hz ↦ hz.2)
  · exact (contMDiffOn_iff_contDiffOn.mpr hs).comp
      (hgs.mono inter_subset_left) (fun z hz ↦ hz.2)
  · simp only [curveGermReparametrize, ← hge, Germ.coe_compTendsto]
    rfl

/-- The admissible curve germ obtained by rational source reparametrization. (Ghys, p.591) -/
def curveParamGermReparametrize (p : CurveJetReparametrization) (γ : CurveParamGerm L) :
    CurveParamGerm L :=
  ⟨curveGermReparametrize L p γ.1, curve_germ_reparametrize_admissible L p γ⟩


end HolomorphicAnosov.Ghys

#check @HolomorphicAnosov.Ghys.curve_germ_reparametrize_admissible
