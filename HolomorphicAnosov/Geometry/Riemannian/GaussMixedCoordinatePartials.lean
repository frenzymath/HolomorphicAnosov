import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The ordinary mixed coordinate partials of a C² map commute. -/

open scoped Topology _root_.Topology

namespace HolomorphicAnosov

set_option maxHeartbeats 600000 in
/-- The ordinary mixed partial derivatives of a map that is C² at the specified point commute.
(Gallier–Quaintance, Prop. 16.7, p.451) -/
theorem gauss_mixed_coordinate_partials_public
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {t s : ℝ} (hf : ContDiffAt ℝ 2 f (t, s)) :
    deriv (fun r ↦ deriv (fun q ↦ f (r, q)) s) t =
      deriv (fun q ↦ deriv (fun r ↦ f (r, q)) t) s := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) (t, s) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : ∀ᶠ z in 𝓝 (t, s), DifferentiableAt ℝ f z :=
    (hf.eventually (by norm_num)).mono fun z hz ↦ hz.differentiableAt (by norm_num)
  have ht : (fun r ↦ deriv (fun q ↦ f (r, q)) s) =ᶠ[𝓝 t]
      (fun r ↦ fderiv ℝ f (r, s) (0, 1)) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hnear] with r hr
    exact (hr.hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_const s r).prodMk (hasDerivAt_id s))).deriv
  have hs : (fun q ↦ deriv (fun r ↦ f (r, q)) t) =ᶠ[𝓝 s]
      (fun q ↦ fderiv ℝ f (t, q) (1, 0)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually hnear] with q hq
    exact (hq.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t q))).deriv
  rw [ht.deriv_eq, hs.deriv_eq]
  have htder := ((hd.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t s))).clm_apply
      (hasDerivAt_const t ((0, 1) : ℝ × ℝ))).deriv
  have hsder := ((hd.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_const s t).prodMk (hasDerivAt_id s))).clm_apply
      (hasDerivAt_const s ((1, 0) : ℝ × ℝ))).deriv
  simp only [Function.comp_apply, id_eq, map_zero, add_zero] at htder hsder
  rw [htder, hsder]
  exact hf.isSymmSndFDerivAt (by norm_num) (1, 0) (0, 1)

end HolomorphicAnosov
