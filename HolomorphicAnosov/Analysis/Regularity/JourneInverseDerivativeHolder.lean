import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

noncomputable section
namespace HolomorphicAnosov
open Set Filter
open scoped Topology _root_.Topology

/-- The inverse derivative inherits a quantitative Hölder estimate on its
actual receiving domain. Differentiate the two local inverse identities, use
R−S=R(Q−P)S for the two inverse derivatives, bound their norms by the inverse
Lipschitz constant, and transfer the forward derivative modulus along the
same Lipschitz inverse. The constant is K² C K^α. -/
theorem inverse_fderiv_holder_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph E F) {V : Set F}
    (hV : IsOpen V) (hsub : V ⊆ e.target)
    (he : DifferentiableOn ℝ e e.source)
    (hi : DifferentiableOn ℝ e.symm V)
    {K C α : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hLip : ∀ u ∈ V, ∀ v ∈ V, ‖e.symm u - e.symm v‖ ≤ K * ‖u - v‖)
    (hD : ∀ u ∈ V, ∀ v ∈ V,
      ‖fderiv ℝ e (e.symm u) - fderiv ℝ e (e.symm v)‖ ≤
        C * ‖e.symm u - e.symm v‖ ^ α) :
    ∀ u ∈ V, ∀ v ∈ V,
      ‖fderiv ℝ e.symm u - fderiv ℝ e.symm v‖ ≤
        (K * K * C * K ^ α) * ‖u - v‖ ^ α := by
  have hd (y : F) (hy : y ∈ V) : DifferentiableAt ℝ e (e.symm y) :=
    (he _ (e.map_target (hsub hy))).differentiableAt
      (e.open_source.mem_nhds (e.map_target (hsub hy)))
  have hid (y : F) (hy : y ∈ V) : DifferentiableAt ℝ e.symm y :=
    (hi y hy).differentiableAt (hV.mem_nhds hy)
  have hleft (y : F) (hy : y ∈ V) :
      (fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)) =
        ContinuousLinearMap.id ℝ E := by
    have hi' := (hid y hy).hasFDerivAt
    rw [← e.right_inv (hsub hy)] at hi'
    have hc := hi'.comp (e.symm y) (hd y hy).hasFDerivAt
    rw [e.right_inv (hsub hy)] at hc
    apply HasFDerivAt.unique _ (hasFDerivAt_id (e.symm y))
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds (e.map_target (hsub hy))] with z hz
    exact (e.left_inv hz).symm
  have hright (y : F) (hy : y ∈ V) :
      (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
        ContinuousLinearMap.id ℝ F := by
    have hc := (hd y hy).hasFDerivAt.comp y (hid y hy).hasFDerivAt
    apply HasFDerivAt.unique _ (hasFDerivAt_id y)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hy] with z hz
    exact (e.right_inv (hsub hz)).symm
  have hnorm (y : F) (hy : y ∈ V) : ‖fderiv ℝ e.symm y‖ ≤ K := by
    exact norm_fderiv_le_of_lipschitzOn ℝ (hV.mem_nhds hy)
      (show LipschitzOnWith ⟨K, hK⟩ e.symm V from
        lipschitzOnWith_iff_norm_sub_le.mpr hLip)
  intro u hu v hv
  let R := fderiv ℝ e.symm u
  let S := fderiv ℝ e.symm v
  let P := fderiv ℝ e (e.symm u)
  let Q := fderiv ℝ e (e.symm v)
  have hidiff : R - S = (R.comp (Q - P)).comp S := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_assoc, show Q.comp S = ContinuousLinearMap.id ℝ F from hright v hv,
      show R.comp P = ContinuousLinearMap.id ℝ E from hleft u hu]
    simp
  have hPQ : ‖Q - P‖ ≤ C * ‖e.symm u - e.symm v‖ ^ α := by
    rw [norm_sub_rev]
    exact hD u hu v hv
  calc
    ‖fderiv ℝ e.symm u - fderiv ℝ e.symm v‖ = ‖(R.comp (Q - P)).comp S‖ := by rw [← hidiff]
    _ ≤ (‖R‖ * ‖Q - P‖) * ‖S‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg S))
    _ ≤ (K * (C * (K * ‖u - v‖) ^ α)) * K := by
      gcongr
      · exact hnorm u hu
      · exact hPQ.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hLip u hu v hv) hα) hC)
      · exact hnorm v hv
    _ = (K * K * C * K ^ α) * ‖u - v‖ ^ α := by
      rw [Real.mul_rpow hK (norm_nonneg _)]
      ring

end HolomorphicAnosov
