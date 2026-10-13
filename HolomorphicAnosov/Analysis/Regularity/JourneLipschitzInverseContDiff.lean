import HolomorphicAnosov.Analysis.Regularity.JourneOpenPartialInverseAntiLipschitz
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
namespace HolomorphicAnosov
open Set

/-- A C^n partial homeomorphism between equal-dimensional finite real vector spaces has a C^n inverse on any open receiving domain where that inverse is Lipschitz. -/
theorem contDiffOn_inverse_of_lipschitzOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (e : OpenPartialHomeomorph E F) {n : ℕ} (hn : 1 ≤ n)
    (he : ContDiffOn ℝ n e e.source)
    {V : Set F} (hV : IsOpen V) (hsub : V ⊆ e.target)
    {K : ℝ} (hLip : ∀ u ∈ V, ∀ v ∈ V,
      ‖e.symm u - e.symm v‖ ≤ K * ‖u - v‖) :
    ContDiffOn ℝ n e.symm V := by
  intro y hy
  let x := e.symm y
  have hx : x ∈ e.source := e.map_target (hsub hy)
  have hxy : e x = y := e.right_inv (hsub hy)
  have hsmooth : ContDiffAt ℝ n e x :=
    (he x hx).contDiffAt (e.open_source.mem_nhds hx)
  have hn' : (n : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hd : HasFDerivAt e (fderiv ℝ e x) x :=
    (hsmooth.differentiableAt hn').hasFDerivAt
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hV y hy
  have hball' : Metric.ball (e x) ρ ⊆ V := by simpa only [hxy] using hball
  have hlower := hasFDerivAt_norm_lower_of_openPartialHomeomorph e hx hρ
    (hball'.trans hsub) (fun u hu v hv ↦ hLip u (hball' hu) v (hball' hv)) rfl hd
  have hinj : Function.Injective (fderiv ℝ e x).toLinearMap := by
    intro u v huv
    have huv' : (fderiv ℝ e x) u = (fderiv ℝ e x) v := huv
    have hzero : (fderiv ℝ e x) (u - v) = 0 := by rw [map_sub, huv', sub_self]
    have h := hlower (u - v)
    rw [hzero, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  let A : E ≃L[ℝ] F :=
    ((fderiv ℝ e x).toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
  have hdA : HasFDerivAt e A.toContinuousLinearMap x := by
    exact hd
  exact (e.contDiffAt_symm (hsub hy) (f₀' := A) hdA hsmooth).contDiffWithinAt

end HolomorphicAnosov
