import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! A smooth equivalence with injective derivatives between real manifolds of equal dimension has a
smooth inverse. (Zhang, p. 13) -/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- A smooth equivalence from a real vector space to a complex manifold viewed as real has a smooth
inverse when its derivatives are injective and the real dimensions agree. (Zhang, p. 13) -/
theorem real_equiv_inverse_contMDiff
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {d : ℕ} {M : Type v} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ (ComplexModel d))
    (e : V ≃ M)
    (hs : ContMDiff (modelWithCornersSelf ℝ V) (realModel d) ∞ e)
    (hi : ∀ a, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ V) (realModel d) e a)) :
    ContMDiff (realModel d) (modelWithCornersSelf ℝ V) ∞ e.symm := by
  let o : V → M := e
  have hs : ContMDiff (modelWithCornersSelf ℝ V) (realModel d) ∞ o := hs
  intro y
  let a : V := e.symm y
  have hay : o a = y := e.apply_symm_apply y
  let ψ := extChartAt (realModel d) y
  let q : V → ComplexModel d := ψ ∘ o
  have hq : ContDiffAt ℝ ∞ q a := by
    apply ContMDiffAt.contDiffAt
    exact (contMDiffAt_extChartAt (I := realModel d) (n := ∞) (x := y)).comp_of_eq
      (hs a) hay
  have hder : fderiv ℝ q a =
      mfderiv (modelWithCornersSelf ℝ V) (realModel d) o a := by
    have hh := mfderiv_comp_of_eq (I := modelWithCornersSelf ℝ V)
      (I' := realModel d) (I'' := modelWithCornersSelf ℝ (ComplexModel d)) (x := a)
      ((contMDiffAt_extChartAt (I := realModel d) (n := ∞) (x := y)).mdifferentiableAt
        (by simp)) ((hs a).mdifferentiableAt (by simp)) hay
    rw [hay, mfderiv_eq_fderiv, mfderiv_extChartAt_self] at hh
    erw [ContinuousLinearMap.id_comp] at hh
    exact hh
  have hqi : Function.Injective (fderiv ℝ q a) := by rw [hder]; exact hi a
  let L : V ≃L[ℝ] ComplexModel d :=
    (fderiv ℝ q a).toLinearMap.linearEquivOfInjective hqi hdim |>.toContinuousLinearEquiv
  have hL : HasFDerivAt q (L : V →L[ℝ] ComplexModel d) a :=
    hq.differentiableAt (by simp) |>.hasFDerivAt
  let H := hq.toOpenPartialHomeomorph q hL (by simp)
  have hH : q a ∈ H.target := hq.image_mem_toOpenPartialHomeomorph_target hL (by simp)
  have hHa : H.symm (q a) = a := hq.localInverse_apply_image hL (by simp)
  have hHs : ContDiffAt ℝ ∞ H.symm (q a) := hq.to_localInverse hL (by simp)
  apply contMDiffAt_iff_source.mpr
  have heq : (e.symm ∘ ψ.symm) =ᶠ[nhds (ψ y)] H.symm := by
    have hb : ψ y = q a := by change ψ y = ψ (o a); rw [hay]
    have htarget : ∀ᶠ b in nhds (ψ y), b ∈ H.target := by
      rw [hb]; exact H.open_target.mem_nhds hH
    have hψtarget : ∀ᶠ b in nhds (ψ y), b ∈ ψ.target := by
      exact extChartAt_target_mem_nhds (I := realModel d) y
    have horbit : ∀ᶠ b in nhds (ψ y), o (H.symm b) ∈ ψ.source := by
      have hc : ContinuousAt (o ∘ H.symm) (ψ y) :=
        hs.continuous.continuousAt.comp (by rw [hb]; exact hHs.continuousAt)
      apply hc.preimage_mem_nhds
      have hcval : o (H.symm (ψ y)) = y := by rw [hb, hHa, hay]
      change ψ.source ∈ nhds (o (H.symm (ψ y)))
      rw [hcval]
      exact extChartAt_source_mem_nhds y
    filter_upwards [htarget, hψtarget, horbit] with b hb hψb hob
    apply e.injective
    change o (e.symm (ψ.symm b)) = o (H.symm b)
    have heinverse : o (e.symm (ψ.symm b)) = ψ.symm b := e.apply_symm_apply _
    rw [heinverse]
    exact (congrArg ψ.symm (H.right_inv hb)).symm.trans (ψ.left_inv hob)
  have hcoords : ContDiffAt ℝ ∞ (e.symm ∘ ψ.symm) (ψ y) := by
    have hb : ψ y = q a := by change ψ y = ψ (o a); rw [hay]
    rw [← hb] at hHs
    exact hHs.congr_of_eventuallyEq heq
  simpa [ψ, realModel] using hcoords.contMDiffAt.contMDiffWithinAt

end HolomorphicAnosov
