import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Continuous evaluation of scalar cotangent families on the real tangent bundle. (Zhang, Lemma
2.2, p. 5) -/

open Set TopologicalSpace Bundle
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- A scalar cotangent family with continuous inverse-chart coefficients has continuous evaluation
on the real tangent bundle. (Zhang, Lemma 2.2, p. 5) -/
theorem continuous_scalar_tangent_evaluation
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hα : ∀ (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContinuousOn (fun z ↦ (α (c.symm z)).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)) c.target) :
    Continuous (fun z : TangentBundle (realModel d) X ↦ α z.proj z.snd) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let e := chartAt (ComplexModel d) z.proj
  let t := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) z.proj
  let A : Set (TangentBundle (realModel d) X) := {w | w.proj ∈ e.source}
  have hA : IsOpen A := e.open_source.preimage
    (FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (realModel d)))
  have hzA : z ∈ A := mem_chart_source _ _
  have ht : Continuous (fun w : A ↦ t w.val) :=
    t.continuousOn.comp_continuous continuous_subtype_val (fun w ↦ w.property)
  have hbase : Continuous (fun w : A ↦ e w.val.proj) :=
    e.continuousOn.comp_continuous
      ((FiberBundle.continuous_proj (ComplexModel d) (TangentSpace (realModel d))).comp
        continuous_subtype_val) (fun w ↦ w.property)
  have hcoef := (hα e (IsManifold.chart_mem_maximalAtlas _)).comp_continuous
    hbase (fun w ↦ e.map_source w.property)
  have heval := hcoef.clm_apply (continuous_snd.comp ht)
  have hn : Continuous (fun w : A ↦ α w.val.proj w.val.snd) := by
    apply heval.congr
    intro w
    change α (e.symm (e w.val.proj))
      (mfderiv (realModel d) (realModel d) e.symm (e w.val.proj) (t w.val).2) = _
    rw [e.left_inv w.property]
    have hinv := TangentBundle.symmL_trivializationAt (I := realModel d)
      (x₀ := z.proj) (x := w.val.proj) w.property
    simp only [realModel, modelWithCornersSelf_coe, Set.range_id,
      mfderivWithin_univ] at hinv
    change t.symmL ℝ w.val.proj =
      mfderiv (realModel d) (realModel d) e.symm (e w.val.proj) at hinv
    have hid : t.symmL ℝ w.val.proj (t w.val).2 = w.val.snd := by
      rw [Trivialization.symmL_apply (R := ℝ) t w.property]
      exact Trivialization.symm_apply_apply_mk t w.property w.val.snd
    have hinvv := congrArg (fun L ↦ L ((t w.val).2 : ComplexModel d)) hinv
    exact congrArg (α w.val.proj) (hinvv.symm.trans hid)
  exact (continuousOn_iff_continuous_domRestrict.mpr hn).continuousAt (hA.mem_nhds hzA)

end HolomorphicAnosov
