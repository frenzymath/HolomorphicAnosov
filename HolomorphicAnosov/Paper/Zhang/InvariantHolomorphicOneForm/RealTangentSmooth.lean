import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealVectorBundle
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealContMDiffOn

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle

attribute [local instance] complex_isManifold_real
universe u

/-- The complex tangent bundle of a smooth complex manifold is a smooth real vector bundle after
restriction of scalars. -/
theorem real_tangent_smooth {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M] :
    let _ : VectorBundle ℝ (ComplexModel d) (fun x : M ↦ TangentSpace (complexModel d) x) :=
      real_vector_bundle
    ContMDiffVectorBundle ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (complexModel d) x) (realModel d) := by
  let : VectorBundle ℝ (ComplexModel d) (fun x : M ↦ TangentSpace (complexModel d) x) :=
    real_vector_bundle
  refine ⟨?_⟩
  intro e e' he he'
  have hc := real_contMDiffOn (contMDiffOn_coordChangeL
    (IB := complexModel d) (n := ∞) e e')
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel d)
    (ComplexModel d) ℝ ℝ).contMDiff.comp_contMDiffOn hc
  apply hr.congr
  intro x hx
  simp only [ContinuousLinearMap.coe_restrict_scalarsL', Function.comp_apply]
  apply ContinuousLinearMap.ext
  intro v
  change e.coordChangeL ℝ e' x v = e.coordChangeL ℂ e' x v
  rw [Trivialization.coordChangeL_apply (R := ℝ) e e' hx,
    Trivialization.coordChangeL_apply (R := ℂ) e e' hx]


end HolomorphicAnosov.OneFormBundle
