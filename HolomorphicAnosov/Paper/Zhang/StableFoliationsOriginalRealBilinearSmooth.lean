import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.Basic
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinear
import HolomorphicAnosov.Paper.Zhang.StableFoliationsOriginalRealBilinearApply
import HolomorphicAnosov.Paper.Zhang.StableFoliationsRealInverseChartFrame
import HolomorphicAnosov.Paper.Zhang.StableFoliationsPairingInverseChartSmooth

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The real bilinear form associated to a smooth Hermitian metric is a smooth section of the real
tangent Hom bundle. -/
theorem originalRealBilinear_smooth {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h) :
    ContMDiff (realModel d)
      ((realModel d).prod 𝓘(ℝ, ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ)) ∞
      (fun x : M ↦ Bundle.TotalSpace.mk' (ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ)
        x (originalRealBilinear h x)) := by
  intro a
  rw [Bundle.contMDiffAt_section, contMDiffAt_iff_source]
  let e := chartAt (ComplexModel d) a
  have hc : ContDiffOn ℝ ∞ (fun z ↦
      (trivializationAt (ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace (realModel d) x →L[ℝ] TangentSpace (realModel d) x →L[ℝ] ℝ)
        a ⟨e.symm z, originalRealBilinear h (e.symm z)⟩).2) e.target := by
    apply contDiffOn_clm_apply.mpr
    intro v
    apply contDiffOn_clm_apply.mpr
    intro w
    have hs := Complex.reCLM.contDiff.comp_contDiffOn
      (pairing_inverse_chart_smooth h hh e (IsManifold.chart_mem_maximalAtlas a) v w)
    apply hs.congr
    intro z hz
    have hx : e.symm z ∈ e.source := e.map_target hz
    rw [hom_trivializationAt_apply]
    rw [inCoordinates_apply_eq₂]
    · simp only [Bundle.Trivial.fiberBundle_trivializationAt',
        Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]
      rw [← (trivializationAt (ComplexModel d) (TangentSpace (realModel d)) a).symmL_apply (R := ℝ) hx,
        ← (trivializationAt (ComplexModel d) (TangentSpace (realModel d)) a).symmL_apply (R := ℝ) hx]
      rw [real_inverse_chart_frame a _ hx v, real_inverse_chart_frame a _ hx w]
      have heq : chartAt (ComplexModel d) a (e.symm z) = z := e.right_inv hz
      simp only [originalRealBilinear_apply, hermitianTangentRealPairing]
      rw [heq]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      rfl
    · exact hx
    · exact hx
    · simp
  have hp := hc.contDiffAt (e.open_target.mem_nhds (e.map_source (mem_chart_source _ _)))
  have hrange : Set.range (realModel d) = Set.univ := by simp [realModel]
  rw [hrange, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  exact hp

end StableFoliationsSupport
end HolomorphicAnosov
