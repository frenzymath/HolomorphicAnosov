import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealVectorBundle
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealTangentSmooth
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.RealContMDiffOnMap

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle

attribute [local instance] complex_isManifold_real
universe u

set_option backward.isDefEq.respectTransparency false in
/-- A compact complex manifold admits a smooth Hermitian tangent metric. -/
theorem original_smooth_tangent_metric_exists {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsCompactComplexManifold d M] :
    ∃ g : HermitianTangentMetricCore d M, IsSmoothHermitianTangentMetric g := by
  let : IsManifold (realModel d) ∞ M := complex_isManifold_real d M
  let : VectorBundle ℝ (ComplexModel d) (fun x : M ↦ TangentSpace (complexModel d) x) :=
    real_vector_bundle
  let : ContMDiffVectorBundle ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (complexModel d) x) (realModel d) :=
    real_tangent_smooth
  obtain ⟨g, hp, _, _⟩ := smooth_complex_bundle_hermitian_metric
    (B := ComplexModel d) (M := M)
    (E := fun x : M ↦ TangentSpace (complexModel d) x) d
  refine ⟨g, ?_⟩
  intro e he i j
  have hframe (i : Fin d) :
      ContMDiffOn (realModel d) ((realModel d).prod 𝓘(ℝ, ComplexModel d)) ∞
        (fun x ↦ TotalSpace.mk' (E := fun x : M ↦ TangentSpace (complexModel d) x)
          (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
    have hs := contMDiffOn_symm_of_mem_maximalAtlas he
    have htm := hs.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      e.open_target.uniqueMDiffOn
    have hinput : ContMDiffOn (complexModel d) ((complexModel d).tangent) ∞
        (fun x ↦ (tangentBundleModelSpaceHomeomorph (complexModel d)).symm
          (e x, Pi.single i 1)) e.source :=
      contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas he).prodMk_space contMDiffOn_const)
    have hc := htm.comp hinput (fun x hx ↦ e.map_source hx)
    have hc' : ContMDiffOn (complexModel d) ((complexModel d).prod 𝓘(ℂ, ComplexModel d)) ∞
        (fun x ↦ TotalSpace.mk' (E := fun x : M ↦ TangentSpace (complexModel d) x)
          (ComplexModel d) x (hermitianTangentChartFrame e (e x) i)) e.source := by
      apply hc.congr
      intro x hx
      simp only [Function.comp_apply, tangentBundleModelSpaceHomeomorph_coe_symm,
        tangentMapWithin]
      dsimp only [TotalSpace.toProd, Equiv.coe_fn_symm_mk]
      rw [mfderivWithin_eq_mfderiv (e.open_target.uniqueMDiffOn _ (e.map_source hx))
        (((hs _ (e.map_source hx)).contMDiffAt
          (e.open_target.mem_nhds (e.map_source hx))).mdifferentiableAt (by simp))]
      simp only [hermitianTangentChartFrame]
      apply TotalSpace.ext (e.left_inv hx).symm
      rfl
    intro x hx
    obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hc' x hx)
    exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  have hpair := hp e.source e.open_source
    (fun x ↦ hermitianTangentChartFrame e (e x) i)
    (fun x ↦ hermitianTangentChartFrame e (e x) j) (hframe i) (hframe j)
  have hinv := real_contMDiffOn_map (contMDiffOn_symm_of_mem_maximalAtlas he)
  have hcoeff := hpair.comp hinv (fun z hz ↦ e.map_target hz)
  have hc : ContMDiffOn 𝓘(ℝ, ComplexModel d) 𝓘(ℝ, ℂ) ∞
      (hermitianTangentChartCoefficient g e i j) e.target := by
    apply hcoeff.congr
    intro z hz
    simp only [Function.comp_apply,
      hermitianTangentChartCoefficient, hermitianTangentPairing]
    rw [e.right_inv hz]
  exact hc.contDiffOn


end HolomorphicAnosov.OneFormBundle
