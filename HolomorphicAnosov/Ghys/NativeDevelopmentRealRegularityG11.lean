import HolomorphicAnosov.Ghys.RealMetricAffinePlaque
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

noncomputable section
open Set Filter _root_.Topology
open scoped Manifold ContDiff
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace
universe u

/-- A map with invertible affine germs in a native leaf affine atlas is real smooth and its real derivative into the complex plane is injective at every point. Source: Ghys (1995), §3 pp.590–593. -/
lemma native_development_real_regular
    {d : ℕ} {M L : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace L] [ChartedSpace (Fin 2 → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ L]
    [ChartedSpace ℂ L] [IsManifold 𝓘(ℂ) ∞ L]
    {V : RealTangentDistribution (realModel d) M}
    (N : HPS.NativeLeaf (r := 2) V L)
    (hhol : ContMDiff 𝓘(ℂ) (complexModel d) ∞ N.inclusion)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) N.inclusion x))
    (A : ComplexAffineAtlas L) (D : L → ℂ)
    (hD : ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y)) :
    ContMDiff 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ D ∧
      ∀ p, Function.Injective (mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p) := by
  have hpoint (p : L) : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ D p ∧
      Function.Injective (mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p) := by
    obtain ⟨c, hc, hp⟩ := A.cover p
    have hcmax := (isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas L c).mp
      (A.holomorphic c hc)
    obtain ⟨hcr, hcir⟩ := native_holomorphic_chart_real_smooth N hhol hinj c
      (contMDiffOn_of_mem_maximalAtlas hcmax) (contMDiffOn_symm_of_mem_maximalAtlas hcmax)
    obtain ⟨b, hb⟩ := hD c hc p hp
    have hcp := hcr.contMDiffAt (c.open_source.mem_nhds hp)
    have hbcont : ContDiff ℝ ∞ (fun z : ℂ ↦ b.slope * z + b.translation) := by fun_prop
    have hDC : ContMDiffAt 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ D p :=
      ((contMDiff_iff_contDiff.mpr hbcont).contMDiffAt.comp p hcp).congr_of_eventuallyEq hb
    refine ⟨hDC, ?_⟩
    have hcd : c.MDifferentiable 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) :=
      ⟨hcr.mdifferentiableOn (by simp), hcir.mdifferentiableOn (by simp)⟩
    have hder (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) p) :
        mvfderiv 𝓘(ℝ, Fin 2 → ℝ) D p v =
          b.slope * mvfderiv 𝓘(ℝ, Fin 2 → ℝ) c p v :=
      real_chart_affine_unit_derivative b.slope b.translation
        (hcp.mdifferentiableAt (by simp)) (hasDerivAt_id (c p)) hb v
    intro v w hvw
    rw [hder, hder] at hvw
    apply (hcd.mfderiv_bijective hp).injective
    apply (tangentSpaceCastModel 𝓘(ℝ, ℂ) (c p)).injective
    exact mul_left_cancel₀ b.slope_ne_zero hvw
  exact ⟨fun p ↦ (hpoint p).1, fun p ↦ (hpoint p).2⟩
end HolomorphicAnosov.Ghys
