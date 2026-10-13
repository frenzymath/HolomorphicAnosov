import HolomorphicAnosov.Geometry.SmoothMetricPullbackCore

noncomputable section
open Set Filter Bundle Bornology
open scoped Manifold ContDiff Topology ENNReal Bundle
namespace HolomorphicAnosov

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

/-! Pullback Riemannian metrics along immersions. -/

/-- A smooth map with injective differential pulls back the given smooth tensor on a finite-dimensional target to a smooth Riemannian tensor with the source's original tangent-fibre topology (Lee §11 pp.275–279 and Gallier–Quaintance Definition 14.4 p.415).-/
theorem immersion_riemannianMetric_exists
    (g : ContMDiffRiemannianMetric J ∞ F (TangentSpace J : N → Type _))
    (j : M → N) (hj : ContMDiff I J ∞ j)
    (hinj : ∀ x, Function.Injective (mfderiv I J j x)) :
    ∃ gM : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _),
      ∀ x v w, gM.inner x v w = g.inner (j x) (mfderiv I J j x v)
        (mfderiv I J j x w) := by
  let D := fun x ↦ mfderiv I J j x
  let q : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ := by
    let : ∀ x : M, NormedAddCommGroup (TangentSpace I x) :=
      fun _ ↦ inferInstanceAs (NormedAddCommGroup E)
    let : ∀ x : M, NormedSpace ℝ (TangentSpace I x) :=
      fun _ ↦ inferInstanceAs (NormedSpace ℝ E)
    let : ∀ x : N, NormedAddCommGroup (TangentSpace J x) :=
      fun _ ↦ inferInstanceAs (NormedAddCommGroup F)
    let : ∀ x : N, NormedSpace ℝ (TangentSpace J x) :=
      fun _ ↦ inferInstanceAs (NormedSpace ℝ F)
    exact fun x ↦ (g.inner (j x)).bilinearComp (D x) (D x)
  have hq (x : M) (v w : TangentSpace I x) :
      q x v w = g.inner (j x) (D x v) (D x w) := rfl
  have hqpos (x : M) (v : TangentSpace I x) (hv : v ≠ 0) : 0 < q x v v := by
    apply g.pos
    exact fun h ↦ hv ((hinj x) (h.trans (map_zero (D x)).symm))
  have hqbounded (x : M) : IsVonNBounded ℝ {v | q x v v < 1} := by
    obtain ⟨A, hA⟩ := (D x).toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr (hinj x))
    let B : TangentSpace J (j x) →L[ℝ] TangentSpace I x :=
      ⟨A, A.continuous_of_finiteDimensional⟩
    apply ((g.isVonNBounded (j x)).image B).subset
    intro v hv
    refine ⟨D x v, hv, ?_⟩
    exact congrArg (fun T : TangentSpace I x →ₗ[ℝ] TangentSpace I x ↦ T v) hA
  have hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (q x)) := by
    intro x₀
    rw [contMDiffAt_section]
    have hg : ContMDiffAt J 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
        (fun y ↦ bilinearCoordinates (j x₀) y (g.inner y)) (j x₀) :=
      (contMDiffAt_section (j x₀)).mp (g.contMDiff (j x₀))
    have hd := (hj x₀).mfderiv_const (m := ∞) (by simp)
    have hform := contMDiffAt_bilinearComp (hg.comp x₀ hj.contMDiffAt) hd
    apply hform.congr_of_eventuallyEq
    have hx : ∀ᶠ x in 𝓝 x₀,
        x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
      (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' x₀)
    have hb : ∀ᶠ x in 𝓝 x₀, j x ∈
        (trivializationAt F (TangentSpace J : N → Type _) (j x₀)).baseSet :=
      hj.continuous.continuousAt.preimage_mem_nhds
        ((trivializationAt F (TangentSpace J : N → Type _) (j x₀)).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (j x₀)))
    filter_upwards [hx, hb] with x hx hb
    change bilinearCoordinates x₀ x (q x) = _
    ext v w
    rw [bilinearCoordinates_apply _ _ _ hx, ContinuousLinearMap.bilinearComp_apply]
    dsimp only [Function.comp_apply]
    rw [bilinearCoordinates_apply _ _ _ hb]
    rw [hq]
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.comp_apply]
    rw [Trivialization.symmL_continuousLinearMapAt _ hb,
      Trivialization.symmL_continuousLinearMapAt _ hb]
    rfl
  refine ⟨{ inner := q
            symm := fun x v w ↦ g.symm (j x) _ _
            pos := hqpos
            isVonNBounded := hqbounded
            contMDiff := hsmooth }, ?_⟩
  exact fun _ _ _ ↦ rfl
end HolomorphicAnosov
