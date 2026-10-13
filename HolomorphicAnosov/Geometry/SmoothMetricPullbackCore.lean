import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped ContDiff Manifold Topology _root_.Topology
open Bundle Bornology ContinuousLinearMap
universe u v
namespace HolomorphicAnosov
noncomputable section
section Implementation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- The inverse tangent differential together with its continuous inverse. -/
def inverseTangentEquiv (e : Diffeomorph I J M N ∞) (y : N) :
    TangentSpace J y ≃L[ℝ] TangentSpace I (e.symm y) :=
  e.symm.mfderivToContinuousLinearEquiv (by simp) y

/-- The transported inner product is obtained by applying the inverse differential to both arguments. -/
def transportedInner (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (y : N) :
    TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ :=
  let D := inverseTangentEquiv e y
  (D.symm.arrowCongr (D.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
    (g.inner (e.symm y))

omit [IsManifold J ∞ N] in
theorem transportedInner_apply (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (y : N) (v w : TangentSpace J y) :
    transportedInner e g y v w =
      g.inner (e.symm y) (mfderiv J I e.symm y v) (mfderiv J I e.symm y w) := rfl

omit [IsManifold J ∞ N] in
theorem transportedInner_symm (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (y : N) (v w : TangentSpace J y) :
    transportedInner e g y v w = transportedInner e g y w v :=
  g.symm (e.symm y) _ _

omit [IsManifold J ∞ N] in
theorem transportedInner_pos (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (y : N) (v : TangentSpace J y) (hv : v ≠ 0) :
    0 < transportedInner e g y v v := by
  apply g.pos
  exact (map_ne_zero_iff (inverseTangentEquiv e y)
    (inverseTangentEquiv e y).injective).mpr hv

omit [IsManifold J ∞ N] in
/-- The transported unit ellipsoid is the continuous-linear image of the original unit ellipsoid. -/
theorem transportedInner_isVonNBounded (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (y : N) :
    IsVonNBounded ℝ {v : TangentSpace J y | transportedInner e g y v v < 1} := by
  let D := inverseTangentEquiv e y
  have heq : {v : TangentSpace J y | transportedInner e g y v v < 1} =
      D.symm '' {w : TangentSpace I (e.symm y) | g.inner (e.symm y) w w < 1} := by
    ext v
    constructor
    · intro hv
      exact ⟨D v, hv, D.symm_apply_apply v⟩
    · rintro ⟨w, hw, rfl⟩
      change g.inner (e.symm y) (D (D.symm w)) (D (D.symm w)) < 1
      simpa using hw
  rw [heq]
  exact (g.isVonNBounded (e.symm y)).image D.symm.toContinuousLinearMap

/-- Bilinear forms in the nested hom-bundle trivialization. -/
def bilinearCoordinates (x₀ x : M)
    (q : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x₀ ⟨x, q⟩).2

theorem bilinearCoordinates_apply (x₀ x : M)
    (q : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hx : x ∈ (trivializationAt E (fun x : M ↦ TangentSpace I x) x₀).baseSet)
    (v w : E) : bilinearCoordinates x₀ x q v w =
      q ((trivializationAt E (fun x : M ↦ TangentSpace I x) x₀).symmL ℝ x v)
        ((trivializationAt E (fun x : M ↦ TangentSpace I x) x₀).symmL ℝ x w) := by
  unfold bilinearCoordinates
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hx hx (by simp)]
  simp only [Trivialization.symmL_apply _ hx]
  rw [Trivialization.coe_linearMapAt_of_mem _ (by simp)]
  rfl

omit [IsManifold J ∞ N] in
theorem contMDiffAt_bilinearComp {q : N → E →L[ℝ] E →L[ℝ] ℝ}
    {D : N → F →L[ℝ] E} {y : N}
    (hq : ContMDiffAt J 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ q y)
    (hD : ContMDiffAt J 𝓘(ℝ, F →L[ℝ] E) ∞ D y) :
    ContMDiffAt J 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun z ↦ (q z).bilinearComp (D z) (D z)) y := by
  exact (hD.clm_precomp (F₃ := ℝ)).clm_comp (hq.clm_comp hD)

/-- Coordinates of the transported tensor are the original coordinates composed with the inverse differential in both slots. -/
theorem transportedInner_coordinates (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (y₀ y : N)
    (hy : y ∈ (trivializationAt F (fun y : N ↦ TangentSpace J y) y₀).baseSet)
    (hb : e.symm y ∈ (trivializationAt E (fun x : M ↦ TangentSpace I x)
      (e.symm y₀)).baseSet) :
    bilinearCoordinates y₀ y (transportedInner e g y) =
      (bilinearCoordinates (e.symm y₀) (e.symm y) (g.inner (e.symm y))).bilinearComp
        (inTangentCoordinates J I id e.symm (mfderiv J I e.symm) y₀ y)
        (inTangentCoordinates J I id e.symm (mfderiv J I e.symm) y₀ y) := by
  ext v w
  rw [bilinearCoordinates_apply _ _ _ hy, ContinuousLinearMap.bilinearComp_apply,
    bilinearCoordinates_apply _ _ _ hb, transportedInner_apply]
  simp only [inTangentCoordinates, inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt _ hb,
    Trivialization.symmL_continuousLinearMapAt _ hb]
  rfl

/-- The transported tensor is smooth in the receiving tangent bundle. -/
theorem transportedInner_contMDiff (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    ContMDiff J (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) y (transportedInner e g y)) := by
  intro y₀
  rw [contMDiffAt_section]
  have hg : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x ↦ bilinearCoordinates (e.symm y₀) x (g.inner x)) (e.symm y₀) := by
    exact (contMDiffAt_section (e.symm y₀)).mp (g.contMDiff (e.symm y₀))
  have hg' := hg.comp y₀ e.symm.contMDiff.contMDiffAt
  have hD : ContMDiffAt J 𝓘(ℝ, F →L[ℝ] E) ∞
      (inTangentCoordinates J I id e.symm (mfderiv J I e.symm) y₀) y₀ :=
    e.symm.contMDiff.contMDiffAt.mfderiv_const (by simp)
  have hform := contMDiffAt_bilinearComp hg' hD
  apply hform.congr_of_eventuallyEq
  have hy : ∀ᶠ y in 𝓝 y₀,
      y ∈ (trivializationAt F (fun y : N ↦ TangentSpace J y) y₀).baseSet :=
    (trivializationAt F (fun y : N ↦ TangentSpace J y) y₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' y₀)
  have hb : ∀ᶠ y in 𝓝 y₀, e.symm y ∈
      (trivializationAt E (fun x : M ↦ TangentSpace I x) (e.symm y₀)).baseSet :=
    e.symm.continuous.continuousAt.preimage_mem_nhds
      ((trivializationAt E (fun x : M ↦ TangentSpace I x) (e.symm y₀)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (e.symm y₀)))
  filter_upwards [hy, hb] with y hy hb
  exact transportedInner_coordinates e g y₀ y hy hb

/-- The smooth pullback Riemannian metric. -/
def transportedContMDiffRiemannianMetric (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :
    Bundle.ContMDiffRiemannianMetric J ∞ F (fun y : N ↦ TangentSpace J y) where
  inner := transportedInner e g
  symm := transportedInner_symm e g
  pos := transportedInner_pos e g
  isVonNBounded := transportedInner_isVonNBounded e g
  contMDiff := transportedInner_contMDiff e g

open scoped Bundle in
/-- The pullback metric has the exact inverse-differential length identity. -/
theorem transported_norm_inverse (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (y : N) (w : TangentSpace J y) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace J y) :=
      ⟨(transportedContMDiffRiemannianMetric e g).toRiemannianMetric⟩
    ‖w‖ = ‖mfderiv J I e.symm y w‖ := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace J y) :=
    ⟨(transportedContMDiffRiemannianMetric e g).toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  rfl

open scoped Bundle in
/-- The pullback metric has the exact forward-differential length identity. -/
theorem transported_norm_forward (e : Diffeomorph I J M N ∞)
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (x : M) (v : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace J y) :=
      ⟨(transportedContMDiffRiemannianMetric e g).toRiemannianMetric⟩
    ‖mfderiv I J e x v‖ = ‖v‖ := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (fun y : N ↦ TangentSpace J y) :=
    ⟨(transportedContMDiffRiemannianMetric e g).toRiemannianMetric⟩
  have hc := mfderiv_comp x
    (e.symm.contMDiff.mdifferentiable (by simp) (e x))
    (e.contMDiff.mdifferentiable (by simp) x)
  have hmap : (e.symm : N → M) ∘ (e : M → N) = id := by
    funext y
    exact e.symm_apply_apply y
  rw [hmap, mfderiv_id] at hc
  have hback := (congrArg (fun T ↦ T v) hc).symm
  change mfderiv J I e.symm (e x) (mfderiv I J e x v) = v at hback
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  change Real.sqrt (g.inner (e.symm (e x))
    (mfderiv J I e.symm (e x) (mfderiv I J e x v))
    (mfderiv J I e.symm (e x) (mfderiv I J e x v))) = Real.sqrt (g.inner x v v)
  rw [hback, e.symm_apply_apply]

end Implementation
end
end HolomorphicAnosov
