import HolomorphicAnosov.Dynamics.HirschPughFiniteEnergyHelper
import HolomorphicAnosov.Dynamics.HirschPughRestrictedSplitting
import HolomorphicAnosov.Geometry.SmoothMetricPullbackCore
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Continuous split finite energy tensor

Hirsch–Pugh (1969), Theorem 3.1 p.148, finite-energy adapted metric construction.
The complementary projections over the original hyperbolic set are continuous
by the restricted splitting theorem. Pull back the original scalar product by
each of the finitely many forward/backward derivatives and sum, then compose
with the respective projections. Evaluations are continuous; finite dimension
turns this into tensor continuity in each bundle chart. The zero iterate makes
each energy positive, complementarity makes the split form positive, and the
projection identities identify its restrictions with the original finite sums.
-/

open Set Bundle Filter
open scoped ContDiff Manifold Topology Bundle
noncomputable section
namespace HolomorphicAnosov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The finite Mather energy, with both vector arguments retained. -/
def hyperbolicFiniteEnergyTensor
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (x : M) :
    TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  ∑ j ∈ Finset.range q,
    (H.originalMetric.inner (((g : M → M)^[j]) x)).bilinearComp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j]) x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j]) x)

theorem hyperbolicFiniteEnergyTensor_diag
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    hyperbolicFiniteEnergyTensor H q g x v v = hyperbolicFiniteEnergy H q g x v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  simp only [hyperbolicFiniteEnergyTensor, hyperbolicFiniteEnergy,
    sum_apply, ContinuousLinearMap.bilinearComp_apply,
    hyperbolicRiemannianNorm]
  apply Finset.sum_congr rfl
  intro j hj
  apply (Real.sq_sqrt ?_).symm
  exact real_inner_self_nonneg (x := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
    ((g : M → M)^[j]) x v))

/-- The continuous adapted form makes the original stable and unstable subspaces
orthogonal, using the finite forward and backward energy on the respective summands. -/
def hyperbolicSplitEnergyTensor [FiniteDimensional ℝ E]
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ) (x : Λ) :
    TangentSpace 𝓘(ℝ, E) (x : M) →L[ℝ] TangentSpace 𝓘(ℝ, E) (x : M) →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  let Ps := ((H.stable.fibre x).projection (H.unstable.fibre x)
    (H.complementary x)).toContinuousLinearMap
  let Pu := ((H.unstable.fibre x).projection (H.stable.fibre x)
    (H.complementary x).symm).toContinuousLinearMap
  (hyperbolicFiniteEnergyTensor H q f x).bilinearComp Ps Ps +
    (hyperbolicFiniteEnergyTensor H q f.symm x).bilinearComp Pu Pu

/-- The finite energy tensor is continuous when evaluated on continuous tangent vectors. -/
theorem hyperbolicFiniteEnergyTensor_eval_continuousAt
    {X : Type*} [TopologicalSpace X] {x₀ : X}
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (b : X → M) (s t : ∀ x, TangentSpace 𝓘(ℝ, E) (b x))
    (hs : ContinuousAt (fun x ↦ (⟨b x, s x⟩ : TangentBundle 𝓘(ℝ, E) M)) x₀)
    (ht : ContinuousAt (fun x ↦ (⟨b x, t x⟩ : TangentBundle 𝓘(ℝ, E) M)) x₀) :
    ContinuousAt (fun x ↦ hyperbolicFiniteEnergyTensor H q g (b x) (s x) (t x)) x₀ := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.inner, H.originalMetric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  simp only [hyperbolicFiniteEnergyTensor, sum_apply,
    ContinuousLinearMap.bilinearComp_apply]
  apply tendsto_finsetSum
  intro j hj
  have hd := (g.contMDiff.iterate j).continuous_tangentMap (by simp)
  have hs' := hd.continuousAt.comp hs
  have ht' := hd.continuousAt.comp ht
  exact hs'.inner_bundle ht'

/-- Complementary restricted projections give continuity of the split energy when
evaluated on continuous tangent vectors over the invariant set. -/
theorem hyperbolicSplitEnergyTensor_eval_continuousAt [FiniteDimensional ℝ E]
    {X : Type*} [TopologicalSpace X] {x₀ : X}
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ)
    (b : X → Λ) (s t : ∀ x, TangentSpace 𝓘(ℝ, E) (b x : M))
    (hs : ContinuousAt (fun x ↦ (⟨(b x : M), s x⟩ : TangentBundle 𝓘(ℝ, E) M)) x₀)
    (ht : ContinuousAt (fun x ↦ (⟨(b x : M), t x⟩ : TangentBundle 𝓘(ℝ, E) M)) x₀) :
    ContinuousAt (fun x ↦ hyperbolicSplitEnergyTensor H q (b x) (s x) (t x)) x₀ := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  have hps := HirschRestrictedCoordinates.continuous_restricted_projection
    H.stable H.unstable H.complementary
  have hpu := HirschRestrictedCoordinates.continuous_restricted_projection
    H.unstable H.stable (fun x ↦ (H.complementary x).symm)
  have hs' : ContinuousAt (fun x ↦
      (⟨(⟨(b x : M), s x⟩ : TangentBundle 𝓘(ℝ, E) M), (b x).property⟩ :
        {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ})) x₀ := hs.codRestrict _
  have ht' : ContinuousAt (fun x ↦
      (⟨(⟨(b x : M), t x⟩ : TangentBundle 𝓘(ℝ, E) M), (b x).property⟩ :
        {z : TangentBundle 𝓘(ℝ, E) M // z.proj ∈ Λ})) x₀ := ht.codRestrict _
  exact (hyperbolicFiniteEnergyTensor_eval_continuousAt H q f (fun x ↦ (b x : M))
    (fun x ↦ (H.stable.fibre (b x)).projection (H.unstable.fibre (b x))
      (H.complementary (b x)) (s x))
    (fun x ↦ (H.stable.fibre (b x)).projection (H.unstable.fibre (b x))
      (H.complementary (b x)) (t x))
    (hps.continuousAt.comp hs') (hps.continuousAt.comp ht')).add
      (hyperbolicFiniteEnergyTensor_eval_continuousAt H q f.symm (fun x ↦ (b x : M))
        (fun x ↦ (H.unstable.fibre (b x)).projection (H.stable.fibre (b x))
          (H.complementary (b x)).symm (s x))
        (fun x ↦ (H.unstable.fibre (b x)).projection (H.stable.fibre (b x))
          (H.complementary (b x)).symm (t x))
        (hpu.continuousAt.comp hs') (hpu.continuousAt.comp ht'))

/-- The split finite energy is a continuous section of the actual bilinear tensor bundle.
In any tangent chart, continuity of evaluation on two fixed vectors implies operator
continuity twice, since the model space is finite dimensional. -/
theorem hyperbolicSplitEnergyTensor_continuous [FiniteDimensional ℝ E]
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ) :
    Continuous (fun x : Λ ↦ (⟨(x : M), hyperbolicSplitEnergyTensor H q x⟩ :
      TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x →L[ℝ]
          TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ))) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace (E →L[ℝ] E →L[ℝ] ℝ)]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  change ContinuousAt (fun x : Λ ↦
    bilinearCoordinates (x₀ : M) (x : M) (hyperbolicSplitEnergyTensor H q x)) x₀
  apply continuousAt_clm_apply.mpr
  intro v
  apply continuousAt_clm_apply.mpr
  intro w
  let e := trivializationAt E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) (x₀ : M)
  have hbase : (x₀ : M) ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have hs (u : E) : ContinuousAt (fun x : Λ ↦
      (⟨(x : M), e.symmL ℝ (x : M) u⟩ : TangentBundle 𝓘(ℝ, E) M)) x₀ := by
    have htarget : ((x₀ : M), u) ∈ e.target := e.mem_target.mpr hbase
    have hp : ContinuousAt (fun x : Λ ↦ ((x : M), u)) x₀ :=
      (continuous_subtype_val.prodMk continuous_const).continuousAt
    have h := (e.continuousOn_symm.continuousAt
      (e.open_target.mem_nhds htarget)).comp (f := fun x : Λ ↦ ((x : M), u)) hp
    apply h.congr_of_eventuallyEq
    have hb : ∀ᶠ x : Λ in 𝓝 x₀, (x : M) ∈ e.baseSet :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)
    filter_upwards [hb] with x hx
    simp only [Function.comp_apply, e.symmL_apply hx]
  have h := hyperbolicSplitEnergyTensor_eval_continuousAt H q (fun x : Λ ↦ x)
    (fun x ↦ e.symmL ℝ (x : M) v) (fun x ↦ e.symmL ℝ (x : M) w) (hs v) (hs w)
  apply h.congr_of_eventuallyEq
  have hb : ∀ᶠ x : Λ in 𝓝 x₀, (x : M) ∈ e.baseSet :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)
  filter_upwards [hb] with x hx
  exact bilinearCoordinates_apply (x₀ : M) (x : M) (hyperbolicSplitEnergyTensor H q x) hx v w

/-- The zero iterate contributes the original positive quadratic form. -/
theorem hyperbolicFiniteEnergyTensor_pos
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) {q : ℕ} (hq : 0 < q)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) (hv : v ≠ 0) :
    0 < hyperbolicFiniteEnergyTensor H q g x v v := by
  rw [hyperbolicFiniteEnergyTensor_diag]
  apply Finset.sum_pos'
  · intro j hj
    exact sq_nonneg _
  · refine ⟨0, Finset.mem_range.mpr hq, ?_⟩
    simp only [Function.iterate_zero, mfderiv_id]
    exact sq_pos_of_pos (Real.sqrt_pos.mpr (H.originalMetric.pos x v hv))

theorem hyperbolicFiniteEnergyTensor_nonneg
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    0 ≤ hyperbolicFiniteEnergyTensor H q g x v v := by
  rw [hyperbolicFiniteEnergyTensor_diag]
  exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)

/-- Complementarity guarantees that a nonzero tangent vector has a nonzero
stable or unstable component, so the split finite energy is positive definite. -/
theorem hyperbolicSplitEnergyTensor_pos [FiniteDimensional ℝ E]
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) {q : ℕ} (hq : 0 < q)
    (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)) (hv : v ≠ 0) :
    0 < hyperbolicSplitEnergyTensor H q x v v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  let Ps := (H.stable.fibre x).projection (H.unstable.fibre x) (H.complementary x)
  let Pu := (H.unstable.fibre x).projection (H.stable.fibre x) (H.complementary x).symm
  change 0 < hyperbolicFiniteEnergyTensor H q f x (Ps v) (Ps v) +
    hyperbolicFiniteEnergyTensor H q f.symm x (Pu v) (Pu v)
  by_cases hs : Ps v = 0
  · have hu : Pu v ≠ 0 := by
      intro hu
      have heq := Submodule.projection_add_projection_eq_self (H.complementary x) v
      change Ps v + Pu v = v at heq
      simp only [hs, hu, add_zero] at heq
      exact hv heq.symm
    exact add_pos_of_nonneg_of_pos (hyperbolicFiniteEnergyTensor_nonneg H q f x _)
      (hyperbolicFiniteEnergyTensor_pos H hq f.symm x _ hu)
  · exact add_pos_of_pos_of_nonneg (hyperbolicFiniteEnergyTensor_pos H hq f x _ hs)
      (hyperbolicFiniteEnergyTensor_nonneg H q f.symm x _)

/-- On the stable subspace the split form agrees exactly with forward finite energy. -/
theorem hyperbolicSplitEnergyTensor_stable [FiniteDimensional ℝ E]
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ)
    (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)) (hv : v ∈ H.stable.fibre x) :
    hyperbolicSplitEnergyTensor H q x v v = hyperbolicFiniteEnergy H q f x v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  simp only [hyperbolicSplitEnergyTensor, add_apply,
    ContinuousLinearMap.bilinearComp_apply, LinearMap.coe_toContinuousLinearMap',
    Submodule.projection_apply_of_mem_left (H.complementary x) hv,
    Submodule.projection_apply_of_mem_right (H.complementary x).symm hv,
    map_zero, add_zero, hyperbolicFiniteEnergyTensor_diag]

/-- On the unstable subspace the split form agrees exactly with backward finite energy. -/
theorem hyperbolicSplitEnergyTensor_unstable [FiniteDimensional ℝ E]
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ) (q : ℕ)
    (x : Λ) (v : TangentSpace 𝓘(ℝ, E) (x : M)) (hv : v ∈ H.unstable.fibre x) :
    hyperbolicSplitEnergyTensor H q x v v = hyperbolicFiniteEnergy H q f.symm x v := by
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    ⟨H.originalMetric.toRiemannianMetric⟩
  simp only [hyperbolicSplitEnergyTensor, add_apply,
    ContinuousLinearMap.bilinearComp_apply, LinearMap.coe_toContinuousLinearMap',
    Submodule.projection_apply_of_mem_left (H.complementary x).symm hv,
    Submodule.projection_apply_of_mem_right (H.complementary x) hv,
    map_zero, zero_add, hyperbolicFiniteEnergyTensor_diag]

end HolomorphicAnosov

