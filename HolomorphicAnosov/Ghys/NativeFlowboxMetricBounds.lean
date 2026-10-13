import HolomorphicAnosov.Ghys.NativeFlowboxRealCharts
import HolomorphicAnosov.Ghys.NativeFlowboxScalarDerivative
import HolomorphicAnosov.Analysis.ContinuousRealDerivativeFromComplexCoordinates
import HolomorphicAnosov.Analysis.MetricPullbackCompactLowerBound

/-! Uniform real metric bounds on compact native flowbox domains (Ghys) -/
noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology Bundle
open scoped ContDiff Manifold
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace
variable {d : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
  {ι : Type u} (L : ι → Type u)
  [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
  [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
  [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
  (f : Biholomorph d d M M) (a : AnosovDatum f)
  (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
  (G : NativeInvariantJetAffineLeafFamily f a L U)

/-- In any receiving ambient complex chart, the real derivative of the actual inverse slice is jointly continuous. (Ghys, Lemma 3.3) -/
theorem native_flowbox_real_derivative_continuous (j : Fin G.boxCount)
    (ψ : OpenPartialHomeomorph M (ComplexModel d))
    (hψ : ψ ∈ IsManifold.maximalAtlas (complexModel d) ∞ M) :
    ContinuousOn
      (fun p : ℂ × (Fin (2*d-2) → ℝ) ↦
        fderiv ℝ (fun z ↦ ψ ((G.box j).symm (z,p.2))) p.1)
      ((G.box j).target ∩ (G.box j).symm ⁻¹' ψ.source) := by
  let Ω := (G.box j).target ∩ (G.box j).symm ⁻¹' ψ.source
  have hopen : IsOpen Ω :=
    (G.box j).symm.continuousOn.isOpen_inter_preimage
      (G.box j).open_target ψ.open_source
  have hslice (t : G.transverse j) :
      ContMDiff 𝓘(ℂ) (complexModel d) ∞
        (fun z : nativeAffineFlowboxSlice (G.box j) t.val ↦
          (G.box j).symm (z.val,t.val)) := by
    have hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞
        (fun z : nativeAffineFlowboxSlice (G.box j) t.val ↦
          (G.parametrization j t z).val) :=
      contMDiff_subtype_val.comp (G.parametrization j t).contMDiff
    convert (G.holomorphic_inclusion (G.label j t)).1.comp hp using 1
    funext z
    exact G.parametrization_inclusion j t z
  have hambient (t : G.transverse j) :
      ContMDiffOn 𝓘(ℂ) (complexModel d) ∞
        (fun z : ℂ ↦ (G.box j).symm (z,t.val))
        {z | (z,t.val) ∈ (G.box j).target} := by
    intro z hz
    exact ((contMDiffAt_subtype_iff (I := 𝓘(ℂ)) (I' := complexModel d)
      (U := nativeAffineFlowboxSlice (G.box j) t.val)
      (f := fun z : ℂ ↦ (G.box j).symm (z,t.val))).mp
      ((hslice t).contMDiffAt
        (x := (⟨z,hz⟩ : nativeAffineFlowboxSlice (G.box j) t.val)))).contMDiffWithinAt
  have hdiff (p : ℂ × (Fin (2*d-2) → ℝ)) (hp : p ∈ Ω) :
      DifferentiableAt ℂ (fun z ↦ ψ ((G.box j).symm (z,p.2))) p.1 := by
    let t : G.transverse j := ⟨p.2,G.transverse_contains j p hp.1⟩
    have hc : ContDiffOn ℂ ∞ (fun z ↦ ψ ((G.box j).symm (z,p.2)))
        {z | (z,p.2) ∈ Ω} :=
      contMDiffOn_iff_contDiffOn.mp
        ((contMDiffOn_of_mem_maximalAtlas hψ).comp
          ((hambient t).mono (fun _ hz ↦ hz.1)) (fun _ hz ↦ hz.2))
    exact (hc.differentiableOn (by simp) p.1 hp).differentiableAt
      ((hopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hp)
  exact Analysis.continuousOn_real_derivative_of_complex_coordinates
    (fun p ↦ ψ ((G.box j).symm p)) Ω hdiff
    (fun k ↦ native_flowbox_scalar_derivative_continuous f a U G j ψ hψ k)

/-- The actual real inverse-slice differential, evaluated on an arbitrary model vector, is jointly continuous into the original ambient real tangent bundle. (Ghys, Lemma 3.3) -/
theorem native_flowbox_real_tangent_continuous (j : Fin G.boxCount) :
    Continuous (fun p : (G.box j).target × ℂ ↦
      (⟨(G.box j).symm p.1.val,
        mfderiv 𝓘(ℝ, ℂ) (realModel d)
          (fun w : ℂ ↦ (G.box j).symm (w, p.1.val.2)) p.1.val.1
          ((tangentSpaceCastModel 𝓘(ℝ, ℂ) p.1.val.1).symm p.2)⟩ :
          TangentBundle (realModel d) M)) := by
  let F (p : (G.box j).target × ℂ) : TangentBundle (realModel d) M :=
      ⟨(G.box j).symm p.1.val,
        mfderiv 𝓘(ℝ, ℂ) (realModel d)
          (fun w : ℂ ↦ (G.box j).symm (w, p.1.val.2)) p.1.val.1
          ((tangentSpaceCastModel 𝓘(ℝ, ℂ) p.1.val.1).symm p.2)⟩
  have hb : Continuous (fun p : (G.box j).target × ℂ ↦ (G.box j).symm p.1.val) :=
    (G.box j).symm.continuousOn.domRestrict.comp continuous_fst
  change Continuous F
  rw [continuous_iff_continuousAt]
  intro p
  apply (FiberBundle.continuousAt_totalSpace (ComplexModel d) F).mpr
  refine ⟨hb.continuousAt, ?_⟩
  let x := (F p).proj
  let ψ := chartAt (ComplexModel d) x
  have hx : (G.box j).symm p.1.val ∈ ψ.source := mem_chart_source _ _
  have hopen : IsOpen ((G.box j).target ∩ (G.box j).symm ⁻¹' ψ.source) :=
    (G.box j).symm.continuousOn.isOpen_inter_preimage (G.box j).open_target ψ.open_source
  have hc := (native_flowbox_real_derivative_continuous L f a U G j ψ
    (IsManifold.chart_mem_maximalAtlas (I := complexModel d) x)).continuousAt
      (hopen.mem_nhds ⟨p.1.property, hx⟩)
  have hp : Continuous (fun p : (G.box j).target × ℂ ↦ p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  apply ((hc.comp (x := p) hp.continuousAt).clm_apply continuous_snd.continuousAt).congr
  filter_upwards [hb.continuousAt.preimage_mem_nhds (ψ.open_source.mem_nhds hx)] with q hq
  let t : G.transverse j := ⟨q.1.val.2, G.transverse_contains j q.1.val q.1.property⟩
  have hs := (native_flowbox_slice_real_immersion f a L U G j t q.1.val.1 q.1.property).1.mdifferentiableAt (by simp)
  have hψ : MDifferentiableAt (realModel d) 𝓘(ℝ, ComplexModel d) ψ ((G.box j).symm q.1.val) :=
    (mdifferentiable_chart (I := realModel d) x).mdifferentiableAt hq
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := realModel d)
    (I'' := 𝓘(ℝ, ComplexModel d)) q.1.val.1 hψ hs
  have he := congrArg (fun B ↦ B ((tangentSpaceCastModel 𝓘(ℝ, ℂ) q.1.val.1).symm q.2)) hcomp
  rw [mfderiv_eq_fderiv] at he
  rw [TangentBundle.trivializationAt_apply]
  change fderiv ℝ (fun z ↦ ψ ((G.box j).symm (z, q.1.val.2))) q.1.val.1 q.2 =
    tangentCoordChange (realModel d) ((G.box j).symm q.1.val) x ((G.box j).symm q.1.val) (F q).snd
  rw [← mfderiv_chartAt_eq_tangentCoordChange (I := realModel d) hq]
  exact he

/-- On every compact subset of an actual flowbox target, the original real pullback metric has a uniform positive lower bound against the scalar model norm. (Ghys, Lemma 3.3) -/
theorem native_flowbox_compact_metric_lower_bound
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x))
    (j : Fin G.boxCount) (K : Set (ℂ × (Fin (2*d-2) → ℝ)))
    (hK : IsCompact K) (hKt : K ⊆ (G.box j).target) :
    ∃ m : ℝ, 0 < m ∧ ∀ p ∈ K, ∀ v : ℂ,
      m * ‖v‖ ≤ Real.sqrt (g.inner ((G.box j).symm p)
        (mfderiv 𝓘(ℝ, ℂ) (realModel d) (fun w : ℂ ↦ (G.box j).symm (w,p.2)) p.1
          ((tangentSpaceCastModel 𝓘(ℝ, ℂ) p.1).symm v))
        (mfderiv 𝓘(ℝ, ℂ) (realModel d) (fun w : ℂ ↦ (G.box j).symm (w,p.2)) p.1
          ((tangentSpaceCastModel 𝓘(ℝ, ℂ) p.1).symm v))) := by
  by_cases hn : K.Nonempty
  · let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let : Nonempty K := hn.to_subtype
    let b : K → M := fun p ↦ (G.box j).symm p.val
    let D (p : K) : ℂ →L[ℝ] TangentSpace (realModel d) (b p) :=
      (mfderiv 𝓘(ℝ, ℂ) (realModel d)
        (fun w : ℂ ↦ (G.box j).symm (w,p.val.2)) p.val.1).comp
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) p.val.1).symm.toContinuousLinearMap
    have hmap : Continuous (fun z : K × ℂ ↦
        ((⟨z.1.val, hKt z.1.property⟩ : (G.box j).target), z.2)) :=
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
    have hD : Continuous (fun z : K × ℂ ↦
        (⟨b z.1, D z.1 z.2⟩ : TangentBundle (realModel d) M)) :=
      (native_flowbox_real_tangent_continuous L f a U G j).comp hmap
    have hinj (p : K) : Function.Injective (D p) := by
      let t : G.transverse j := ⟨p.val.2, G.transverse_contains j p.val (hKt p.property)⟩
      exact ((native_flowbox_slice_real_immersion f a L U G j t p.val.1 (hKt p.property)).2).comp
        (tangentSpaceCastModel 𝓘(ℝ, ℂ) p.val.1).symm.injective
    obtain ⟨m, hm, hbound⟩ := Analysis.exists_uniform_metric_pullback_lower_bound g b D hD hinj
    exact ⟨m, hm, fun p hp v ↦ hbound ⟨p, hp⟩ v⟩
  · exact ⟨1, zero_lt_one, fun p hp ↦ (hn ⟨p, hp⟩).elim⟩

/-- The actual inverse-slice derivative cancels the exact scalar chart forward derivative, leaving the original native inclusion derivative. (Ghys, Lemma 3.3) -/
theorem native_flowbox_chart_derivative_identity (j : Fin G.boxCount) (t : G.transverse j)
    (c : OpenPartialHomeomorph (L (G.label j t)) ℂ)
    (ht : c.target = (nativeAffineFlowboxSlice (G.box j) t.val : Set ℂ))
    (hi : ∀ z : nativeAffineFlowboxSlice (G.box j) t.val,
      c.symm z = (G.parametrization j t z).val)
    (hc : ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) ∞ c c.source)
    {x : L (G.label j t)} (hx : x ∈ c.source)
    (v : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x) :
    mfderiv 𝓘(ℝ, ℂ) (realModel d) (fun z : ℂ ↦ (G.box j).symm (z,t.val)) (c x)
      (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) c x v) =
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) (realModel d) (U.leaf (G.label j t)).inclusion x v := by
  have htarget : (c x, t.val) ∈ (G.box j).target := by
    have h := c.map_source hx
    rw [ht] at h
    exact h
  have heq : ((fun z : ℂ ↦ (G.box j).symm (z,t.val)) ∘ c) =ᶠ[𝓝 x]
      (U.leaf (G.label j t)).inclusion := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    let z : nativeAffineFlowboxSlice (G.box j) t.val :=
      ⟨c y, by change c y ∈ (nativeAffineFlowboxSlice (G.box j) t.val : Set ℂ); rw [← ht]; exact c.map_source hy⟩
    change (G.box j).symm (c y,t.val) = (U.leaf (G.label j t)).inclusion y
    rw [G.parametrization_inclusion j t z, ← hi z]
    exact congrArg (U.leaf (G.label j t)).inclusion (c.left_inv hy)
  have hs := (native_flowbox_slice_real_immersion f a L U G j t (c x) htarget).1.mdifferentiableAt (by simp)
  have hd := (hc.contMDiffAt (c.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have h := mfderiv_comp x hs hd
  rw [heq.mfderiv_eq] at h
  exact congrArg (fun B ↦ B v) h.symm

/-- In the original real tangent model, an affine postcomposition of a scalar coordinate with a holomorphic function of derivative one has differential alpha times that scalar-coordinate differential. (Ghys, Lemma 3.3) -/
theorem real_chart_affine_unit_derivative
    {r : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (Fin r → ℝ) N]
    {c D : N → ℂ} {H : ℂ → ℂ} {x : N} (alpha beta : ℂ)
    (hc : MDifferentiableAt 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ) c x)
    (hH : HasDerivAt H 1 (c x))
    (hD : D =ᶠ[𝓝 x] (fun y ↦ alpha * H (c y) + beta))
    (v : TangentSpace 𝓘(ℝ, Fin r → ℝ) x) :
    (tangentSpaceCastModel 𝓘(ℝ, ℂ) (D x))
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ) D x v) =
      alpha * (tangentSpaceCastModel 𝓘(ℝ, ℂ) (c x))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ) c x v) := by
  have hd : HasDerivAt (fun z ↦ alpha * H z + beta) alpha (c x) := by
    simpa only [mul_one] using (hH.const_mul alpha).add_const beta
  have hf := hd.hasFDerivAt.restrictScalars ℝ
  have hm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z ↦ alpha * H z + beta) (c x) :=
    mdifferentiableAt_iff_differentiableAt.mpr hf.differentiableAt
  have h := mfderiv_comp x hm hc
  rw [mfderiv_eq_fderiv, hf.fderiv] at h
  rw [hD.mfderiv_eq]
  change mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ)
    ((fun z ↦ alpha * H z + beta) ∘ c) x v = _
  rw [h]
  change (tangentSpaceCastModel 𝓘(ℝ, ℂ) (c x))
    (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, ℂ) c x v) * alpha = _
  exact mul_comm _ _

end HolomorphicAnosov.Ghys



