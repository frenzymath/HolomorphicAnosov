import HolomorphicAnosov.Geometry.RealComplexProjectedGraph
import HolomorphicAnosov.Geometry.ComplexImmersionGraphCharts
import HolomorphicAnosov.Geometry.ComplexMDerivativeRealification
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle

namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff Manifold Topology _root_.Topology
universe u v
attribute [local instance] complex_isManifold_real

/-- The local projection/graph witness in Demailly's construction. -/
structure NativeLeafLocalProjectionGraph
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) (x : L) where
  chart : OpenPartialHomeomorph L (ComplexModel k)
  ambientChart : OpenPartialHomeomorph M (ComplexModel d)
  linearModel : ComplexModel k →L[ℂ] ComplexModel d
  linearModel_injective : Function.Injective linearModel
  realChart : OpenPartialHomeomorph L (Fin (2*k) → ℝ)
  realChart_mem_real_atlas : realChart ∈ atlas (Fin (2*k) → ℝ) L
  ambientChart_mem_complex_atlas : ambientChart ∈ IsManifold.maximalAtlas (complexModel d) ∞ M
  point_mem_chart : x ∈ chart.source
  point_mem_ambient : inc x ∈ ambientChart.source
  source_inside_ambient : chart.source ⊆ inc ⁻¹' ambientChart.source
  graph_equation : Set.EqOn
    ((ambientChart.extend (complexModel d)) ∘ inc ∘
      (chart.extend (complexModel k)).symm)
    (fun u : ComplexModel k => linearModel u)
    (chart.extend (complexModel k)).target
  /-- Smoothness of the new graph coordinate against its selected original real chart on the exact overlap. -/
  real_to_complex : ∀ e : OpenPartialHomeomorph L (Fin (2*k) → ℝ),
    e ∈ atlas (Fin (2*k) → ℝ) L →
    ContDiffOn ℝ ∞ (chart ∘ e.symm)
      (e.target ∩ e.symm ⁻¹' chart.source)
  /-- Smoothness of the selected original real chart against the new graph coordinate on the exact overlap. -/
  complex_to_real : ∀ e : OpenPartialHomeomorph L (Fin (2*k) → ℝ),
    e ∈ atlas (Fin (2*k) → ℝ) L →
    ContDiffOn ℝ ∞ (e ∘ chart.symm)
      (chart.target ∩ chart.symm ⁻¹' e.source)

/-- Demailly's local projection/implicit-function step for a real immersed leaf whose derivative range is the realification of a continuous complex tangent subbundle (Demailly, Complex Analytic and Differential Geometry (2012), Chapter I, Lemma 7.15, printed p.60).-/
theorem native_leaf_local_projection_graph
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M)
    (x : L)
    (P : ContinuousRealTangentSubbundle (realModel d) M)
    (hinc : Manifold.IsImmersion 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) ∞ inc)
    (_hP : ∀ y : L, (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc y).range =
      P.toDistribution (inc y))
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (hS : ∀ y : L, ((S.toDistribution (inc y)).restrictScalars ℝ).map
      (complexTangentToReal d (inc y)).toLinearEquiv.toLinearMap =
      (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc y).range) :
    Nonempty (NativeLeafLocalProjectionGraph (k := k) (d := d) inc x) := by
  let c := chartAt (Fin (2*k) → ℝ) x
  let t := chartAt (ComplexModel d) (inc x)
  let g : (Fin (2*k) → ℝ) → ComplexModel d := t ∘ inc ∘ c.symm
  let U := c.target ∩ c.symm ⁻¹' (inc ⁻¹' t.source)
  have hU : IsOpen U := c.isOpen_inter_preimage_symm
    (t.open_source.preimage hinc.contMDiff.continuous)
  have hcx : x ∈ c.source := mem_chart_source _ _
  have htx : inc x ∈ t.source := mem_chart_source _ _
  have hca : c x ∈ U := ⟨c.map_source hcx, by
    change inc (c.symm (c x)) ∈ t.source
    simpa only [c.left_inv hcx] using htx⟩
  have hcs : ContMDiffOn 𝓘(ℝ, Fin (2*k) → ℝ) 𝓘(ℝ, Fin (2*k) → ℝ)
      ∞ c.symm c.target := contMDiffOn_chart_symm
  have hts : ContMDiffOn (realModel d) (realModel d) ∞ t t.source :=
    contMDiffOn_chart
  have hg : ContDiffOn ℝ ∞ g U := by
    apply ContMDiffOn.contDiffOn
    exact hts.comp (hinc.contMDiff.comp_contMDiffOn
      (hcs.mono inter_subset_left)) inter_subset_right
  have hder (z) (hz : z ∈ U) :
      fderiv ℝ g z =
      (mfderiv (realModel d) (realModel d) t (inc (c.symm z))).comp
        ((mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc (c.symm z)).comp
          (mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) 𝓘(ℝ, Fin (2*k) → ℝ) c.symm z)) := by
    have hc := ((mdifferentiable_chart (I := 𝓘(ℝ, Fin (2*k) → ℝ)) x).symm.mdifferentiableAt hz.1)
    have ht := (mdifferentiable_chart (I := realModel d) (inc x)).mdifferentiableAt hz.2
    have hi := (hinc.contMDiff (c.symm z)).mdifferentiableAt (by simp)
    rw [← mfderiv_eq_fderiv]
    exact (mfderiv_comp z ht (hi.comp z hc)).trans
      (congrArg (fun D ↦ (mfderiv (realModel d) (realModel d) t (inc (c.symm z))).comp D)
        (mfderiv_comp z hi hc))
  have hgi : Function.Injective (fderiv ℝ g (c x)) := by
    rw [hder (c x) hca]
    exact ((mdifferentiable_chart (I := realModel d) (inc x)).mfderiv_injective hca.2).comp
      ((hinc.mfderiv_injective (by simp) (c.symm (c x))).comp
        ((mdifferentiable_chart (I := 𝓘(ℝ, Fin (2*k) → ℝ)) x).symm.mfderiv_injective hca.1))
  have hgD : ∀ z ∈ U, ∀ b : ℂ, ∀ v,
      b • fderiv ℝ g z v ∈ (fderiv ℝ g z).range := by
    intro z hz b v
    let y := c.symm z
    let Di := mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) (realModel d) inc y
    let Dc := mfderiv 𝓘(ℝ, Fin (2*k) → ℝ) 𝓘(ℝ, Fin (2*k) → ℝ) c.symm z
    let Dt : TangentSpace (realModel d) (inc y) →L[ℝ] ComplexModel d :=
      mfderiv (realModel d) (realModel d) t (inc y)
    have hmem : Di (Dc v) ∈ Di.range := ⟨Dc v, rfl⟩
    rw [← hS y] at hmem
    obtain ⟨w, hw, he⟩ := hmem
    have hbw : (complexTangentToReal d (inc y)) (b • w) ∈ Di.range := by
      rw [← hS y]
      exact ⟨b • w, (S.toDistribution (inc y)).smul_mem b hw, rfl⟩
    obtain ⟨u, hu⟩ := hbw
    obtain ⟨v', hv'⟩ :=
      ((mdifferentiable_chart (I := 𝓘(ℝ, Fin (2*k) → ℝ)) x).symm.mfderiv_surjective hz.1) u
    have ht : MDifferentiableAt (complexModel d) (complexModel d) t (inc y) :=
      (mdifferentiable_chart (I := complexModel d) (inc x)).mdifferentiableAt hz.2
    have hreal (w' : TangentSpace (complexModel d) (inc y)) :
        Dt (complexTangentToReal d (inc y) w') =
          mfderiv (complexModel d) (complexModel d) t (inc y) w' :=
      mfderiv_complex_to_real ht w'
    refine ⟨v', ?_⟩
    rw [hder z hz]
    change Dt (Di (Dc v')) = b • Dt (Di (Dc v))
    change Dc v' = u at hv'
    erw [hv', hu, ← he, hreal, hreal, map_smul]
    rfl
  obtain ⟨p, hpa, hpU, hpC, hpiC, hGp, hGinj⟩ :=
    real_complex_projected_graph hU hca hg hgi hgD
  let G := g ∘ p.symm
  have hGat : ContDiffAt ℂ 1 G (p (c x)) :=
    (hGp.contDiffAt (p.open_target.mem_nhds (p.map_source hpa))).of_le (by simp)
  obtain ⟨F, e, r, h, hra, hrp, hrC, hriC, hh, hgraph⟩ :=
    complex_euclidean_smooth_graph p.open_target (p.map_source hpa)
      hGat hGat.differentiableAt_one.hasFDerivAt hGinj
  obtain ⟨q, hqsource, hqtarget, hqC, hqiC, hqgraph⟩ :=
    complex_ambient_graph_chart e r.open_target hh
  let a := (c.trans p).trans r
  let b := t.trans q
  let A : ComplexModel k →L[ℂ] ComplexModel d :=
    e.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ (ComplexModel k) F)
  have hxa : x ∈ a.source := ⟨⟨hcx, hpa⟩, hra⟩
  have hqin : ∀ z ∈ r.source, G z ∈ q.source := by
    intro z hz
    rw [hqsource, hgraph z hz]
    simpa only [mem_ofPred_eq, e.symm_apply_apply] using r.map_source hz
  have hab : a.source ⊆ inc ⁻¹' b.source := by
    intro y hy
    change (y ∈ c.source ∧ c y ∈ p.source) ∧ p (c y) ∈ r.source at hy
    have hi : inc y ∈ t.source := by
      have hm := (hpU hy.1.2).2
      change inc (c.symm (c y)) ∈ t.source at hm
      simpa only [c.left_inv hy.1.1] using hm
    refine ⟨hi, ?_⟩
    have hq := hqin (p (c y)) hy.2
    change t (inc y) ∈ q.source
    simpa only [G, g, Function.comp_apply, p.left_inv hy.1.2, c.left_inv hy.1.1] using hq
  have haC : ContMDiffOn 𝓘(ℝ, Fin (2*k) → ℝ) (realModel k) ∞ a a.source := by
    apply (hrC.restrict_scalars ℝ).contMDiffOn.comp
    · exact hpC.contMDiffOn.comp
        ((contMDiffOn_chart (I := 𝓘(ℝ, Fin (2*k) → ℝ)) (x := x)).mono
          (fun _ hz ↦ hz.1.1)) (fun _ hz ↦ hz.1.2)
    · exact fun _ hz ↦ hz.2
  have haiC : ContMDiffOn (realModel k) 𝓘(ℝ, Fin (2*k) → ℝ) ∞ a.symm a.target := by
    apply hcs.comp
    · exact hpiC.contMDiffOn.comp
        ((hriC.restrict_scalars ℝ).contMDiffOn.mono inter_subset_left)
        (fun _ hz ↦ hz.2.1)
    · exact fun _ hz ↦ hz.2.2
  refine ⟨{ chart := a
            ambientChart := b
            linearModel := A
            linearModel_injective := e.injective.comp (by intro u v h; exact congrArg Prod.fst h)
            realChart := c
            realChart_mem_real_atlas := chart_mem_atlas _ _
            ambientChart_mem_complex_atlas :=
              complex_chart_trans_mem_maximalAtlas
                (IsManifold.chart_mem_maximalAtlas (inc x)) q hqC hqiC
            point_mem_chart := hxa
            point_mem_ambient := hab hxa
            source_inside_ambient := hab
            graph_equation := ?_
            real_to_complex := ?_
            complex_to_real := ?_ }⟩
  · intro u hu
    have hu' : u ∈ a.target := by simpa using hu
    change q (G (r.symm u)) = e (u, 0)
    rw [hgraph (r.symm u) (r.map_target hu'.1), r.right_inv hu'.1]
    exact hqgraph u hu'.1
  · intro c' hc'
    apply ContMDiffOn.contDiffOn
    exact haC.comp ((contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas hc')).mono inter_subset_left) inter_subset_right
  · intro c' hc'
    apply ContMDiffOn.contDiffOn
    exact (contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc')).comp
      (haiC.mono inter_subset_left) inter_subset_right

end HolomorphicAnosov
