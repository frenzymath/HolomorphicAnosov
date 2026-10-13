import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Analysis.Lebl.lebl_analyticOnNhd
import HolomorphicAnosov.Geometry.ComplexLinearSplitNormalForm
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff




/-! This file constructs holomorphic graph charts for a map whose differential splits. (Demailly, I.7.15, p. 60).
-/
namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff Manifold Topology _root_.Topology
universe u v

/-- The source and target extended charts admit a common open source domain on which `f` maps into the target chart source. (Mathlib, `ContinuousAt` and `mem_nhds_iff`). -/
private theorem complex_chart_domain_at
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (ComplexModel k) L]
    [IsManifold (complexModel k) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : L → M} {x : L}
    (hf : ContMDiffAt (complexModel k) (complexModel d) ∞ f x) :
    ∃ U : Set L, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt (complexModel k) x).source ∧
      MapsTo f U (extChartAt (complexModel d) (f x)).source := by
  have hcont : ContinuousAt f x := hf.continuousAt
  have hsrc : (extChartAt (complexModel k) x).source ∈ 𝓝 x :=
    (isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x)
  have htgt : (extChartAt (complexModel d) (f x)).source ∈ 𝓝 (f x) :=
    (isOpen_extChartAt_source (f x)).mem_nhds (mem_extChartAt_source (f x))
  have hpre : f ⁻¹' (extChartAt (complexModel d) (f x)).source ∈ 𝓝 x :=
    hcont htgt
  obtain ⟨U, hUsub, hU, hUx⟩ := mem_nhds_iff.mp (inter_mem hsrc hpre)
  refine ⟨U, hU, hUx, ?_, ?_⟩
  · intro z hz
    exact hUsub hz |>.1
  · intro z hz
    exact hUsub hz |>.2

/-- The coordinate representative of `f` at `x` is the corresponding extended-chart composition. -/
private theorem complex_written_map_C1_at
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (ComplexModel k) L]
    [IsManifold (complexModel k) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : L → M} {x : L}
    (hf : ContMDiffAt (complexModel k) (complexModel d) ∞ f x) :
    ContDiffWithinAt ℂ 1
      ((extChartAt (complexModel d) (f x)) ∘ f ∘ (extChartAt (complexModel k) x).symm)
      (Set.range (complexModel k)) (extChartAt (complexModel k) x x) := by
  let : IsManifold (complexModel k) (1 : WithTop ℕ∞) L :=
    IsManifold.of_le (n := ∞) (by simp)
  let : IsManifold (complexModel d) (1 : WithTop ℕ∞) M :=
    IsManifold.of_le (n := ∞) (by simp)
  have hf1 : ContMDiffAt (complexModel k) (complexModel d) 1 f x := hf.of_le (by simp)
  exact (contMDiffAt_iff (I := complexModel k) (I' := complexModel d)
    (n := (1 : WithTop ℕ∞)) (f := f) (x := x)).mp hf1 |>.2

/-- The coordinate representative is `C¹`, and its derivative at the marked point is injective when the manifold differential is an immersion. -/
private theorem complex_written_map_C1_fderivWithin_injective
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (ComplexModel k) L]
    [IsManifold (complexModel k) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : L → M} {x : L}
    (hf : ContMDiffAt (complexModel k) (complexModel d) ∞ f x)
    (hdiff : IsDiffImmersionAt (complexModel k) (complexModel d) f x) :
    ContDiffWithinAt ℂ 1
        ((extChartAt (complexModel d) (f x)) ∘ f ∘
          (extChartAt (complexModel k) x).symm)
        (Set.range (complexModel k)) (extChartAt (complexModel k) x x) ∧
      Function.Injective (fderivWithin ℂ
        ((extChartAt (complexModel d) (f x)) ∘ f ∘
          (extChartAt (complexModel k) x).symm)
        (Set.range (complexModel k)) (extChartAt (complexModel k) x x)) := by
  constructor
  · exact complex_written_map_C1_at hf
  · let : IsManifold (complexModel k) (1 : WithTop ℕ∞) L :=
      IsManifold.of_le (n := ∞) (by simp)
    let : IsManifold (complexModel d) (1 : WithTop ℕ∞) M :=
      IsManifold.of_le (n := ∞) (by simp)
    have hmd : MDifferentiableAt (complexModel k) (complexModel d) f x :=
      IsDiffImmersionAt.mdifferentiableAt hdiff
    have heq := hmd.mfderiv
    have hinj := hdiff.mfderiv_injective
    let cdom := tangentSpaceCastModel (complexModel k) x
    let ccod := tangentSpaceCastModel (complexModel d) (f x)
    intro u v huv
    apply cdom.symm.injective
    apply hinj
    rw [heq]
    simp only [ContinuousLinearMap.comp_apply]
    apply ccod.symm.injective
    exact huv

/-- A differentiable map on an open finite-dimensional complex model is analytic by the several-variable Cauchy theorem. -/
private theorem complex_differentiableOn_analyticOnNhd
    {d e : ℕ} {S : Set (ComplexModel d)} {g : ComplexModel d → ComplexModel e}
    (hS : IsOpen S) (hd : 1 ≤ d) (hg : DifferentiableOn ℂ g S) :
    AnalyticOnNhd ℂ g S := by
  apply AnalyticOnNhd.pi
  intro i
  apply HolomorphicAnosov.Analysis.lebl_analyticOnNhd hd hS
  exact differentiableOn_pi.mp hg i

/-- The zero-dimensional source case is constant; positive-dimensional sources use the several-variable Cauchy theorem. -/
private theorem complex_differentiableOn_analyticOnNhd_or_zero
    {d e : ℕ} {S : Set (ComplexModel d)} {g : ComplexModel d → ComplexModel e}
    (hS : IsOpen S) (hg : DifferentiableOn ℂ g S) :
    AnalyticOnNhd ℂ g S := by
  by_cases hd : d = 0
  · subst d
    have hconst : g = fun _ ↦ g 0 := by
      funext z
      congr 1
      exact Subsingleton.elim z 0
    rw [hconst]
    exact analyticOnNhd_const
  · exact complex_differentiableOn_analyticOnNhd hS (Nat.one_le_iff_ne_zero.mpr hd) hg

/-- A `C¹` coordinate map on an open finite-dimensional complex model has an analytic representative. -/
private theorem complex_contDiffOn_one_analyticOnNhd
    {d e : ℕ} {S : Set (ComplexModel d)} {g : ComplexModel d → ComplexModel e}
    (hS : IsOpen S) (hg : ContDiffOn ℂ 1 g S) :
    AnalyticOnNhd ℂ g S :=
  complex_differentiableOn_analyticOnNhd_or_zero hS hg.differentiableOn_one

/-- A complex `C¹` map with invertible derivative has a local inverse whose two directions are smooth on their open domains. -/
private theorem complex_model_smooth_inverse_restrict
    {d : ℕ} {g : ComplexModel d → ComplexModel d} {a : ComplexModel d}
    {S : Set (ComplexModel d)} (hS : IsOpen S) (ha : a ∈ S)
    (hg : ContDiffAt ℂ 1 g a) (e : ComplexModel d ≃L[ℂ] ComplexModel d)
    (he : HasFDerivAt g e.toContinuousLinearMap a) :
    ∃ p : OpenPartialHomeomorph (ComplexModel d) (ComplexModel d),
      a ∈ p.source ∧ p.source ⊆ S ∧ (p : ComplexModel d → ComplexModel d) = g ∧
      ContDiffOn ℂ ∞ p p.source ∧ ContDiffOn ℂ ∞ p.symm p.target := by
  let p := hg.toOpenPartialHomeomorph g he one_ne_zero
  let q := p.restrOpen S hS
  have hqa : a ∈ q.source := by
    change a ∈ p.source ∩ S
    exact ⟨hg.mem_toOpenPartialHomeomorph_source he one_ne_zero, ha⟩
  have hq : (q : ComplexModel d → ComplexModel d) = g := rfl
  have hqC : ContDiffAt ℂ 1 q a := by simpa only [hq] using hg
  have hqi : ContDiffAt ℂ 1 q.symm (q a) := by
    apply q.contDiffAt_symm (f₀' := e) (q.map_source hqa)
    · rw [q.left_inv hqa, hq]
      exact he
    · simpa only [q.left_inv hqa] using hqC
  let r := q.restrContDiff ℂ 1 (by simp)
  have hra : a ∈ r.source := ⟨hqa, hqC, hqi⟩
  have hrs : r.source ⊆ S := fun z hz ↦ hz.1.2
  have hrC : ContDiffOn ℂ 1 r r.source :=
    OpenPartialHomeomorph.contDiffOn_restrContDiff_source ℂ q (by simp)
  have hriC : ContDiffOn ℂ 1 r.symm r.target :=
    OpenPartialHomeomorph.contDiffOn_restrContDiff_target ℂ q (by simp)
  exact ⟨r, hra, hrs, rfl,
    (complex_contDiffOn_one_analyticOnNhd r.open_source hrC).contDiffOn_of_completeSpace,
    (complex_contDiffOn_one_analyticOnNhd r.open_target hriC).contDiffOn_of_completeSpace⟩

/-- The projected inverse has smooth inverse directions when the split projection has identity derivative at the marked point. -/
private theorem complex_projected_inverse_smooth_restrict
    {d : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [FiniteDimensional ℂ E']
    {g : ComplexModel d → E'} {S : Set (ComplexModel d)} (hS : IsOpen S)
    {a : ComplexModel d} (ha : a ∈ S) (hg : ContDiffOn ℂ ∞ g S)
    (P : E' →L[ℂ] ComplexModel d)
    {A : ComplexModel d →L[ℂ] E'}
    (hPA : P.comp A = ContinuousLinearMap.id ℂ (ComplexModel d))
    (he : HasFDerivAt g A a) :
    ∃ p : OpenPartialHomeomorph (ComplexModel d) (ComplexModel d),
      a ∈ p.source ∧ p.source ⊆ S ∧ (p : ComplexModel d → ComplexModel d) = P ∘ g ∧
      ContDiffOn ℂ ∞ p p.source ∧ ContDiffOn ℂ ∞ p.symm p.target := by
  let := FiniteDimensional.complete ℂ (ComplexModel d)
  have hPg : HasFDerivAt (P ∘ g) (P.comp A) a := P.hasFDerivAt.comp a he
  have hPid : HasFDerivAt (P ∘ g)
      (ContinuousLinearEquiv.refl ℂ (ComplexModel d)).toContinuousLinearMap a := by
    simpa [hPA] using hPg
  have hGP : ContDiffAt ℂ 1 (P ∘ g) a := by
    have hga := hg.contDiffAt (hS.mem_nhds ha)
    exact (P.contDiff.contDiffAt.comp a hga).of_le (by simp)
  obtain ⟨p, hpa, hpS, hp, hpC, hpiC⟩ :=
    complex_model_smooth_inverse_restrict hS ha hGP (ContinuousLinearEquiv.refl ℂ (ComplexModel d)) hPid
  exact ⟨p, hpa, hpS, hp, hpC, hpiC⟩

/-- The Euclidean graph construction produces a smooth local source chart and graph over a complement of an injective derivative. (Demailly, I.7.15, p. 60). -/
theorem complex_euclidean_smooth_graph
    {k d : ℕ} {g : ComplexModel k → ComplexModel d} {a : ComplexModel k}
    {S : Set (ComplexModel k)} (hS : IsOpen S) (ha : a ∈ S)
    (hg : ContDiffAt ℂ 1 g a) {A : ComplexModel k →L[ℂ] ComplexModel d}
    (hA : HasFDerivAt g A a) (hinj : Function.Injective A) :
    ∃ (F : Submodule ℂ (ComplexModel d))
      (e : (ComplexModel k × F) ≃L[ℂ] ComplexModel d)
      (p : OpenPartialHomeomorph (ComplexModel k) (ComplexModel k))
      (h : ComplexModel k → F),
      a ∈ p.source ∧ p.source ⊆ S ∧
      ContDiffOn ℂ ∞ p p.source ∧ ContDiffOn ℂ ∞ p.symm p.target ∧
      ContDiffOn ℂ ∞ h p.target ∧
      (∀ z ∈ p.source, g z = e (p z, h (p z))) := by
  obtain ⟨V, hVa, hVg⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨W, hWV, hW, haW⟩ := mem_nhds_iff.mp hVa
  let U := W ∩ S
  have hU : IsOpen U := hW.inter hS
  have haU : a ∈ U := ⟨haW, ha⟩
  have hgU : ContDiffOn ℂ ∞ g U :=
    (complex_contDiffOn_one_analyticOnNhd hU
      (hVg.mono (inter_subset_left.trans hWV))).contDiffOn_of_completeSpace
  obtain ⟨F, e, he⟩ := complex_linear_split_normal_form A hinj
  let P := (ContinuousLinearMap.fst ℂ (ComplexModel k) F).comp
    e.symm.toContinuousLinearMap
  have hPA : P.comp A = ContinuousLinearMap.id ℂ (ComplexModel k) := by
    ext z : 1
    have hz := congrArg (fun w ↦ (e.symm w).1) (he z)
    simpa [P] using hz.symm
  obtain ⟨p, hpa, hpU, hp, hpC, hpiC⟩ :=
    complex_projected_inverse_smooth_restrict hU haU hgU P hPA hA
  let h : ComplexModel k → F := fun z ↦ (e.symm (g (p.symm z))).2
  have hgp : ContDiffOn ℂ ∞ (g ∘ p.symm) p.target :=
    hgU.comp hpiC (fun z hz ↦ hpU (p.map_target hz))
  have hh : ContDiffOn ℂ ∞ h p.target :=
    (e.symm.contDiff.comp_contDiffOn hgp).snd
  refine ⟨F, e, p, h, hpa, hpU.trans inter_subset_right, hpC, hpiC, hh, ?_⟩
  intro z hz
  apply e.symm.injective
  rw [e.symm_apply_apply]
  apply Prod.ext
  · change P (g z) = p z
    rw [hp]
    rfl
  · simp only [h, p.left_inv hz]

/-- The ambient graph subtraction is a smooth local homeomorphism over the graph domain, with inverse given by graph addition. (Demailly, I.7.15). -/
theorem complex_ambient_graph_chart
    {E F E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (e : (E × F) ≃L[ℂ] E') {U : Set E} (hU : IsOpen U)
    {h : E → F} (hh : ContDiffOn ℂ ∞ h U) :
    ∃ q : OpenPartialHomeomorph E' E',
      q.source = {y | (e.symm y).1 ∈ U} ∧ q.target = q.source ∧
      ContDiffOn ℂ ∞ q q.source ∧ ContDiffOn ℂ ∞ q.symm q.target ∧
      (∀ u ∈ U, q (e (u, h u)) = e (u, 0)) := by
  let V : Set E' := {y | (e.symm y).1 ∈ U}
  have hV : IsOpen V := hU.preimage (continuous_fst.comp e.symm.continuous)
  have hhc : ContDiffOn ℂ ∞ (fun y : E' ↦ h (e.symm y).1) V :=
    hh.comp e.symm.contDiff.fst.contDiffOn (fun _ hy ↦ hy)
  have hsub : ContDiffOn ℂ ∞
      (fun y : E' ↦ e ((e.symm y).1, (e.symm y).2 - h (e.symm y).1)) V :=
    e.contDiff.comp_contDiffOn
      (e.symm.contDiff.fst.contDiffOn.prodMk (e.symm.contDiff.snd.contDiffOn.sub hhc))
  have hadd : ContDiffOn ℂ ∞
      (fun y : E' ↦ e ((e.symm y).1, (e.symm y).2 + h (e.symm y).1)) V :=
    e.contDiff.comp_contDiffOn
      (e.symm.contDiff.fst.contDiffOn.prodMk (e.symm.contDiff.snd.contDiffOn.add hhc))
  let q : OpenPartialHomeomorph E' E' :=
    { toFun := fun y ↦ e ((e.symm y).1, (e.symm y).2 - h (e.symm y).1)
      invFun := fun y ↦ e ((e.symm y).1, (e.symm y).2 + h (e.symm y).1)
      source := V
      target := V
      map_source' := by intro y hy; simpa only [V, mem_ofPred_eq, e.symm_apply_apply] using hy
      map_target' := by intro y hy; simpa only [V, mem_ofPred_eq, e.symm_apply_apply] using hy
      left_inv' := by intro y hy; simp
      right_inv' := by intro y hy; simp
      continuousOn_toFun := hsub.continuousOn
      continuousOn_invFun := hadd.continuousOn
      open_source := hV
      open_target := hV }
  refine ⟨q, rfl, rfl, hsub, hadd, ?_⟩
  intro u hu
  simp [q]

/-- Composing a maximal-atlas chart with a smooth local coordinate change yields another chart in the same maximal atlas. -/
theorem complex_chart_trans_mem_maximalAtlas
    {k : ℕ} {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel k) L]
    [IsManifold (complexModel k) ∞ L]
    {c : OpenPartialHomeomorph L (ComplexModel k)}
    (hc : c ∈ IsManifold.maximalAtlas (complexModel k) ∞ L)
    (p : OpenPartialHomeomorph (ComplexModel k) (ComplexModel k))
    (hp : ContDiffOn ℂ ∞ p p.source) (hpi : ContDiffOn ℂ ∞ p.symm p.target) :
    c.trans p ∈ IsManifold.maximalAtlas (complexModel k) ∞ L := by
  apply (c.trans p).mem_maximalAtlas_of_contMDiffOn
  · exact hp.contMDiffOn.comp
      ((contMDiffOn_of_mem_maximalAtlas hc).mono inter_subset_left) inter_subset_right
  · exact (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
      (hpi.contMDiffOn.mono inter_subset_left) inter_subset_right


/-- A holomorphic map with split differential admits holomorphic coordinates in which it is a standard linear inclusion with a finite-dimensional complex complement. (Demailly, I.7.15, p. 60). -/
theorem complex_immersion_graph_charts
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (ComplexModel k) L]
    [IsManifold (complexModel k) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    {f : L → M} {x : L}
    (hf : ContMDiffAt (complexModel k) (complexModel d) ∞ f x)
    (hdiff : IsDiffImmersionAt (complexModel k) (complexModel d) f x) :
    ∃ (F : Submodule ℂ (ComplexModel d))
      (e : (ComplexModel k × F) ≃L[ℂ] ComplexModel d)
      (a : OpenPartialHomeomorph L (ComplexModel k))
      (b : OpenPartialHomeomorph M (ComplexModel d)),
      x ∈ a.source ∧ f x ∈ b.source ∧
      a ∈ IsManifold.maximalAtlas (complexModel k) ∞ L ∧
      b ∈ IsManifold.maximalAtlas (complexModel d) ∞ M ∧
      a.source ⊆ f ⁻¹' b.source ∧
      Set.EqOn ((b.extend (complexModel d)) ∘ f ∘ (a.extend (complexModel k)).symm)
        (e ∘ (fun u ↦ (u, 0))) (a.extend (complexModel k)).target := by
  let c := chartAt (ComplexModel k) x
  let t := chartAt (ComplexModel d) (f x)
  let g : ComplexModel k → ComplexModel d := t ∘ f ∘ c.symm
  have hcx : x ∈ c.source := mem_chart_source _ _
  have htfx : f x ∈ t.source := mem_chart_source _ _
  obtain ⟨hg, hinj⟩ := complex_written_map_C1_fderivWithin_injective hf hdiff
  have hg' : ContDiffAt ℂ 1 g (c x) := by
    simpa [g, c, t, extChartAt, complexModel, mfld_simps,
      contDiffWithinAt_univ] using hg
  have hinj' : Function.Injective (fderiv ℂ g (c x)) := by
    simpa [g, c, t, extChartAt, complexModel, mfld_simps] using hinj
  obtain ⟨U, hU, hxU, hUc, hUf⟩ := complex_chart_domain_at hf
  have hUf' : MapsTo f U t.source := by
    simpa [t] using hUf
  let S := c.target ∩ c.symm ⁻¹' U
  have hS : IsOpen S := c.isOpen_inter_preimage_symm hU
  have hcxS : c x ∈ S := ⟨c.map_source hcx, by
    change c.symm (c x) ∈ U
    simpa only [c.left_inv hcx] using hxU⟩
  obtain ⟨F, e, p, h, hpa, hpS, hpC, hpiC, hh, hgraph⟩ :=
    complex_euclidean_smooth_graph hS hcxS hg'
      hg'.differentiableAt_one.hasFDerivAt hinj'
  obtain ⟨q, hqsource, hqtarget, hqC, hqiC, hqgraph⟩ :=
    complex_ambient_graph_chart e p.open_target hh
  let a := c.trans p
  let b := t.trans q
  have hxa : x ∈ a.source := ⟨hcx, hpa⟩
  have hgfx : g (c x) = t (f x) := by simp only [g, Function.comp_apply, c.left_inv hcx]
  have hqin : ∀ z ∈ p.source, g z ∈ q.source := by
    intro z hz
    rw [hqsource, hgraph z hz]
    simpa only [mem_ofPred_eq, e.symm_apply_apply] using p.map_source hz
  have hfxb : f x ∈ b.source := by
    change f x ∈ t.source ∧ t (f x) ∈ q.source
    exact ⟨htfx, hgfx ▸ hqin (c x) hpa⟩
  have haAtlas : a ∈ IsManifold.maximalAtlas (complexModel k) ∞ L :=
    complex_chart_trans_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) p hpC hpiC
  have hbAtlas : b ∈ IsManifold.maximalAtlas (complexModel d) ∞ M :=
    complex_chart_trans_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (f x)) q hqC hqiC
  refine ⟨F, e, a, b, hxa, hfxb, haAtlas, hbAtlas, ?_, ?_⟩
  · intro z hz
    change z ∈ c.source ∧ c z ∈ p.source at hz
    have hzU : z ∈ U := by
      have h := (hpS hz.2).2
      change c.symm (c z) ∈ U at h
      simpa only [c.left_inv hz.1] using h
    change f z ∈ t.source ∧ t (f z) ∈ q.source
    refine ⟨hUf' hzU, ?_⟩
    have h := hqin (c z) hz.2
    simpa only [g, Function.comp_apply, c.left_inv hz.1] using h
  · intro u hu
    have hu' : u ∈ a.target := by
      simpa [OpenPartialHomeomorph.extend_target, complexModel, mfld_simps] using hu
    change q (g (p.symm u)) = e (u, 0)
    rw [hgraph (p.symm u) (p.map_target hu'.1), p.right_inv hu'.1]
    exact hqgraph u hu'.1


end HolomorphicAnosov
