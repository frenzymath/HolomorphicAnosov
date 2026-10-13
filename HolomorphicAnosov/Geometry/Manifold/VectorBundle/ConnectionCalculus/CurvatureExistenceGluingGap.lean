import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalFrameConnectionForm
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferentialChartTransportG12
import HolomorphicAnosov.Analysis.ScalarGaugePullbackCurvature
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameCover

/-! This file constructs intrinsic curvature from local connection forms and proves agreement on
chart and holomorphic-frame overlaps. (Zhang, p.6; Demailly, V §3, p.256 and §14, p.273) -/

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

omit [IsManifold (complexModel d) ∞ X] in
private theorem chart_real_mdifferentiable
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) :
    c.MDifferentiable (realModel d) (realModel d) := by
  constructor
  · intro x hx
    obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp (contMDiffAt_of_mem_maximalAtlas hc hx)
    exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt
      (by simp) |>.mdifferentiableWithinAt
  · intro x hx
    obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp (contMDiffAt_symm_of_mem_maximalAtlas hc hx)
    exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt
      (by simp) |>.mdifferentiableWithinAt

omit [IsManifold (complexModel d) ∞ X] in
private theorem chart_transition_fderiv
    (c c' : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ c.target) (hz' : c.symm z ∈ c'.source) :
    fderiv ℝ (c' ∘ c.symm) z =
      (mfderiv (realModel d) (realModel d) c' (c.symm z)).comp
        (mfderiv (realModel d) (realModel d) c.symm z) := by
  have h1 := ((chart_real_mdifferentiable c hc).symm.mdifferentiableAt hz)
  have h2 := ((chart_real_mdifferentiable c' hc').mdifferentiableAt hz')
  rw [← mfderiv_eq_fderiv, mfderiv_comp z h2 h1]

private theorem coordinate_form_transition
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (D : QuotientLineConnection.Connection P)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (c c' : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ c.target) (hz' : c.symm z ∈ c'.source) :
    QuotientLineConnection.coordinateForm D e c z =
      (QuotientLineConnection.coordinateForm D e c' ((c' ∘ c.symm) z)).comp
        (fderiv ℝ (c' ∘ c.symm) z) := by
  have hbase := c'.left_inv hz'
  ext v
  simp only [QuotientLineConnection.coordinateForm, ContinuousLinearMap.comp_apply,
    Function.comp_apply]
  rw [hbase]
  change D.form V e (c.symm z) (mfderiv (realModel d) (realModel d) c.symm z v) =
    D.form V e (c.symm z) (mfderiv (realModel d) (realModel d) c'.symm
      (c' (c.symm z)) (fderiv ℝ (c' ∘ c.symm) z v))
  rw [chart_transition_fderiv c c' hc hc' z hz hz']
  exact congrArg (D.form V e (c.symm z))
    (congrArg (fun L ↦ L (mfderiv (realModel d) (realModel d) c.symm z v))
      ((chart_real_mdifferentiable c' hc').symm_comp_deriv hz')).symm

/-- Curvature coordinate expressions agree on chart and holomorphic-frame overlaps. (Demailly, V §3,
p.256) -/
theorem curvature_coordinate_overlap
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (D : QuotientLineConnection.Connection P)
    (hD : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (QuotientLineConnection.coordinateForm D e c)
        (c.target ∩ c.symm ⁻¹' (V : Set X)))
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (c c' : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ c.target) (hz' : c.symm z ∈ c'.source)
    (hzV : c.symm z ∈ V) (hzW : c.symm z ∈ W) (v w : ComplexModel d) :
    fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z v w -
      fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z w v =
    fderiv ℝ (QuotientLineConnection.coordinateForm D e' c') ((c' ∘ c.symm) z)
      (fderiv ℝ (c' ∘ c.symm) z v) (fderiv ℝ (c' ∘ c.symm) z w) -
    fderiv ℝ (QuotientLineConnection.coordinateForm D e' c') ((c' ∘ c.symm) z)
      (fderiv ℝ (c' ∘ c.symm) z w) (fderiv ℝ (c' ∘ c.symm) z v) := by
  let F := c' ∘ c.symm
  let g := fun y ↦ e'.coefficient e.sectionValue (c.symm y)
  have hcs := contMDiffAt_symm_of_mem_maximalAtlas hc hz
  have hFs := (contMDiffAt_of_mem_maximalAtlas hc' hz').comp z hcs
  have hF : ContDiffAt ℝ 2 F z := by
    have hFc : ContDiffAt ℂ ∞ F z := by
      simpa only [contMDiffAt_iff_contDiffAt] using hFs
    exact (hFc.restrict_scalars ℝ).of_le (by simp)
  have hgs := ((frame_coefficient_holomorphic hP hline W V e'
    e.sectionValue e.holomorphic).contMDiffAt
      ((W.isOpen.inter V.isOpen).mem_nhds ⟨hzW, hzV⟩)).comp z hcs
  have hg : ContDiffAt ℝ 2 g z := by
    have hgc : ContDiffAt ℂ ∞ g z := by
      simpa only [g, Function.comp_def, contMDiffAt_iff_contDiffAt] using hgs
    exact (hgc.restrict_scalars ℝ).of_le (by simp)
  have hg0 : g z ≠ 0 := frame_transition_nonzero W V e' e _ hzW hzV
  have hlocal : QuotientLineConnection.coordinateForm D e c =ᶠ[nhds z]
      (fun y ↦ (g y)⁻¹ • fderiv ℝ g y +
        (QuotientLineConnection.coordinateForm D e' c' (F y)).comp (fderiv ℝ F y)) := by
    filter_upwards [c.open_target.mem_nhds hz,
      hcs.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hzV),
      hcs.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds hzW),
      hcs.continuousAt.preimage_mem_nhds (c'.open_source.mem_nhds hz')]
      with y hyT hyV hyW hyS
    have hgdiff := frame_coefficient_real_differentiableAt hP hline W V e'
      e.sectionValue e.holomorphic (c.symm y) hyW hyV
    have ht := coordinate_form_transition D W e' c c' hc hc' y hyT hyS
    unfold QuotientLineConnection.coordinateForm
    rw [D.gauge W V e' e (c.symm y) hyW hyV, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.smul_comp,
      scalar_differential_chart_transport _ c hc y hyT hgdiff]
    change QuotientLineConnection.coordinateForm D e' c y + _ = _
    rw [ht, add_comm]
    rfl
  rw [hlocal.fderiv_eq]
  apply scalar_gauge_pullback_curvature _ hF hg hg0
  have hzTarget : F z ∈ c'.target ∩ c'.symm ⁻¹' (W : Set X) := by
    refine ⟨c'.map_source hz', ?_⟩
    change c'.symm (c' (c.symm z)) ∈ W
    rw [c'.left_inv hz']
    exact hzW
  exact ((hD W e' c' hc').contDiffAt
    ((c'.isOpen_inter_preimage_symm W.isOpen).mem_nhds hzTarget)).differentiableAt (by simp)

/-- The real exterior derivatives of the local forms of a smooth quotient-line connection define an
intrinsic curvature representative. (Zhang, p.6; Demailly, V §3, p.256) -/
theorem exists_curvature_representative_gap
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    {r : ℕ} (hP : IsHolomorphicTangentSubbundle r P)
    (hline : IsQuotientTangentLine P)
    (D : QuotientLineConnection.Connection P)
    (hD : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (QuotientLineConnection.coordinateForm D e c)
        (c.target ∩ c.symm ⁻¹' (V : Set X))) :
    ∃ R : (x : X) → TangentSpace (realModel d) x →L[ℝ]
          (TangentSpace (realModel d) x →L[ℝ] ℂ),
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ∀ z ∈ c.target ∩ c.symm ⁻¹' (V : Set X), ∀ v w : ComplexModel d,
          R (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z
              ((NormedSpace.fromTangentSpace z).symm v))
            (mfderiv (realModel d) (realModel d) c.symm z
              ((NormedSpace.fromTangentSpace z).symm w)) =
            fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z v w -
              fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z w v := by
  classical
  choose V hxV e using fun x ↦ (holomorphic_frame_cover P hP hline x)
  let E := ComplexModel d
  let c := fun x : X ↦ chartAt E x
  let A := fun x : X ↦ fderiv ℝ (QuotientLineConnection.coordinateForm D (e x).some (c x)) (c x x)
  let J := fun x : X ↦ mfderiv (realModel d) (realModel d) (c x) x
  let R : (x : X) → TangentSpace (realModel d) x →L[ℝ]
      (TangentSpace (realModel d) x →L[ℝ] ℂ) := fun x ↦
    ((ContinuousLinearMap.compL ℝ E E ℂ).flip (J x)).comp
      (((A x) - (A x).flip).comp (J x))
  refine ⟨R, ?_⟩
  intro W e' c' hc' z hz v w
  let x := c'.symm z
  have hxC : x ∈ (c x).source := mem_chart_source _ x
  have hc : c x ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
    IsManifold.chart_mem_maximalAtlas x
  have hover := curvature_coordinate_overlap P hP hline D hD W (V x) e' (e x).some
    c' (c x) hc' hc z hz.1 hxC hz.2 (hxV x) v w
  have hder := chart_transition_fderiv c' (c x) hc' hc z hz.1 hxC
  change R x (mfderiv (realModel d) (realModel d) c'.symm z v)
    (mfderiv (realModel d) (realModel d) c'.symm z w) = _
  rw [hover, hder]
  rfl

end HolomorphicAnosov.ConnectionCalculus
