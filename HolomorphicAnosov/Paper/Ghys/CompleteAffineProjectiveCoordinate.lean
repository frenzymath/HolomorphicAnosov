import HolomorphicAnosov.Geometry.TransverseMobiusUniqueness
import HolomorphicAnosov.Geometry.ComplexMobiusPSLNormalization
import HolomorphicAnosov.SurfaceTorusSupport.ProjectiveActionHolomorphic
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveAffineRange

/-! This file shows that locally projective maps on complete affine curves give global coordinates
onto punctured projective lines. (Ghys, §5, pp. 597–598; Thurston, §3.5, pp. 34–35) -/

noncomputable section
open Set Filter _root_.Topology IsManifold
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

lemma affine_transformation_mobius (a : ComplexAffineTransformation) :
    ∃ g : MobiusGroup, ∀ z : ℂ, g.apply (z : OnePoint ℂ) = (a.apply z : OnePoint ℂ) := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![a.slope, a.translation; 0, 1]
  have hdet : M.det ≠ 0 := by simpa [M, Matrix.det_fin_two] using a.slope_ne_zero
  let m := Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet
  refine ⟨⟨MulAction.toPerm m, ⟨m, rfl⟩⟩, ?_⟩
  intro z
  change m • (z : OnePoint ℂ) = _
  rw [OnePoint.smul_some_eq_ite]
  simp [m, M, ComplexAffineTransformation.apply]

lemma psl_transformation_mobius (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) :
    ∃ g : MobiusGroup, ∀ p : ComplexProjectiveLine,
      (OnePoint.equivProjectivization ℂ).symm (a • p) =
        g.apply ((OnePoint.equivProjectivization ℂ).symm p) := by
  induction a using QuotientGroup.induction_on with
  | H m =>
    refine ⟨complexMobiusToMobiusGroup (ComplexMobiusTransformation.ofMatrix m), ?_⟩
    intro p
    rw [← complexMobiusToMobiusGroup_intertwines]
    congr 1

/-- A map locally given by Möbius transformations of a fixed open coordinate on a connected domain
is globally given by one Möbius transformation. (Thurston, §3.5, pp. 34–35) -/
theorem mobius_formula_global_of_local
    {L : Type*} [TopologicalSpace L] [PreconnectedSpace L]
    (e : L → ℂ) (he : IsOpenMap e) (k : L → OnePoint ℂ)
    (hloc : ∀ x, ∃ g : MobiusGroup, ∀ᶠ y in 𝓝 x, k y = g.apply (e y))
    (x₀ : L) : ∃ g : MobiusGroup, ∀ y, k y = g.apply (e y) := by
  obtain ⟨g₀, hg₀⟩ := hloc x₀
  refine ⟨g₀, congrFun (eq_of_locally_propagating_germs k
    (fun y ↦ g₀.apply (e y)) ?_ x₀ hg₀)⟩
  intro x
  obtain ⟨g, hg⟩ := hloc x
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hg
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy hyeq
  obtain ⟨V, hVsub, hV, hyV⟩ := mem_nhds_iff.mp hyeq
  have hlabel : g = g₀ := by
    apply mobius_eq_of_infinite_finite_eq g g₀ (e '' (U ∩ V))
    · exact infinite_of_mem_nhds (e y) ((he _ (hU.inter hV)).mem_nhds
        ⟨y, ⟨hy, hyV⟩, rfl⟩)
    · rintro z ⟨w, hw, rfl⟩
      exact (hUsub hw.1).symm.trans (hVsub hw.2)
  intro z hz
  simpa only [hlabel, Set.mem_ofPred_eq] using hUsub hz

/-- Each maximal affine chart is locally an affine transformation of the specified complete plane
coordinate. (Ghys, §3, p. 590) -/
lemma complete_coordinate_chart_affine
    {L : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineStructure L)
    (e : Diffeomorph (complexModel 1) 𝓘(ℂ) L ℂ ∞)
    (he : ∀ c ∈ A.out.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, e y = a.apply (c y))
    (c : OpenPartialHomeomorph L ℂ) (hc : c ∈ ComplexAffineStructure.maximalAtlas L A)
    (x : L) (hx : x ∈ c.source) :
    ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, c y = a.apply (e y) := by
  obtain ⟨d, hd, hxd⟩ := A.out.cover x
  obtain ⟨a, ha⟩ := hc.2 d hd x ⟨hxd, hx⟩
  obtain ⟨b, hb⟩ := he d hd x hxd
  refine ⟨⟨a.slope / b.slope, div_ne_zero a.slope_ne_zero b.slope_ne_zero,
    a.translation - a.slope / b.slope * b.translation⟩, ?_⟩
  filter_upwards [ha, hb] with y hay hby
  rw [hay, hby]
  dsimp [ComplexAffineTransformation.apply]
  field_simp [b.slope_ne_zero]
  ring

/-- A map locally projective in a complete affine structure is globally a projective transformation
of a complete affine coordinate. (Ghys, §5, pp. 597–598; Thurston, §3.5, pp. 34–35) -/
theorem complete_affine_projective_global_formula
    {L : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineStructure L) (hA : ComplexAffineStructure.Complete L A)
    (k : L → ComplexProjectiveLine)
    (hloc : ∀ x, ∃ c ∈ ComplexAffineStructure.maximalAtlas L A,
      x ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
        ∀ᶠ y in 𝓝 x, k y = g • complexProjectiveLineFinite (c y))
    (x₀ : L) :
    ∃ e : Diffeomorph (complexModel 1) 𝓘(ℂ) L ℂ ∞,
      ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
        ∀ y, k y = g • complexProjectiveLineFinite (e y) := by
  let : SimplyConnectedSpace L := hA.1
  obtain ⟨e, he⟩ := hA.2
  have hform : ∀ x, ∃ g : MobiusGroup, ∀ᶠ y in 𝓝 x,
      (OnePoint.equivProjectivization ℂ).symm (k y) = g.apply (e y) := by
    intro x
    obtain ⟨c, hc, hx, a, ha⟩ := hloc x
    obtain ⟨b, hb⟩ := complete_coordinate_chart_affine A e he c hc x hx
    obtain ⟨g, hg⟩ := psl_transformation_mobius a
    obtain ⟨h, hh⟩ := affine_transformation_mobius b
    refine ⟨g * h, ?_⟩
    filter_upwards [ha, hb] with y hay hby
    rw [hay, hg, complexProjectiveLineFinite_to_onePoint, hby, ← hh]
    rfl
  obtain ⟨g, hg⟩ := mobius_formula_global_of_local e e.toHomeomorph.isOpenMap
    (fun y ↦ (OnePoint.equivProjectivization ℂ).symm (k y)) hform x₀
  obtain ⟨a, ha, _⟩ := complex_mobius_psl_normalization (mobiusGroupToComplexMobius g)
  refine ⟨e, a, ?_⟩
  intro y
  rw [ha, mobiusGroupToComplexMobius_apply, complexProjectiveLineFinite_to_onePoint]
  exact (Equiv.symm_apply_eq (OnePoint.equivProjectivization ℂ)).mp (hg y)

/-- A projective transformation of a complete affine coordinate is a biholomorphic chart onto the
complement of its transformed infinity. (Ghys, §5, pp. 597–598) -/
theorem projective_affine_coordinate_chart
    {L : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (e : Diffeomorph (complexModel 1) 𝓘(ℂ) L ℂ ∞)
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) :
    ∃ q : OpenPartialHomeomorph L ComplexProjectiveLine,
      q.source = univ ∧ q.target = {g • complexProjectiveLineInfinity}ᶜ ∧
      (∀ x, q x = g • complexProjectiveLineFinite (e x)) ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ q q.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ q.symm q.target := by
  let h : ComplexProjectiveLine ≃ₜ ComplexProjectiveLine := {
    toEquiv := MulAction.toPerm g
    continuous_toFun := (projective_special_linear_action_contMDiff g).continuous
    continuous_invFun := (projective_special_linear_action_contMDiff g⁻¹).continuous }
  let b := e.toHomeomorph.toOpenPartialHomeomorph.trans canonicalPlaneCoordinate.symm
  let c := b.trans (complexProjectiveLineChart 1).symm
  let q := c.trans h.toOpenPartialHomeomorph
  have hb : b.source = univ := by simp [b, canonicalPlaneCoordinate]
  have hc : c.source = univ := by simp [c, hb, complexProjectiveLineChart]
  have hq : q.source = univ := by simp [q, hc]
  have hfun (x : L) : q x = g • complexProjectiveLineFinite (e x) := rfl
  have hrange : q.target = {g • complexProjectiveLineInfinity}ᶜ := by
    rw [← q.image_source_eq_target, hq, image_univ]
    change range (fun x ↦ g • complexProjectiveLineFinite (e x)) = _
    exact developing_projective_affine_range e e.toEquiv.surjective g
  have hchart : complexProjectiveLineChart 1 ∈ maximalAtlas (complexModel 1) ∞
      ComplexProjectiveLine := IsManifold.subset_maximalAtlas ⟨1, rfl⟩
  have hbhol : ContMDiff (complexModel 1) (complexModel 1) ∞ b := by
    exact (contMDiffOn_univ.mp canonicalPlaneCoordinate_properties.2.1.2).comp e.contMDiff
  have hchol : ContMDiff (complexModel 1) (complexModel 1) ∞ c := by
    exact (contMDiffOn_univ.mp (contMDiffOn_symm_of_mem_maximalAtlas hchart)).comp hbhol
  refine ⟨q, hq, hrange, hfun,
    ((projective_special_linear_action_contMDiff g).comp hchol).contMDiffOn, ?_⟩
  have hbihol : ContMDiff (complexModel 1) (complexModel 1) ∞ b.symm := by
    exact e.symm.contMDiff.comp
      (contMDiffOn_univ.mp canonicalPlaneCoordinate_properties.2.1.1)
  apply hbihol.comp_contMDiffOn
    ((contMDiffOn_of_mem_maximalAtlas hchart).comp
      (projective_special_linear_action_contMDiff g⁻¹).contMDiffOn ?_)
  intro z hz
  exact hz.2.1

/-- A map locally projective in a complete affine structure is a biholomorphic coordinate onto a
punctured projective line. (Ghys, §5, pp. 597–598; Thurston, §3.5, pp. 34–35) -/
theorem complete_affine_projective_coordinate
    {L : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A : ComplexAffineStructure L) (hA : ComplexAffineStructure.Complete L A)
    (k : L → ComplexProjectiveLine)
    (hloc : ∀ x, ∃ c ∈ ComplexAffineStructure.maximalAtlas L A,
      x ∈ c.source ∧ ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ,
        ∀ᶠ y in 𝓝 x, k y = g • complexProjectiveLineFinite (c y))
    (x₀ : L) : ∃ (pole : ComplexProjectiveLine)
      (q : OpenPartialHomeomorph L ComplexProjectiveLine),
      q.source = univ ∧ q.target = {pole}ᶜ ∧ (∀ y, q y = k y) ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ q q.source ∧
      ContMDiffOn (complexModel 1) (complexModel 1) ∞ q.symm q.target := by
  obtain ⟨e, g, hg⟩ := complete_affine_projective_global_formula A hA k hloc x₀
  obtain ⟨q, hs, ht, he, hh, hi⟩ := projective_affine_coordinate_chart e g
  exact ⟨g • complexProjectiveLineInfinity, q, hs, ht,
    fun y ↦ (he y).trans (hg y).symm, hh, hi⟩

end HolomorphicAnosov.Ghys

