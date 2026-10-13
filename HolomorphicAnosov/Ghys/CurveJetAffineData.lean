import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.CurveJetTruncationBase
import HolomorphicAnosov.Ghys.LeafJetComplexManifold
import HolomorphicAnosov.Ghys.CurveJetReparametrization

/-! Coefficient atlases, homogeneous holomorphic jet sections, and their correspondence with complex
affine structures. (Ghys, Lemma 3.2) -/

open Filter Set
open scoped Topology _root_.Topology Manifold ContDiff
noncomputable section
namespace HolomorphicAnosov.Ghys
universe u v
variable (L : Type u) [TopologicalSpace L] [ChartedSpace ℂ L]

/-- The charted space obtained from scalar curve charts by identifying ℂ with the one-coordinate
product `ComplexModel 1`. (Ghys, p.590) -/
@[instance_reducible]
def curveScalarToProductChartedSpace : ChartedSpace (ComplexModel 1) L := by
  letI : ChartedSpace (ComplexModel 1) ℂ :=
    (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).chartedSpace
  exact ChartedSpace.comp (ComplexModel 1) ℂ L

attribute [local instance] curveScalarToProductChartedSpace

section ModelChange

variable {L}

/-- The inverse product-model chart is the scalar inverse chart composed with evaluation at the
unique coordinate. -/
theorem curveScalarToProduct_chart_symm (x : L) :
    (chartAt (ComplexModel 1) x).symm =
      (chartAt ℂ x).symm ∘ (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)) := by
  let : ChartedSpace (ComplexModel 1) ℂ :=
    (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).chartedSpace
  change (⇑((chartAt ℂ x).trans (chartAt (ComplexModel 1) (chartAt ℂ x x))).symm) = _
  rw [OpenPartialHomeomorph.coe_trans_symm]
  congr 1
  change (⇑(((Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).isLocalHomeomorph.localInverseAt _).trans
    (OpenPartialHomeomorph.refl _)).symm) = _
  simp only [OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.refl_symm,
    IsLocalHomeomorph.localInverseAt_symm]
  rfl

/-- On its source, the product-model chart inserts the scalar chart value into its unique
coordinate. -/
theorem curveScalarToProduct_chart_apply (x y : L) (hy : y ∈ (chartAt (ComplexModel 1) x).source) :
    chartAt (ComplexModel 1) x y =
      (Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)).symm (chartAt ℂ x y) := by
  let e := Homeomorph.piUnique (fun _ : Fin 1 ↦ ℂ)
  apply e.injective
  rw [e.apply_symm_apply]
  change e ((e.isLocalHomeomorph.localInverseAt _) (chartAt ℂ x y)) = _
  apply IsLocalHomeomorph.apply_localInverseAt_of_mem
  exact hy.2.1

variable {L' : Type v} [TopologicalSpace L'] [ChartedSpace ℂ L']
/-- A map holomorphic in scalar curve charts is holomorphic in the corresponding one-coordinate
product charts. -/
theorem curveScalarToProduct_contMDiff {f : L → L'}
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ f) :
    ContMDiff (complexModel 1) (complexModel 1) ∞ f := by
  intro x
  have hs := (contMDiffAt_iff.mp (hf x)).2
  have hc := (contMDiffAt_iff.mp (hf x)).1
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.range_id, contDiffWithinAt_univ] at hs
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  change ContDiffWithinAt ℂ ∞ _ (Set.range (modelWithCornersSelf ℂ (ComplexModel 1))) _
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.range_id, contDiffWithinAt_univ]
  let e := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  have he : e (chartAt (ComplexModel 1) x x) = chartAt ℂ x x := by
    rw [curveScalarToProduct_chart_apply x x (mem_chart_source _ _)]
    exact e.apply_symm_apply _
  have hlinear := e.symm.contDiff.contDiffAt.comp (chartAt (ComplexModel 1) x x)
    ((he.symm ▸ hs).comp (chartAt (ComplexModel 1) x x) e.contDiff.contDiffAt)
  apply hlinear.congr_of_eventuallyEq
  have hnear : ∀ᶠ z in 𝓝 (chartAt (ComplexModel 1) x x),
      f ((chartAt (ComplexModel 1) x).symm z) ∈ (chartAt (ComplexModel 1) (f x)).source := by
    have hi := ((chartAt (ComplexModel 1) x).continuousAt_symm
      ((chartAt (ComplexModel 1) x).map_source (mem_chart_source _ x))).tendsto
    rw [(chartAt (ComplexModel 1) x).left_inv (mem_chart_source _ x)] at hi
    apply (hc.tendsto.comp hi).eventually
    exact (chartAt (ComplexModel 1) (f x)).open_source.mem_nhds (mem_chart_source _ _)
  filter_upwards [hnear] with z hz
  simp only [Function.comp_apply, curveScalarToProduct_chart_symm]
  rw [curveScalarToProduct_chart_symm] at hz
  exact curveScalarToProduct_chart_apply (f x) _ hz

end ModelChange

/-- The identity is holomorphic from the scalar model to the corresponding product model. -/
theorem curveScalarToProduct_contMDiff_id :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (complexModel 1) ∞ (id : L → L) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_id, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.range_id, contDiffWithinAt_univ]
  let e := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  have hlinear : ContDiffAt ℂ ∞ (e.symm : ℂ → ComplexModel 1) (chartAt ℂ x x) :=
    e.symm.contDiff.contDiffAt
  apply hlinear.congr_of_eventuallyEq
  have hi := (chartAt ℂ x).continuousAt_symm
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  have hnear := hi.preimage_mem_nhds (by
    simpa only [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using
      (chartAt (ComplexModel 1) x).open_source.mem_nhds (mem_chart_source _ x))
  filter_upwards [hnear, (chartAt ℂ x).open_target.mem_nhds
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x))] with z hz hzt
  simp only [Function.comp_apply, id_eq]
  rw [curveScalarToProduct_chart_apply x _ hz, (chartAt ℂ x).right_inv hzt]
  rfl

/-- The identity is holomorphic from the corresponding product model to the scalar model. -/
theorem curveProductToScalar_contMDiff_id :
    ContMDiff (complexModel 1) (modelWithCornersSelf ℂ ℂ) ∞ (id : L → L) := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_id, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.range_id, contDiffWithinAt_univ]
  let e := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)
  have hlinear : ContDiffAt ℂ ∞ (e : ComplexModel 1 → ℂ)
      (chartAt (ComplexModel 1) x x) := e.contDiff.contDiffAt
  apply hlinear.congr_of_eventuallyEq
  have he : e (chartAt (ComplexModel 1) x x) = chartAt ℂ x x := by
    rw [curveScalarToProduct_chart_apply x x (mem_chart_source _ _)]
    exact e.apply_symm_apply _
  have hnear := e.continuous.continuousAt.preimage_mem_nhds
    ((chartAt ℂ x).open_target.mem_nhds
      (he.symm ▸ (chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  filter_upwards [hnear] with z hz
  simp only [Function.comp_apply, curveScalarToProduct_chart_symm]
  exact (chartAt ℂ x).right_inv hz

/-- A scalar chart is holomorphic exactly when it belongs to the scalar maximal atlas. -/
theorem isHolomorphicScalarChart_iff_mem_scalar_maximalAtlas
    [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]
    (c : OpenPartialHomeomorph L ℂ) :
    IsHolomorphicScalarChart L c ↔
      c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) ∞ L := by
  rw [IsManifold.mem_maximalAtlas_iff_contMDiffOn]
  constructor
  · intro h
    exact ⟨h.1.comp (curveScalarToProduct_contMDiff_id L).contMDiffOn (fun _ hx ↦ hx),
      (curveProductToScalar_contMDiff_id L).comp_contMDiffOn h.2⟩
  · intro h
    exact ⟨h.1.comp (curveProductToScalar_contMDiff_id L).contMDiffOn (fun _ hx ↦ hx),
      (curveScalarToProduct_contMDiff_id L).comp_contMDiffOn h.2⟩


variable [IsManifold (modelWithCornersSelf ℂ ℂ) ∞ L]

/-- The first- and second-jet atlases consist of holomorphic coefficient charts associated to leaf
charts. (Ghys, p.591) -/
def CurveJetCoefficientAtlases
    (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
    (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)) : Prop :=
  letI := A1
  letI := A2
  IsManifold (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ (CurveJet1 L) ∧
  IsManifold (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ (CurveJet2 L) ∧
  (∀ c : LeafChart L,
    ∃ (e1 : OpenPartialHomeomorph (CurveJet1 L) (ℂ × ℂ))
      (e2 : OpenPartialHomeomorph (CurveJet2 L) ((ℂ × ℂ) × ℂ)),
      e1 ∈ atlas (ℂ × ℂ) (CurveJet1 L) ∧
      e2 ∈ atlas ((ℂ × ℂ) × ℂ) (CurveJet2 L) ∧
      e1.source = (curveJet1Base L) ⁻¹' c.1.source ∧
      e2.source = (curveJet2Base L) ⁻¹' c.1.source ∧
      e1.target = curveJet1Target L c ∧ e2.target = curveJet2Target L c ∧
      EqOn e1 (curveJet1Coeff L c) e1.source ∧
      EqOn e2 (curveJet2Coeff L c) e2.source ∧
      ContMDiffOn (modelWithCornersSelf ℂ (ℂ × ℂ))
        (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ e1 e1.source ∧
      ContMDiffOn (modelWithCornersSelf ℂ (ℂ × ℂ))
        (modelWithCornersSelf ℂ (ℂ × ℂ)) ∞ e1.symm e1.target ∧
      ContMDiffOn (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
        (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ e2 e2.source ∧
      ContMDiffOn (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ))
        (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ e2.symm e2.target) ∧
  (∀ e ∈ atlas (ℂ × ℂ) (CurveJet1 L), ∃ c : LeafChart L,
    e.source = (curveJet1Base L) ⁻¹' c.1.source ∧
    e.target = curveJet1Target L c ∧ EqOn e (curveJet1Coeff L c) e.source) ∧
  (∀ e ∈ atlas ((ℂ × ℂ) × ℂ) (CurveJet2 L), ∃ c : LeafChart L,
    e.source = (curveJet2Base L) ⁻¹' c.1.source ∧
    e.target = curveJet2Target L c ∧ EqOn e (curveJet2Coeff L c) e.source)

/-- Holomorphic sections of jet truncation that commute with nonzero scalar source changes. (Ghys,
Lemma 3.2) -/
def HomogeneousCurveJetSection
    (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
    (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)) :=
  letI := A1
  letI := A2
  {σ : CurveJet1 L → CurveJet2 L //
    (∀ j, curveJetTruncation L (σ j) = j) ∧
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ℂ))
      (modelWithCornersSelf ℂ ((ℂ × ℂ) × ℂ)) ∞ σ ∧
    ∀ (omega : ℂˣ) (j : CurveJet1 L),
      σ (curveJet1Scale L omega j) = curveJet2Reparametrize L (.scale omega) (σ j)}

/-- An equivalence between complex affine structures and homogeneous holomorphic jet sections,
characterized by vanishing second coefficients in affine charts. (Ghys, p.591) -/
structure CurveJetAffineCorrespondence
    (A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L))
    (A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)) where
  equiv : ComplexAffineStructure L ≃ HomogeneousCurveJetSection L A1 A2
  affine_parametrization : ∀ (F : ComplexAffineStructure L)
    (c : OpenPartialHomeomorph L ℂ), c ∈ ComplexAffineStructure.maximalAtlas L F →
    ∀ γ : CurveParamGerm L, curveGermBase L γ.1 ∈ c.source →
      ((equiv F).1 (curveJet1Class L γ) = curveJet2Class L γ ↔
        germSecond (γ.1.map (c : L → ℂ)) = 0)
  flat_chart_iff : ∀ (F : ComplexAffineStructure L) (c : OpenPartialHomeomorph L ℂ),
    c ∈ ComplexAffineStructure.maximalAtlas L F ↔
      IsHolomorphicScalarChart L c ∧
      ∀ γ : CurveParamGerm L, curveGermBase L γ.1 ∈ c.source →
        ((equiv F).1 (curveJet1Class L γ) = curveJet2Class L γ ↔
          germSecond (γ.1.map (c : L → ℂ)) = 0)


theorem homogeneous_curve_jet_section_coeff_scale
    [T2Space L] [SecondCountableTopology L]
    {A1 : ChartedSpace (ℂ × ℂ) (CurveJet1 L)}
    {A2 : ChartedSpace ((ℂ × ℂ) × ℂ) (CurveJet2 L)}
    (σ : HomogeneousCurveJetSection L A1 A2)
    (omega : ℂˣ) (j : CurveJet1 L) (c : LeafChart L)
    (hj : curveJet1Base L j ∈ c.1.source) :
    curveJet2Coeff L c (σ.1 (curveJet1Scale L omega j)) =
      (((curveJet2Coeff L c (σ.1 j)).1.1,
          (omega : ℂ) * (curveJet2Coeff L c (σ.1 j)).1.2),
        (omega : ℂ) ^ 2 * (curveJet2Coeff L c (σ.1 j)).2) := by
  have hbase : curveJet2Base L (σ.1 j) = curveJet1Base L j := by
    rw [← curve_jet_truncation_base L (σ.1 j), σ.2.1 j]
  have hc : curveJet2Base L (σ.1 j) ∈ c.1.source := by
    rw [hbase]
    exact hj
  obtain ⟨_, _, hcoeff, _⟩ := curve_jet_reparametrization L
  rw [σ.2.2.2 omega j]
  simpa [CurveJetReparametrization.scale] using
    hcoeff (.scale omega) (σ.1 j) |>.2.2 c hc

end HolomorphicAnosov.Ghys
