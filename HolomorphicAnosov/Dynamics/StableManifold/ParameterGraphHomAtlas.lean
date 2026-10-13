import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import Mathlib.Topology.VectorBundle.Hom
import HolomorphicAnosov.Analysis.FrameOperatorNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

noncomputable section
open Set
open scoped Topology
namespace HolomorphicAnosov

namespace ParameterGraphVaryingCharts
variable {I B Z : Type*} [TopologicalSpace B]
  (D : I → Type*) [∀ i, TopologicalSpace (D i)] (π : Z → B)
  (e : ∀ i, Bundle.Pretrivialization (D i) π)

/-- The chart-generated topology for locally varying finite-dimensional models.
This is the coinduced chart topology of `FiberPrebundle.totalSpaceTopology`,
allowing the model to depend on the chart index. -/
@[instance_reducible]
def topology : TopologicalSpace Z :=
  ⨆ i, TopologicalSpace.coinduced (e i).setSymm inferInstance


lemma continuous_symm (i : I) :
    @ContinuousOn _ _ _ (topology D π e) (e i).toPartialEquiv.symm (e i).target := by
  let := topology D π e
  refine fun z H U h ↦ preimage_nhdsWithin_coinduced' H (Filter.le_def.1 (nhds_mono ?_) U h)
  exact le_iSup (α := TopologicalSpace Z) (fun i ↦
    TopologicalSpace.coinduced (e i).setSymm inferInstance) i

lemma isOpen_source (i : I) : @IsOpen Z (topology D π e) (e i).source := by
  let := topology D π e
  refine isOpen_iSup_iff.mpr fun j ↦ ?_
  refine isOpen_coinduced.mpr (isOpen_induced_iff.mpr ⟨(e i).baseSet ×ˢ (Set.univ : Set (D j)), (e i).open_baseSet.prod isOpen_univ, ?_⟩)
  ext ⟨x,hx⟩
  simp only [mem_preimage, Bundle.Pretrivialization.setSymm, domRestrict,
    Set.mem_prod, Set.mem_univ, and_true, (e i).mem_source, (e j).proj_symm_apply hx]

lemma isOpen_overlap (i j : I) :
    IsOpen ((e j).target ∩ (e j).toPartialEquiv.symm ⁻¹' (e i).source) := by
  let := topology D π e
  obtain ⟨u,hu1,hu2⟩ := continuousOn_iff'.mp (continuous_symm D π e j)
    (e i).source (isOpen_source D π e i)
  rw [inter_comm,hu2]
  exact hu1.inter (e j).open_target

/-- Compatible pretrivializations with varying models become genuine bundle
charts in their coinduced topology. This is the same open-set argument as
Mathlib's fixed-model `FiberPrebundle.trivializationOfMemPretrivializationAtlas`. -/
def trivialization
    (hcompat : ∀ i j, ContinuousOn ((e i) ∘ (e j).toPartialEquiv.symm)
      ((e j).target ∩ (e j).toPartialEquiv.symm ⁻¹' (e i).source))
    (i : I) : @Bundle.Trivialization B (D i) Z _ _ (topology D π e) π :=
  let := topology D π e
  { e i with
    open_source := isOpen_source D π e i
    continuousOn_toFun := by
      refine continuousOn_iff'.mpr fun s hs ↦ ⟨(e i) ⁻¹' s ∩ (e i).source,
        isOpen_iSup_iff.mpr fun j ↦ ?_, by rw [inter_assoc, inter_self]; rfl⟩
      rw [isOpen_coinduced, isOpen_induced_iff]
      obtain ⟨u,hu1,hu2⟩ := continuousOn_iff'.mp (hcompat i j) s hs
      have hu3 := congrArg (fun s ↦ (fun x : (e j).target ↦ (x : B × D j)) ⁻¹' s) hu2
      simp only [Subtype.coe_preimage_self, preimage_inter, univ_inter] at hu3
      refine ⟨u ∩ (e j).target ∩ (e j).toPartialEquiv.symm ⁻¹' (e i).source, ?_, by
        simp only [preimage_inter, inter_univ, Subtype.coe_preimage_self, hu3.symm]; rfl⟩
      rw [inter_assoc]
      exact hu1.inter (isOpen_overlap D π e i j)
    continuousOn_invFun := continuous_symm D π e i }

end ParameterGraphVaryingCharts
namespace ParameterGraphHomAtlas
attribute [local instance] Classical.propDecidable
variable {A : Type*} [TopologicalSpace A] {E F : A → Type*}
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
  (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))

abbrev HomModel (i : A) := FiniteFiberModel (e.rank i) →L[ℝ] FiniteFiberModel (f.rank i)
def rank (i : A) : ℕ := Module.finrank ℝ (HomModel e f i)
lemma rank_eq_mul (i : A) : rank e f i = e.rank i * f.rank i := by
  have h := (LinearMap.toContinuousLinearMap :
    (FiniteFiberModel (e.rank i) →ₗ[ℝ] FiniteFiberModel (f.rank i)) ≃ₗ[ℝ]
      HomModel e f i).finrank_eq
  change Module.finrank ℝ (HomModel e f i) = _
  rw [← h,Module.finrank_linearMap]
  simp [FiniteFiberModel]

def baseSet (i : A) : Set A := (e.chart i).baseSet ∩ (f.chart i).baseSet

def modelEquiv (i : A) : HomModel e f i ≃L[ℝ] FiniteFiberModel (rank e f i) :=
  ContinuousLinearEquiv.ofFinrankEq ((finrank_euclideanSpace_fin (𝕜 := ℝ)).symm)

def coordinates (i p : A) (hp : p ∈ baseSet e f i) :
    (E p →L[ℝ] F p) ≃L[ℝ] FiniteFiberModel (rank e f i) :=
  ((e.coordinates i p hp.1).arrowCongr (f.coordinates i p hp.2)).trans (modelEquiv e f i)

/-- The actual conjugation chart on the bundle of original continuous linear maps. -/
def prechart (i : A) : Bundle.Pretrivialization (FiniteFiberModel (rank e f i))
    (fun z : Sigma (fun p ↦ E p →L[ℝ] F p) ↦ z.1) where
  toFun z := (z.1,if hz : z.1 ∈ baseSet e f i then coordinates e f i z.1 hz z.2 else 0)
  invFun z := ⟨z.1,if hz : z.1 ∈ baseSet e f i then (coordinates e f i z.1 hz).symm z.2 else 0⟩
  source := (fun z : Sigma (fun p ↦ E p →L[ℝ] F p) ↦ z.1) ⁻¹' baseSet e f i
  target := baseSet e f i ×ˢ univ
  map_source' := fun z hz ↦ ⟨hz,mem_univ _⟩
  map_target' := fun z hz ↦ hz.1
  left_inv' := by
    intro z hz
    simp only [mem_preimage] at hz
    simp only [dite_eq_left hz, ContinuousLinearEquiv.symm_apply_apply]
  right_inv' := by
    intro z hz
    simp only [mem_prod, mem_univ, and_true] at hz
    simp only [dite_eq_left hz, ContinuousLinearEquiv.apply_symm_apply]
  open_target := ((e.chart i).open_baseSet.inter (f.chart i).open_baseSet).prod isOpen_univ
  baseSet := baseSet e f i
  open_baseSet := (e.chart i).open_baseSet.inter (f.chart i).open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

lemma continuous_transition (i j : A) :
    Continuous (fun p : {p // p ∈ ParameterGraphHomAtlas.baseSet e f i ∩ ParameterGraphHomAtlas.baseSet e f j} ↦
      (ParameterGraphHomAtlas.coordinates e f j p.1 p.2.2).toContinuousLinearMap.comp
        (ParameterGraphHomAtlas.coordinates e f i p.1 p.2.1).symm.toContinuousLinearMap) := by
  let O := {p // p ∈ baseSet e f i ∩ baseSet e f j}
  have he : Continuous (fun p : O ↦
      (e.coordinates i p.1 p.2.1.1).toContinuousLinearMap.comp
        (e.coordinates j p.1 p.2.2.1).symm.toContinuousLinearMap) :=
    (e.continuous_transition j i).comp
      (continuous_subtype_val.subtype_mk (fun p : O ↦ ⟨p.2.2.1,p.2.1.1⟩))
  have hf : Continuous (fun p : O ↦
      (f.coordinates j p.1 p.2.2.2).toContinuousLinearMap.comp
        (f.coordinates i p.1 p.2.1.2).symm.toContinuousLinearMap) :=
    (f.continuous_transition i j).comp
      (continuous_subtype_val.subtype_mk (fun p : O ↦ ⟨p.2.1.2,p.2.2.2⟩))
  rw [continuous_clm_apply]
  intro v
  have hc := (modelEquiv e f j).continuous.comp
    (hf.clm_comp ((continuous_const (y := (modelEquiv e f i).symm v)).clm_comp he))
  apply hc.congr
  intro p
  change modelEquiv e f j
    (((f.coordinates j p.1 p.2.2.2).toContinuousLinearMap.comp
      (f.coordinates i p.1 p.2.1.2).symm.toContinuousLinearMap).comp
      (((modelEquiv e f i).symm v).comp
        ((e.coordinates i p.1 p.2.1.1).toContinuousLinearMap.comp
          (e.coordinates j p.1 p.2.2.1).symm.toContinuousLinearMap))) =
    coordinates e f j p.1 p.2.2 ((coordinates e f i p.1 p.2.1).symm v)
  apply congrArg (modelEquiv e f j)
  ext w
  rfl

lemma compatible (i j : A) :
    ContinuousOn ((prechart e f i) ∘ (prechart e f j).toPartialEquiv.symm)
      ((prechart e f j).target ∩ (prechart e f j).toPartialEquiv.symm ⁻¹' (prechart e f i).source) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let O := ((prechart e f j).target ∩
    (prechart e f j).toPartialEquiv.symm ⁻¹' (prechart e f i).source)
  have hp (z : O) : z.1.1 ∈ baseSet e f j ∩ baseSet e f i := ⟨z.2.1.1,z.2.2⟩
  have hb : Continuous (fun z : O ↦ z.1.1) := continuous_fst.comp continuous_subtype_val
  have hc := (continuous_transition e f j i).comp (hb.subtype_mk hp)
  have heval := hc.clm_apply (continuous_snd.comp continuous_subtype_val)
  apply (hb.prodMk heval).congr
  intro z
  change (z.1.1, coordinates e f i z.1.1 (hp z).2
    ((coordinates e f j z.1.1 (hp z).1).symm z.1.2)) =
    (z.1.1, if hi : z.1.1 ∈ baseSet e f i then coordinates e f i z.1.1 hi
      (if hj : z.1.1 ∈ baseSet e f j then (coordinates e f j z.1.1 hj).symm z.1.2 else 0) else 0)
  simp only [dite_eq_left (hp z).1, dite_eq_left (hp z).2]

@[instance_reducible]
def topology : TopologicalSpace (Sigma (fun p ↦ E p →L[ℝ] F p)) :=
  ParameterGraphVaryingCharts.topology (fun i ↦ FiniteFiberModel (rank e f i))
    (fun z : Sigma (fun p ↦ E p →L[ℝ] F p) ↦ z.1) (prechart e f)

def chart (i : A) : @Bundle.Trivialization A (FiniteFiberModel (rank e f i))
    (Sigma (fun p ↦ E p →L[ℝ] F p)) _ _ (topology e f) (fun z ↦ z.1) :=
  ParameterGraphVaryingCharts.trivialization _ _ (prechart e f) (compatible e f) i

lemma chart_apply (i p : A) (hp : p ∈ baseSet e f i) (L : E p →L[ℝ] F p) :
    chart e f i ⟨p,L⟩ = (p,coordinates e f i p hp L) := by
  change (p,if h : p ∈ baseSet e f i then coordinates e f i p h L else 0) = _
  simp only [dite_eq_left hp]

lemma fibre_inducing (p : A) :
    @Topology.IsInducing (E p →L[ℝ] F p) _ _ (topology e f) (fun L ↦ ⟨p,L⟩) := by
  let := topology e f
  have hp : p ∈ baseSet e f p := ⟨e.mem_baseSet p,f.mem_baseSet p⟩
  have hm (L : E p →L[ℝ] F p) : (⟨p,L⟩ : Sigma (fun p ↦ E p →L[ℝ] F p)) ∈
      (chart e f p).source := hp
  have hi : Topology.IsInducing (fun L : E p →L[ℝ] F p ↦
      chart e f p ⟨p,L⟩) := by
    have heq : (fun L : E p →L[ℝ] F p ↦ chart e f p ⟨p,L⟩) =
        fun L ↦ (p,coordinates e f p p hp L) := funext (chart_apply e f p p hp)
    rw [heq]
    exact Topology.isInducing_const_prod.mpr (coordinates e f p p hp).toHomeomorph.isInducing
  have hc : Continuous (fun L : E p →L[ℝ] F p ↦
      (⟨p,L⟩ : Sigma (fun p ↦ E p →L[ℝ] F p))) := by
    rw [(chart e f p).toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (Set.eq_univ_of_forall hm)]
    exact hi.continuous
  change Topology.IsInducing ((chart e f p) ∘ (fun L : E p →L[ℝ] F p ↦ ⟨p,L⟩)) at hi
  rw [← Set.domRestrict_comp_codRestrict hm] at hi
  apply Topology.IsInducing.of_codRestrict hm
  exact hi.of_comp (hc.codRestrict hm)
    (continuousOn_iff_continuous_domRestrict.mp (chart e f p).toOpenPartialHomeomorph.continuousOn)

lemma continuous_norm : @Continuous _ ℝ (topology e f) _
    (fun z : Sigma (fun p ↦ E p →L[ℝ] F p) ↦ ‖z.2‖) := by
  change @Continuous _ ℝ (⨆ i, TopologicalSpace.coinduced (prechart e f i).setSymm _) _ _
  rw [continuous_iSup_dom]
  intro i
  rw [continuous_coinduced_dom]
  let S := (prechart e f i).target
  let j : ∀ z : S, FiniteFiberModel (e.rank i) ≃L[ℝ] E z.1.1 :=
    fun z ↦ (e.coordinates i z.1.1 z.2.1.1).symm
  let L : ∀ z : S, E z.1.1 →L[ℝ] F z.1.1 :=
    fun z ↦ (coordinates e f i z.1.1 z.2.1).symm z.1.2
  have hb : Continuous (fun z : S × FiniteFiberModel (e.rank i) ↦ z.1.1.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hden : Continuous (fun z : S × FiniteFiberModel (e.rank i) ↦ ‖j z.1 z.2‖) :=
    e.continuous_norm.comp ((atlas_frame_continuous e i).comp
      ((hb.subtype_mk (fun z ↦ z.1.2.1.1)).prodMk continuous_snd))
  have hnum : Continuous (fun z : S × FiniteFiberModel (e.rank i) ↦ ‖L z.1 (j z.1 z.2)‖) := by
    have hOp : Continuous (fun z : S × FiniteFiberModel (e.rank i) ↦
        (modelEquiv e f i).symm z.1.1.2) :=
      (modelEquiv e f i).symm.continuous.comp
        (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))
    have hv := hOp.clm_apply continuous_snd
    have hc := f.continuous_norm.comp ((atlas_frame_continuous f i).comp
      ((hb.subtype_mk (fun z ↦ z.1.2.1.2)).prodMk hv))
    apply hc.congr
    intro z
    change ‖(f.coordinates i z.1.1.1 z.1.2.1.2).symm
      ((modelEquiv e f i).symm z.1.1.2 z.2)‖ = ‖L z.1 (j z.1 z.2)‖
    simp [L,j,coordinates,ContinuousLinearEquiv.arrowCongr_apply]
  have hn := continuous_norm_of_frame j L hden hnum
  apply hn.congr
  intro z
  change ‖(coordinates e f i z.1.1 z.2.1).symm z.1.2‖ =
    ‖(if h : z.1.1 ∈ baseSet e f i then (coordinates e f i z.1.1 h).symm z.1.2 else 0)‖
  simp only [dite_eq_left z.2.1]

/-- The bundle of original continuous linear maps has a finite-rank normed
atlas. Charts are original coordinate conjugations, glued with the coinduced
chart topology. The operator norm is continuous by the frame norm theorem;
the original fibre norm topology is preserved. -/
def atlas : @FiniteRankNormedAtlas A _ (fun p ↦ E p →L[ℝ] F p) _ _ (topology e f) := by
  let := topology e f
  exact {
  rank := rank e f
  chart := chart e f
  mem_baseSet i := ⟨e.mem_baseSet i,f.mem_baseSet i⟩
  rank_eq i p hp := by
    exact congrArg₂ (fun m n : ℕ ↦ Module.finrank ℝ (FiniteFiberModel m →L[ℝ] FiniteFiberModel n))
      (e.rank_eq i p hp.1) (f.rank_eq i p hp.2)
  coordinates := coordinates e f
  chart_apply := chart_apply e f
  fibre_inducing := fibre_inducing e f
  continuous_norm := continuous_norm e f
  continuous_transition := continuous_transition e f }


/-- Evaluation on continuous local source frames detects continuity of an
original operator family. Finite-dimensional operator continuity is tested on
fixed frame vectors, then the target Hom chart reconstructs the total map. -/
lemma continuous_of_evaluation {Z : Type*} [TopologicalSpace Z]
    (p : Z → A) (hp : Continuous p) (L : ∀ z, E (p z) →L[ℝ] F (p z))
    (hL : ∀ i (v : FiniteFiberModel (e.rank i)), Continuous
      (fun z : {z // p z ∈ (e.chart i).baseSet} ↦
        (⟨p z.1,L z.1 ((e.coordinates i (p z.1) z.2).symm v)⟩ : Sigma F))) :
    @Continuous _ _ _ (topology e f) (fun z ↦ (⟨p z,L z⟩ : Sigma (fun p ↦ E p →L[ℝ] F p))) := by
  let := topology e f
  have hloc (i : A) : Continuous (fun z : p ⁻¹' baseSet e f i ↦
      (⟨p z.1,L z.1⟩ : Sigma (fun p ↦ E p →L[ℝ] F p))) := by
    let O := p ⁻¹' baseSet e f i
    let M : O → HomModel e f i := fun z ↦
      (f.coordinates i (p z.1) z.2.2).toContinuousLinearMap.comp
        ((L z.1).comp (e.coordinates i (p z.1) z.2.1).symm.toContinuousLinearMap)
    have hM : Continuous M := by
      rw [continuous_clm_apply]
      intro v
      have he := (hL i v).comp
        (continuous_subtype_val.subtype_mk (fun z : O ↦ z.2.1))
      have hc := (f.chart i).toOpenPartialHomeomorph.continuousOn.comp_continuous he
        (fun z : O ↦ (f.chart i).mem_source.mpr z.2.2)
      apply hc.snd.congr
      intro z
      change ((f.chart i) ⟨p z.1,L z.1 ((e.coordinates i (p z.1) z.2.1).symm v)⟩).2 = M z v
      rw [f.chart_apply i (p z.1) z.2.2]
      rfl
    have hc := ((hp.comp continuous_subtype_val).prodMk
      ((modelEquiv e f i).continuous.comp hM))
    rw [(chart e f i).toOpenPartialHomeomorph.continuous_iff_continuous_comp_left
      (Set.eq_univ_of_forall (fun z : O ↦ z.2))]
    apply hc.congr
    intro z
    exact (chart_apply e f i (p z.1) z.2 (L z.1)).symm
  rw [continuous_iff_continuousAt]
  intro z
  have ho : IsOpen (p ⁻¹' baseSet e f (p z)) :=
    ((e.chart (p z)).open_baseSet.inter (f.chart (p z)).open_baseSet).preimage hp
  have hz : z ∈ p ⁻¹' baseSet e f (p z) :=
    ⟨e.mem_baseSet (p z),f.mem_baseSet (p z)⟩
  exact ((continuousOn_iff_continuous_domRestrict.mpr (hloc (p z))).continuousAt (ho.mem_nhds hz))

/-- Continuous original operator and vector families have continuous evaluation
in the original receiving total space. Local conjugation charts reduce this to
ordinary continuous linear map evaluation in fixed finite models. -/
lemma continuous_apply {Z : Type*} [TopologicalSpace Z]
    (p : Z → A) (hp : Continuous p) (L : ∀ z, E (p z) →L[ℝ] F (p z))
    (v : ∀ z, E (p z))
    (hL : @Continuous _ _ _ (topology e f)
      (fun z ↦ (⟨p z,L z⟩ : Sigma (fun p ↦ E p →L[ℝ] F p))))
    (hv : Continuous (fun z ↦ (⟨p z,v z⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨p z,L z (v z)⟩ : Sigma F)) := by
  let := topology e f
  have hloc (i : A) : Continuous (fun z : p ⁻¹' baseSet e f i ↦
      (⟨p z.1,L z.1 (v z.1)⟩ : Sigma F)) := by
    let O := p ⁻¹' baseSet e f i
    have hcL := (chart e f i).toOpenPartialHomeomorph.continuousOn.comp_continuous
      (hL.comp continuous_subtype_val) (fun z : O ↦ z.2)
    have hcv := (e.chart i).toOpenPartialHomeomorph.continuousOn.comp_continuous
      (hv.comp continuous_subtype_val) (fun z : O ↦ (e.chart i).mem_source.mpr z.2.1)
    have heval := ((modelEquiv e f i).symm.continuous.comp hcL.snd).clm_apply hcv.snd
    have hc := (atlas_frame_continuous f i).comp
      (((hp.comp continuous_subtype_val).subtype_mk (fun z : O ↦ z.2.2)).prodMk heval)
    apply hc.congr
    intro z
    change (⟨p z.1,(f.coordinates i (p z.1) z.2.2).symm
      ((modelEquiv e f i).symm ((chart e f i) ⟨p z.1,L z.1⟩).2
        ((e.chart i) ⟨p z.1,v z.1⟩).2)⟩ : Sigma F) = _
    rw [chart_apply e f i (p z.1) z.2, e.chart_apply i (p z.1) z.2.1]
    simp [coordinates,ContinuousLinearEquiv.arrowCongr_apply]
  rw [continuous_iff_continuousAt]
  intro z
  have ho : IsOpen (p ⁻¹' baseSet e f (p z)) :=
    ((e.chart (p z)).open_baseSet.inter (f.chart (p z)).open_baseSet).preimage hp
  have hz : z ∈ p ⁻¹' baseSet e f (p z) :=
    ⟨e.mem_baseSet (p z),f.mem_baseSet (p z)⟩
  exact (continuousOn_iff_continuous_domRestrict.mpr (hloc (p z))).continuousAt (ho.mem_nhds hz)


end ParameterGraphHomAtlas

end HolomorphicAnosov
