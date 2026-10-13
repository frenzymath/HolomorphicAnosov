import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Prod

noncomputable section
open Set
open scoped Topology
namespace HolomorphicAnosov
namespace ParameterGraphProductAtlas
attribute [local instance] Classical.propDecidable
variable {A : Type*} [TopologicalSpace A] {E F : A → Type*}
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
  (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))

abbrev ProdModel (i : A) := FiniteFiberModel (e.rank i) × FiniteFiberModel (f.rank i)
def rank (i : A) : ℕ := Module.finrank ℝ (ProdModel e f i)
lemma rank_eq_add (i : A) : rank e f i = e.rank i + f.rank i := by
  simp [rank, ProdModel, Module.finrank_prod, FiniteFiberModel]

def baseSet (i : A) : Set A := (e.chart i).baseSet ∩ (f.chart i).baseSet

def modelEquiv (i : A) : ProdModel e f i ≃L[ℝ] FiniteFiberModel (rank e f i) :=
  ContinuousLinearEquiv.ofFinrankEq ((finrank_euclideanSpace_fin (𝕜 := ℝ)).symm)

def coordinates (i p : A) (hp : p ∈ baseSet e f i) :
    (E p × F p) ≃L[ℝ] FiniteFiberModel (rank e f i) :=
  ((e.coordinates i p hp.1).prodCongr (f.coordinates i p hp.2)).trans (modelEquiv e f i)

/-- The actual conjugation chart on the bundle of original fibre products. -/
def prechart (i : A) : Bundle.Pretrivialization (FiniteFiberModel (rank e f i))
    (fun z : Sigma (fun p ↦ E p × F p) ↦ z.1) where
  toFun z := (z.1,if hz : z.1 ∈ baseSet e f i then coordinates e f i z.1 hz z.2 else 0)
  invFun z := ⟨z.1,if hz : z.1 ∈ baseSet e f i then (coordinates e f i z.1 hz).symm z.2 else 0⟩
  source := (fun z : Sigma (fun p ↦ E p × F p) ↦ z.1) ⁻¹' baseSet e f i
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


def pairing (z : Sigma (fun p ↦ E p × F p)) : Sigma E × Sigma F :=
  (⟨z.1,z.2.1⟩,⟨z.1,z.2.2⟩)

@[instance_reducible]
def topology : TopologicalSpace (Sigma (fun p ↦ E p × F p)) :=
  TopologicalSpace.induced (pairing (E := E) (F := F)) inferInstance

omit [TopologicalSpace A] [∀ p, NormedSpace ℝ (E p)] [∀ p, NormedSpace ℝ (F p)]
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedAddCommGroup (F p)] in
lemma pairing_inducing : @Topology.IsInducing _ _ (topology (E := E) (F := F)) _ pairing :=
  Topology.IsInducing.induced _

omit [TopologicalSpace A] [∀ p, NormedSpace ℝ (E p)] [∀ p, NormedSpace ℝ (F p)]
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedAddCommGroup (F p)] in
lemma fst_continuous : @Continuous _ (Sigma E) (topology (E := E) (F := F)) _
    (fun z : Sigma (fun p ↦ E p × F p) ↦ (⟨z.1,z.2.1⟩ : Sigma E)) :=
  by
    let := topology (E := E) (F := F)
    exact (pairing_inducing (E := E) (F := F)).continuous.fst

omit [TopologicalSpace A] [∀ p, NormedSpace ℝ (E p)] [∀ p, NormedSpace ℝ (F p)]
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedAddCommGroup (F p)] in
lemma snd_continuous : @Continuous _ (Sigma F) (topology (E := E) (F := F)) _
    (fun z : Sigma (fun p ↦ E p × F p) ↦ (⟨z.1,z.2.2⟩ : Sigma F)) :=
  by
    let := topology (E := E) (F := F)
    exact (pairing_inducing (E := E) (F := F)).continuous.snd

def chart (i : A) : @Bundle.Trivialization A (FiniteFiberModel (rank e f i))
    (Sigma (fun p ↦ E p × F p)) _ _ topology (fun z ↦ z.1) := by
  let := topology (E := E) (F := F)
  exact { prechart e f i with
    open_source := by
      exact ((e.chart i).open_baseSet.inter (f.chart i).open_baseSet).preimage
        ((parameter_graph_atlas_projection_continuous e).comp (fst_continuous (E := E) (F := F)))
    continuousOn_toFun := by
      rw [continuousOn_iff_continuous_domRestrict]
      let S := (prechart e f i).source
      have he := (e.chart i).toOpenPartialHomeomorph.continuousOn.comp_continuous
        ((fst_continuous (E := E) (F := F)).comp continuous_subtype_val)
        (fun z : S ↦ (e.chart i).mem_source.mpr z.2.1)
      have hf := (f.chart i).toOpenPartialHomeomorph.continuousOn.comp_continuous
        ((snd_continuous (E := E) (F := F)).comp continuous_subtype_val)
        (fun z : S ↦ (f.chart i).mem_source.mpr z.2.2)
      have hp : Continuous (fun z : S ↦ z.1.1) := (parameter_graph_atlas_projection_continuous e).comp
        ((fst_continuous (E := E) (F := F)).comp continuous_subtype_val)
      have hc := hp.prodMk ((modelEquiv e f i).continuous.comp (he.snd.prodMk hf.snd))
      apply hc.congr
      intro z
      change (z.1.1,modelEquiv e f i
        (((e.chart i) ⟨z.1.1,z.1.2.1⟩).2,((f.chart i) ⟨z.1.1,z.1.2.2⟩).2)) =
        (z.1.1,if h : z.1.1 ∈ baseSet e f i then coordinates e f i z.1.1 h z.1.2 else 0)
      rw [e.chart_apply i z.1.1 z.2.1,f.chart_apply i z.1.1 z.2.2]
      rw [dite_eq_left (show z.1.1 ∈ baseSet e f i from z.2)]
      rfl
    continuousOn_invFun := by
      rw [continuousOn_iff_continuous_domRestrict]
      let S := (prechart e f i).target
      have hp : Continuous (fun z : S ↦ z.1.1) := continuous_fst.comp continuous_subtype_val
      have hv : Continuous (fun z : S ↦ (modelEquiv e f i).symm z.1.2) := (modelEquiv e f i).symm.continuous.comp
        (continuous_snd.comp continuous_subtype_val)
      have he := (atlas_frame_continuous e i).comp
        ((hp.subtype_mk (fun z : S ↦ z.2.1.1)).prodMk hv.fst)
      have hf := (atlas_frame_continuous f i).comp
        ((hp.subtype_mk (fun z : S ↦ z.2.1.2)).prodMk hv.snd)
      apply continuous_induced_rng.mpr
      apply (he.prodMk hf).congr
      intro z
      change (⟨z.1.1,(e.coordinates i z.1.1 z.2.1.1).symm
          ((modelEquiv e f i).symm z.1.2).1⟩,
        ⟨z.1.1,(f.coordinates i z.1.1 z.2.1.2).symm
          ((modelEquiv e f i).symm z.1.2).2⟩) =
        pairing ⟨z.1.1,if h : z.1.1 ∈ baseSet e f i then
          (coordinates e f i z.1.1 h).symm z.1.2 else 0⟩
      simp only [dite_eq_left z.2.1]
      rfl }

lemma continuous_transition (i j : A) :
    Continuous (fun p : {p // p ∈ ParameterGraphProductAtlas.baseSet e f i ∩ ParameterGraphProductAtlas.baseSet e f j} ↦
      (ParameterGraphProductAtlas.coordinates e f j p.1 p.2.2).toContinuousLinearMap.comp
        (ParameterGraphProductAtlas.coordinates e f i p.1 p.2.1).symm.toContinuousLinearMap) := by
  let O := {p // p ∈ baseSet e f i ∩ baseSet e f j}
  have he : Continuous (fun p : O ↦
      (e.coordinates j p.1 p.2.2.1).toContinuousLinearMap.comp
        (e.coordinates i p.1 p.2.1.1).symm.toContinuousLinearMap) :=
    (e.continuous_transition i j).comp
      (continuous_subtype_val.subtype_mk (fun p : O ↦ ⟨p.2.1.1,p.2.2.1⟩))
  have hf : Continuous (fun p : O ↦
      (f.coordinates j p.1 p.2.2.2).toContinuousLinearMap.comp
        (f.coordinates i p.1 p.2.1.2).symm.toContinuousLinearMap) :=
    (f.continuous_transition i j).comp
      (continuous_subtype_val.subtype_mk (fun p : O ↦ ⟨p.2.1.2,p.2.2.2⟩))
  rw [continuous_clm_apply]
  intro v
  have hc := (modelEquiv e f j).continuous.comp
    ((Continuous.prod_mapL ℝ he hf).clm_apply (continuous_const (y := (modelEquiv e f i).symm v)))
  exact hc.congr (fun _ ↦ rfl)

lemma chart_apply (i p : A) (hp : p ∈ baseSet e f i) (v : E p × F p) :
    chart e f i ⟨p,v⟩ = (p,coordinates e f i p hp v) := by
  change (p,if h : p ∈ baseSet e f i then coordinates e f i p h v else 0) = _
  simp only [dite_eq_left hp]

include e f in
lemma fibre_inducing (p : A) :
    @Topology.IsInducing (E p × F p) _ _ topology (fun v ↦ ⟨p,v⟩) := by
  let := topology (E := E) (F := F)
  apply (pairing_inducing (E := E) (F := F)).of_comp_iff.mp
  exact (e.fibre_inducing p).prodMap (f.fibre_inducing p)

include e f in
lemma continuous_norm : @Continuous _ ℝ (topology (E := E) (F := F)) _
    (fun z : Sigma (fun p ↦ E p × F p) ↦ ‖z.2‖) := by
  let := topology (E := E) (F := F)
  exact (e.continuous_norm.comp (fst_continuous (E := E) (F := F))).max
    (f.continuous_norm.comp (snd_continuous (E := E) (F := F)))

/-- Original product bundle atlas for the topology induced by the two component
total spaces. The norm is the original maximum product norm. Local coordinates
pair the two original charts and use a fixed Euclidean model equivalence. -/
def atlas : @FiniteRankNormedAtlas A _ (fun p ↦ E p × F p) _ _ topology := by
  let := topology (E := E) (F := F)
  exact {
    rank := rank e f
    chart := chart e f
    mem_baseSet i := ⟨e.mem_baseSet i,f.mem_baseSet i⟩
    rank_eq i p hp := by
      rw [rank_eq_add,rank_eq_add,e.rank_eq i p hp.1,f.rank_eq i p hp.2]
    coordinates := coordinates e f
    chart_apply := chart_apply e f
    fibre_inducing := fibre_inducing e f
    continuous_norm := continuous_norm e f
    continuous_transition := continuous_transition e f }

/-- The actual split bundle atlas, preserving the component atlases and their
pairing topology. This is the bundle product used by the tangent action. -/
def splitAtlas : @SplitFiniteRankNormedAtlas A _ E F _ _ _ _ _ _ topology := by
  let := topology (E := E) (F := F)
  exact ⟨e,f,atlas e f,pairing_inducing⟩

omit [TopologicalSpace A] [∀ p, NormedSpace ℝ (E p)] [∀ p, NormedSpace ℝ (F p)]
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedAddCommGroup (F p)] in
/-- Pairing continuous original component families is continuous in the product
bundle topology. -/
lemma continuous_mk {Z : Type*} [TopologicalSpace Z] (p : Z → A)
    (x : ∀ z, E (p z)) (y : ∀ z, F (p z))
    (hx : Continuous (fun z ↦ (⟨p z,x z⟩ : Sigma E)))
    (hy : Continuous (fun z ↦ (⟨p z,y z⟩ : Sigma F))) :
    @Continuous _ _ _ topology (fun z ↦ (⟨p z,(x z,y z)⟩ : Sigma (fun p ↦ E p × F p))) := by
  let := topology (E := E) (F := F)
  exact continuous_induced_rng.mpr (hx.prodMk hy)


end ParameterGraphProductAtlas
end HolomorphicAnosov
