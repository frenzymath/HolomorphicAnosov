import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphParameterInverseContinuity

noncomputable section
open Set Topology Filter
namespace HolomorphicAnosov

section Atlas
variable {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z]
  {E : A → Type*} [∀ p, NormedAddCommGroup (E p)]
  [∀ p, NormedSpace ℝ (E p)] [TopologicalSpace (Sigma E)]

/-- HPS p.8: the projection of the original bundle is continuous, as follows
locally from the first coordinate of a trivialization. -/
theorem parameter_graph_atlas_projection_continuous (e : FiniteRankNormedAtlas (E := E)) :
    Continuous (fun z : Sigma E ↦ z.1) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let c := e.chart z.1
  have hz : z ∈ c.source := c.mem_source.mpr (e.mem_baseSet z.1)
  have hc := (c.toOpenPartialHomeomorph.continuousAt hz).fst
  apply hc.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with w hw
  exact (c.proj_toFun w hw).symm

/-- Local linear bundle charts identify fibrewise addition with addition in the
fixed model. Compose the two continuous sections with a chart near each tested
point, add their second coordinates, then use the inverse chart criterion.
This is the vector bundle operation in HPS p.8, on its original total topology. -/
theorem parameter_graph_atlas_add_continuous (e : FiniteRankNormedAtlas (E := E))
    (b : Z → A) (hb : Continuous b) (u v : ∀ z, E (b z))
    (hu : Continuous (fun z ↦ (⟨b z, u z⟩ : Sigma E)))
    (hv : Continuous (fun z ↦ (⟨b z, v z⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨b z, u z + v z⟩ : Sigma E)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let i := b z₀
  have hi := e.mem_baseSet i
  have huc := ((e.chart i).toOpenPartialHomeomorph.continuousAt
    ((e.chart i).mem_source.mpr hi)).comp hu.continuousAt
  have hvc := ((e.chart i).toOpenPartialHomeomorph.continuousAt
    ((e.chart i).mem_source.mpr hi)).comp hv.continuousAt
  apply (e.chart i).continuousAt_of_comp_left
    (show ContinuousAt (fun z ↦ (⟨b z, u z + v z⟩ : Sigma E).1) z₀ from hb.continuousAt) hi
  apply (hb.continuousAt.prodMk (huc.snd.add hvc.snd)).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds ((e.chart i).open_baseSet.mem_nhds hi)]
    with z hz
  change (e.chart i) ⟨b z, u z + v z⟩ =
    (b z, ((e.chart i) ⟨b z, u z⟩).2 + ((e.chart i) ⟨b z, v z⟩).2)
  simp only [e.chart_apply i (b z) hz, map_add]

/-- Fibrewise subtraction is continuous by the same linear-chart argument as
addition. HPS p.8, continuous linear bundle structure. -/
theorem parameter_graph_atlas_sub_continuous (e : FiniteRankNormedAtlas (E := E))
    (b : Z → A) (hb : Continuous b) (u v : ∀ z, E (b z))
    (hu : Continuous (fun z ↦ (⟨b z, u z⟩ : Sigma E)))
    (hv : Continuous (fun z ↦ (⟨b z, v z⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨b z, u z - v z⟩ : Sigma E)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let i := b z₀
  have hi := e.mem_baseSet i
  have huc := ((e.chart i).toOpenPartialHomeomorph.continuousAt
    ((e.chart i).mem_source.mpr hi)).comp hu.continuousAt
  have hvc := ((e.chart i).toOpenPartialHomeomorph.continuousAt
    ((e.chart i).mem_source.mpr hi)).comp hv.continuousAt
  apply (e.chart i).continuousAt_of_comp_left
    (show ContinuousAt (fun z ↦ (⟨b z, u z - v z⟩ : Sigma E).1) z₀ from hb.continuousAt) hi
  apply (hb.continuousAt.prodMk (huc.snd.sub hvc.snd)).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds ((e.chart i).open_baseSet.mem_nhds hi)]
    with z hz
  change (e.chart i) ⟨b z, u z - v z⟩ =
    (b z, ((e.chart i) ⟨b z, u z⟩).2 - ((e.chart i) ⟨b z, v z⟩).2)
  simp only [e.chart_apply i (b z) hz, map_sub]

/-- The zero section over an arbitrary continuous base map is continuous:
its chart expression is the pair of the base map and the constant zero vector.
HPS p.8; neither base compactness nor positive rank is required. -/
theorem parameter_graph_atlas_zero_continuous (e : FiniteRankNormedAtlas (E := E))
    (b : Z → A) (hb : Continuous b) :
    Continuous (fun z ↦ (⟨b z, 0⟩ : Sigma E)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let i := b z₀
  have hi := e.mem_baseSet i
  apply (e.chart i).continuousAt_of_comp_left
    (show ContinuousAt (fun z ↦ (⟨b z, 0⟩ : Sigma E).1) z₀ from hb.continuousAt) hi
  apply (hb.continuousAt.prodMk
    (continuousAt_const (y := (0 : FiniteFiberModel (e.rank i))))).congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds ((e.chart i).open_baseSet.mem_nhds hi)]
    with z hz
  change (e.chart i) ⟨b z, 0⟩ = (b z, 0)
  simp only [e.chart_apply i (b z) hz, map_zero]
end Atlas

/-- HPS pp.8 and 62: a uniformly bounded inverse family sends a continuous
receiving vector to a continuous original source vector. On each source chart,
evaluate the forward operators on a constant frame vector, subtract the given
receiving section, and take its continuous original norm. The inverse operator
bound gives the inverse solution estimate; parameter inverse continuity applies.
No trivialization of the full Hom bundle is required. -/
theorem parameter_graph_atlas_inverse_apply_continuous
    {Z A B : Type*} [TopologicalSpace Z] [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : Z → A) (c : Z → B) (hb : Continuous b) (hc : Continuous c)
    (J : ∀ z, E (b z) ≃L[ℝ] F (c z)) (K : ℝ)
    (hK : ∀ z, ‖(J z).symm.toContinuousLinearMap‖ ≤ K)
    (v : ∀ z, F (c z)) (hv : Continuous (fun z ↦ (⟨c z, v z⟩ : Sigma F)))
    (hJ : ∀ i (w : FiniteFiberModel (e.rank i)),
      Continuous (fun z : {z : Z // b z ∈ (e.chart i).baseSet} ↦
        (⟨c z.val, J z.val ((e.coordinates i (b z.val) z.property).symm w)⟩ : Sigma F))) :
    Continuous (fun z ↦ (⟨b z, (J z).symm (v z)⟩ : Sigma E)) := by
  apply parameter_graph_inverse_solution_continuous e b c hb
    (fun z ↦ J z) v (fun z ↦ (J z).symm (v z)) K
  · intro z x y
    calc
      ‖x - y‖ = ‖(J z).symm (J z x - J z y)‖ := by simp only [map_sub,
        ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ ‖(J z).symm.toContinuousLinearMap‖ * ‖J z x - J z y‖ :=
        (J z).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ K * ‖J z x - J z y‖ := mul_le_mul_of_nonneg_right (hK z) (norm_nonneg _)
  · intro z
    exact (J z).apply_symm_apply (v z)
  · intro i w
    exact f.continuous_norm.comp (parameter_graph_atlas_sub_continuous f
      (fun z : {z : Z // b z ∈ (e.chart i).baseSet} ↦ c z.val)
      (hc.comp continuous_subtype_val)
      (fun z ↦ J z.val ((e.coordinates i (b z.val) z.property).symm w))
      (fun z ↦ v z.val) (hJ i w) (hv.comp continuous_subtype_val))

section Split
variable {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z]
  {E₁ E₂ : A → Type*}
  [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
  [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
  [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
  [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]

/-- The split total topology is induced by the pair of component total spaces;
therefore both component projections are continuous. HPS pp.8 and 62. -/
theorem parameter_graph_atlas_split_projections_continuous
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) :
    Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨z.1, z.2.1⟩ : Sigma E₁)) ∧
    Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨z.1, z.2.2⟩ : Sigma E₂)) :=
  ⟨e.split_inducing.continuous.fst, e.split_inducing.continuous.snd⟩

/-- Pairing continuous component sections with the same base is continuous
in the original split total space, by its inducing law. HPS pp.8 and 62. -/
theorem parameter_graph_atlas_pair_continuous
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂))
    (b : Z → A) (u : ∀ z, E₁ (b z)) (v : ∀ z, E₂ (b z))
    (hu : Continuous (fun z ↦ (⟨b z, u z⟩ : Sigma E₁)))
    (hv : Continuous (fun z ↦ (⟨b z, v z⟩ : Sigma E₂))) :
    Continuous (fun z ↦ (⟨b z, (u z, v z)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) := by
  apply e.split_inducing.continuous_iff.mpr
  exact hu.prodMk hv

/-- Inserting a component with zero in the other component is continuous.
Pair the identity with the zero section over the continuous bundle projection.
HPS pp.8 and 62; no compactness of the base is needed. -/
theorem parameter_graph_atlas_split_inclusions_continuous
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) :
    Continuous (fun z : Sigma E₁ ↦
      (⟨z.1, (z.2, 0)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) ∧
    Continuous (fun z : Sigma E₂ ↦
      (⟨z.1, (0, z.2)⟩ : Sigma (fun p ↦ E₁ p × E₂ p))) := by
  constructor
  · apply parameter_graph_atlas_pair_continuous e (fun z : Sigma E₁ ↦ z.1)
      (fun z ↦ z.2) (fun _ ↦ 0)
    · exact continuous_id
    · exact parameter_graph_atlas_zero_continuous e.second _
        (parameter_graph_atlas_projection_continuous e.first)
  · apply parameter_graph_atlas_pair_continuous e (fun z : Sigma E₂ ↦ z.1)
      (fun _ ↦ 0) (fun z ↦ z.2)
    · exact parameter_graph_atlas_zero_continuous e.first _
        (parameter_graph_atlas_projection_continuous e.second)
    · exact continuous_id
end Split

end HolomorphicAnosov
