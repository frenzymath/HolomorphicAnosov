import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Analysis.FrameOperatorNormContinuity
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import Mathlib.Topology.Compactness.Compact

noncomputable section
open Set Filter _root_.Topology
namespace HolomorphicAnosov

/-- The coordinate map is uniformly bounded relative to the original fibre norms on an open
neighborhood of each base point (Hirsch–Pugh–Shub, p. 8). -/
theorem parameter_graph_local_coordinate_bound
    {A : Type*} [TopologicalSpace A] {E : A → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E)) (i : A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p in 𝓝 i, p ∈ (e.chart i).baseSet ∧
      ∀ v : E p, ‖((e.chart i) ⟨p,v⟩).2‖ ≤ C * ‖v‖ := by
  let U := (e.chart i).baseSet
  let j (p : U) := (e.coordinates i p.1 p.2).symm
  let L (p : U) := (e.coordinates i p.1 p.2).toContinuousLinearMap
  have hden : Continuous (fun z : U × FiniteFiberModel (e.rank i) ↦ ‖j z.1 z.2‖) :=
    e.continuous_norm.comp (atlas_frame_continuous e i)
  have hnum : Continuous (fun z : U × FiniteFiberModel (e.rank i) ↦ ‖L z.1 (j z.1 z.2)‖) := by
    simpa only [L, j, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using continuous_snd.norm
  have hnorm := continuous_norm_of_frame j L hden hnum
  let C := ‖L ⟨i,e.mem_baseSet i⟩‖ + 1
  have hC : 0 < C := lt_of_le_of_lt (norm_nonneg _) (lt_add_one _)
  let O : Set A := Subtype.val '' {p : U | ‖L p‖ < C}
  have hO : IsOpen O := (e.chart i).open_baseSet.isOpenMap_subtype_val _
    (isOpen_lt hnorm continuous_const)
  have hi : i ∈ O := by
    refine ⟨⟨i,e.mem_baseSet i⟩, ?_, rfl⟩
    change ‖L ⟨i,e.mem_baseSet i⟩‖ < ‖L ⟨i,e.mem_baseSet i⟩‖ + 1
    exact lt_add_one _
  refine ⟨C,hC,?_⟩
  filter_upwards [hO.mem_nhds hi] with p hp
  obtain ⟨q,hq,rfl⟩ := hp
  refine ⟨q.2,fun v ↦ ?_⟩
  rw [e.chart_apply i q.1 q.2]
  exact (L q).le_opNorm v |>.trans (mul_le_mul_of_nonneg_right hq.le (norm_nonneg v))

/-- HPS pp.8,35,62: a closed disc in the original finite-rank normed bundle
over a compact base is compact. Project an ultrafilter to a base limit, use
one local frame bound to confine its coordinates to a compact model ball,
and pull their joint limit back by the original inverse chart. The closed
norm inequality survives the limit. No separation of the base, constant rank,
or compact closure of a chart domain is assumed. -/
theorem parameter_graph_closed_disc_isCompact
    {A : Type*} [TopologicalSpace A] [CompactSpace A] {E : A → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E)) (R : ℝ) :
    IsCompact {z : Sigma E | ‖z.2‖ ≤ R} := by
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro f hf
  obtain ⟨p, _, hp⟩ := (isCompact_univ : IsCompact (univ : Set A)).ultrafilter_le_nhds'
    (f.map Sigma.fst) (by exact Filter.univ_mem)
  change Tendsto Sigma.fst (f : Filter (Sigma E)) (𝓝 p) at hp
  obtain ⟨C,hC,hbound⟩ := parameter_graph_local_coordinate_bound e p
  have hevent := hp.eventually hbound
  have hball : ∀ᶠ z : Sigma E in (f : Filter (Sigma E)),
      ((e.chart p) z).2 ∈ Metric.closedBall (0 : FiniteFiberModel (e.rank p)) (C*R) := by
    filter_upwards [hevent, hf] with z hz hzR
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hz.2 z.2).trans (mul_le_mul_of_nonneg_left hzR hC.le)
  obtain ⟨v,hv,hvlim⟩ := (isCompact_closedBall (0 : FiniteFiberModel (e.rank p)) (C*R)).ultrafilter_le_nhds'
    (f.map (fun z ↦ ((e.chart p) z).2)) hball
  change Tendsto (fun z ↦ ((e.chart p) z).2) (f : Filter (Sigma E)) (𝓝 v) at hvlim
  have hpair := hp.prodMk_nhds hvlim
  have hchart : Tendsto (e.chart p) (f : Filter (Sigma E)) (𝓝 (p,v)) := by
    apply hpair.congr'
    filter_upwards [hevent] with z hz
    rw [show z = ⟨z.1,z.2⟩ from rfl, e.chart_apply p z.1 hz.1 z.2]
  have hinvc : ContinuousAt (e.chart p).toOpenPartialHomeomorph.symm (p,v) :=
    (e.chart p).toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      ((e.chart p).toOpenPartialHomeomorph.open_target.mem_nhds
        ((e.chart p).mem_target.mpr (e.mem_baseSet p)))
  have hlimit : (f : Filter (Sigma E)) ≤ 𝓝 ((e.chart p).toOpenPartialHomeomorph.symm (p,v)) := by
    have hcomp := hinvc.tendsto.comp hchart
    have hid : Tendsto id (f : Filter (Sigma E))
        (𝓝 ((e.chart p).toOpenPartialHomeomorph.symm (p,v))) := by
      apply hcomp.congr'
      filter_upwards [hevent] with z hz
      exact (e.chart p).toOpenPartialHomeomorph.left_inv ((e.chart p).mem_source.mpr hz.1)
    exact hid
  refine ⟨_, ?_, hlimit⟩
  exact (isClosed_le e.continuous_norm continuous_const).mem_of_tendsto hlimit hf

/-- HPS pp.8,32–35,62: an open neighborhood of the entire zero section
contains one common positive original-norm disc. The part of the compact
unit disc outside the neighborhood is compact. If nonempty, its norm has a
positive minimum, because no zero vector lies there. Take the smaller of
this minimum and one; if the complement is empty use radius one. No
separation or regularity assumption on the base is used. -/
theorem parameter_graph_uniform_zero_tube
    {A : Type*} [TopologicalSpace A] [CompactSpace A] {E : A → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E)) (W : Set (Sigma E))
    (hW : IsOpen W) (hzero : ∀ p, (⟨p,0⟩ : Sigma E) ∈ W) :
    ∃ d : ℝ, 0 < d ∧ ∀ p (x : E p), ‖x‖ < d → (⟨p,x⟩ : Sigma E) ∈ W := by
  let K : Set (Sigma E) := {z | ‖z.2‖ ≤ (1 : ℝ)} ∩ Wᶜ
  have hK : IsCompact K := (parameter_graph_closed_disc_isCompact e 1).inter_right hW.isClosed_compl
  by_cases hne : K.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne e.continuous_norm.continuousOn
    have hpos : 0 < ‖z.2‖ := norm_pos_iff.mpr (by
      intro h
      exact hz.2 (by simpa only [← h] using hzero z.1))
    refine ⟨min 1 ‖z.2‖,lt_min zero_lt_one hpos,?_⟩
    intro p x hx
    by_contra hout
    have hxK : (⟨p,x⟩ : Sigma E) ∈ K := ⟨(hx.trans_le (min_le_left _ _)).le,hout⟩
    exact (not_lt_of_ge (hmin hxK)) (hx.trans_le (min_le_right _ _))
  · refine ⟨1,zero_lt_one,?_⟩
    intro p x hx
    by_contra hout
    exact hne ⟨⟨p,x⟩,hx.le,hout⟩

end HolomorphicAnosov
