import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphClosedDiscCompactness
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphProductAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set
open scoped _root_.Topology ContDiff
namespace HolomorphicAnosov

/-- A closed rectangular disc in a product of original finite-rank fibres is
compact over a compact parameter base. It is the intersection of a compact
max-norm disc with two closed original-norm inequalities. -/
theorem parameter_graph_closed_rectangle_isCompact
    {A : Type*} [TopologicalSpace A] [CompactSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (d M : ℝ) :
    letI := ParameterGraphProductAtlas.topology (E := E) (F := F)
    IsCompact {z : Sigma (fun p ↦ E p × F p) | ‖z.2.1‖≤d ∧ ‖z.2.2‖≤M} := by
  let := ParameterGraphProductAtlas.topology (E := E) (F := F)
  have hclosed : IsClosed {z : Sigma (fun p ↦ E p × F p) | ‖z.2.1‖≤d ∧ ‖z.2.2‖≤M} :=
    (isClosed_le (e.continuous_norm.comp ParameterGraphProductAtlas.fst_continuous)
      continuous_const).inter
      (isClosed_le (f.continuous_norm.comp ParameterGraphProductAtlas.snd_continuous)
        continuous_const)
  apply (parameter_graph_closed_disc_isCompact (ParameterGraphProductAtlas.atlas e f)
    (max d M)).of_isClosed_subset hclosed
  intro z hz
  exact max_le ((hz.1).trans (le_max_left _ _)) ((hz.2).trans (le_max_right _ _))

/-- A jointly fibre C¹ map on a neighborhood of a closed rectangular fibre disc over a compact base
has a uniform derivative bound and a uniform Lipschitz bound on that disc. -/
theorem parameter_graph_compact_rectangular_forcing
    {A B : Type*} [TopologicalSpace A] [CompactSpace A] [TopologicalSpace B]
    {E F : A → Type*} {Y : B → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (y : FiniteRankNormedAtlas (E := Y)) (b : A→B) (hb : Continuous b)
    (G : ∀p,E p×F p→Y (b p)) (r : ℕ) (hr : 1≤r)
    (W : Set (Sigma (fun p ↦ E p×F p))) (d M : ℝ)
    (hW : @IsOpen _ (ParameterGraphProductAtlas.topology (E := E) (F := F)) W)
    (hG : letI := ParameterGraphProductAtlas.topology (E := E) (F := F)
      JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e f) y b r W G)
    (hrect : ∀p (x:E p) (v:F p), ‖x‖≤d → ‖v‖≤M → (⟨p,(x,v)⟩ : Sigma (fun p ↦ E p×F p))∈W) :
    ∃ L : NNReal,
      (∀p (z:E p×F p), ‖z.1‖≤d → ‖z.2‖≤M → ‖fderiv ℝ (G p) z‖≤L) ∧
      (∀p,LipschitzOnWith L (G p) (Metric.closedBall 0 d ×ˢ Metric.closedBall 0 M)) := by
  let := ParameterGraphProductAtlas.topology (E := E) (F := F)
  let K : Set (Sigma (fun p ↦ E p×F p)) := {z | ‖z.2.1‖≤d ∧ ‖z.2.2‖≤M}
  have hK : IsCompact K := parameter_graph_closed_rectangle_isCompact e f d M
  have hKU : K⊆W := fun z hz ↦ hrect z.1 z.2.1 z.2.2 hz.1 hz.2
  have hc := (parameter_graph_local_jet_norm_continuousOn
    (ParameterGraphProductAtlas.atlas e f) y b hb G r 1 hr W hW hG).mono hKU
  obtain ⟨C,hC⟩ := hK.bddAbove_image hc
  let L : NNReal := ⟨max C 0,le_max_right _ _⟩
  have hbound (p:A) (z:E p×F p) (hx:‖z.1‖≤d) (hv:‖z.2‖≤M) :
      ‖fderiv ℝ (G p) z‖≤L := by
    rw [← norm_iteratedFDeriv_one]
    exact (hC ⟨⟨p,z⟩,⟨hx,hv⟩,rfl⟩).trans (le_max_left _ _)
  refine ⟨L,hbound,fun p ↦ ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    ((convex_closedBall (0:E p) d).prod (convex_closedBall (0:F p) M))
  · have hzW := hrect p z.1 z.2
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2)
    exact (hG.1 ⟨p,z⟩ hzW).differentiableAt (by exact_mod_cast Nat.ne_zero_of_lt hr)
  · exact hbound p z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.2)

/-- Separate the receiving-value contraction from the known spatial forcing
on a rectangular fibre disc. -/
theorem parameter_graph_rectangular_comparison
    {X V Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X×V→Y) (L q : NNReal) (d M : ℝ)
    (hF : LipschitzOnWith L F (Metric.closedBall 0 d ×ˢ Metric.closedBall 0 M))
    (hq : ∀x, ‖x‖≤d → LipschitzOnWith q (fun v ↦ F (x,v)) (Metric.closedBall 0 M))
    (x x' : X) (v v' : V) (hx : ‖x‖≤d) (hx' : ‖x'‖≤d)
    (hv : ‖v‖≤M) (hv' : ‖v'‖≤M) :
    ‖F (x,v)-F (x',v')‖ ≤ (q:ℝ)*‖v-v'‖+(L:ℝ)*‖x-x'‖ := by
  have hvb : v∈Metric.closedBall (0:V) M := by simpa using hv
  have hvb' : v'∈Metric.closedBall (0:V) M := by simpa using hv'
  have hxb : x∈Metric.closedBall (0:X) d := by simpa using hx
  have hxb' : x'∈Metric.closedBall (0:X) d := by simpa using hx'
  have h1 := (hq x hx).dist_le_mul v hvb v' hvb'
  have h2 := hF.dist_le_mul (x,v') ⟨hxb,hvb'⟩ (x',v') ⟨hxb',hvb'⟩
  have h2' : ‖F (x,v')-F (x',v')‖≤(L:ℝ)*‖x-x'‖ := by
    simpa only [dist_eq_norm,Prod.mk_sub_mk,sub_self,Prod.norm_mk,norm_zero,
      max_eq_left (norm_nonneg _)] using h2
  have ht : ‖F (x,v)-F (x',v')‖ ≤ ‖F (x,v)-F (x,v')‖+‖F (x,v')-F (x',v')‖ := by
    simpa only [dist_eq_norm] using dist_triangle (F (x,v)) (F (x,v')) (F (x',v'))
  exact ht.trans
    (add_le_add (by simpa only [dist_eq_norm] using h1) h2')

/-- The vertical derivative has the same bound as the vertical contraction
at any interior point of the receiving-value ball, with arbitrary radius. -/
theorem parameter_graph_vertical_derivative_bound_on_ball
    {X V Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X×V→Y) (x:X) (v:V) (M:ℝ) (q:NNReal)
    (hF : DifferentiableAt ℝ F (x,v)) (hv : ‖v‖<M)
    (hq : LipschitzOnWith q (fun w ↦ F (x,w)) (Metric.closedBall 0 M)) :
    ‖(fderiv ℝ F (x,v)).comp (ContinuousLinearMap.inr ℝ X V)‖≤q := by
  have hd := hF.hasFDerivAt.comp v (hasFDerivAt_prodMk_right x v)
  exact hd.le_of_lipschitzOn
    (Metric.closedBall_mem_nhds_of_mem (by simpa [Metric.mem_ball,dist_zero_right] using hv)) hq

end HolomorphicAnosov
