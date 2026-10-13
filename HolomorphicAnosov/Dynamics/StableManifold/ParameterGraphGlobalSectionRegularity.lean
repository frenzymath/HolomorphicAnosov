import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphInvariantSectionRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSectionPropagation

noncomputable section
open Set
namespace HolomorphicAnosov
universe u v w

/-- The finite-order invariant-section theorem with a global contracting
return. The local tangent induction applies on any one compact source disc;
its common regular germ then propagates globally through the invariant
section equation. The action need only be smooth on an open neighborhood of
the entire bounded receiving-value strip, not at singular operators outside
that strip. HPS, Invariant Manifolds, pp.32–36,62. -/
theorem parameter_graph_global_section_regularity
    {A : Type w} [TopologicalSpace A] [CompactSpace A]
    {X : A→Type u} {Y : A→Type (max u v)}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)] [∀p,CompleteSpace (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := X)) (f : FiniteRankNormedAtlas (E := Y))
    (h : A→A) (hh : Continuous h) (R : ∀p,X p→X (h p))
    (F : ∀p,X p×Y (h p)→Y p) (P : ∀p,X p→Y p) (r:ℕ)
    (c q:NNReal) (hc:(c:ℝ)<1) (hq:(q:ℝ)<1)
    (hRL : ∀p,LipschitzWith c (R p)) (hzero : ∀p,R p 0=0)
    (hR : JointFiberContDiff e e h r R)
    (hPc : Continuous (fun z:Sigma X ↦ (⟨z.1,P z.1 z.2⟩ : Sigma Y)))
    (M M₀:ℝ) (hM:M<M₀) (hP:∀p x,‖P p x‖≤M)
    (hinv:∀p x,P p x=F p (x,P (h p) (R p x)))
    (hvertical:∀p x,LipschitzOnWith q (fun v ↦ F p (x,v)) (Metric.closedBall 0 M₀))
    (W : Set (Sigma (fun p ↦ X p×Y (h p))))
    (hW : letI := ParameterGraphPullbackAtlas.topology f h hh
      @IsOpen _ (ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))) W)
    (hF : letI := ParameterGraphPullbackAtlas.topology f h hh
      letI := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
      JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e
        (ParameterGraphPullbackAtlas.atlas f h hh)) f id r W F)
    (hstrip : ∀p (x:X p) (v:Y (h p)),‖v‖≤M₀ →
      (⟨p,(x,v)⟩ : Sigma (fun p ↦ X p×Y (h p)))∈W) :
    JointFiberContDiff e f id r P := by
  obtain ⟨δ,hδ,_,hlocal⟩ := parameter_graph_invariant_section_regularity e h hh R c hc hzero r
    f F P 1 M M₀ q zero_lt_one hM hq (fun p ↦ (hRL p).lipschitzOnWith)
    ((jointFiberContDiffOn_univ_iff.mpr hR).mono (subset_univ _)) hPc.continuousOn
    (fun p x _ ↦ hP p x) (fun p x _ ↦ hinv p x) (fun p x _ ↦ hvertical p x)
    W hW hF (fun p x v _ hv ↦ hstrip p x v hv)
  exact parameter_graph_section_local_to_global e f h hh R F P r hR c hc hRL hzero
    hinv W hW hF (fun p x ↦ hstrip p x _ ((hP _ _).trans hM.le)) δ hδ hlocal

end HolomorphicAnosov
