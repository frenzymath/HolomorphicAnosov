import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageSlopeRegularityData
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageSlopeRegularityData
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageC1
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageC1
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedGraphContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFibreComplete

noncomputable section
open Set Topology
namespace HolomorphicAnosov

/-- HPS pp.33–35,54–58,62: continuous fixed unit graphs are jointly fibre C¹
under the explicit small-perturbation gap. Build the actual horizontal graph
homeomorphisms in the original fibres and prove their total inverses continuous.
Apply the two invariant continuous-slope constructions and Taylor identification.
The gap is essential: identity dynamics admits the nonsmooth graph |x|. -/
theorem parameter_graph_fixed_graph_c1
    {A : Type*} [TopologicalSpace A] {X Y : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma (fun p ↦ X p × Y p))]
    (e : SplitFiniteRankNormedAtlas (E₁ := X) (E₂ := Y))
    (r : ℕ) (hr : 1 ≤ r) (h : A ≃ₜ A)
    (T : ∀p,X p ≃L[ℝ] X (h p)) (S : ∀p,Y p →L[ℝ] Y (h p))
    (G : ∀p,X p × Y p → X (h p) × Y (h p))
    (hGj : JointFiberContDiff e.total e.total h r G) (hzero : ∀p,G p 0=0)
    (a k ε : NNReal) (ha : ∀p,‖(T p).symm.toContinuousLinearMap‖≤a)
    (hk : ∀p,‖S p‖≤k) (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (hslope : (a:ℝ)*(k+2*ε)≤1)
    (hinverse : ((k:ℝ)+2*ε)*((a:ℝ)/(1-(a:ℝ)*ε))<1)
    (hR : ∀p,LipschitzWith ε (fun z ↦ G p z-(T p z.1,S p z.2)))
    (s : ∀p,X p→Y p) (t : ∀p,Y p→X p)
    (hs : ∀p,s p 0=0 ∧ LipschitzWith 1 (s p))
    (ht : ∀p,t p 0=0 ∧ LipschitzWith 1 (t p))
    (hsc : Continuous (fun z : Sigma X ↦ (⟨z.1,s z.1 z.2⟩ : Sigma Y)))
    (htc : Continuous (fun z : Sigma Y ↦ (⟨z.1,t z.1 z.2⟩ : Sigma X)))
    (hsgraph : ∀p,G p '' Set.range (fun x ↦ (x,s p x)) =
      Set.range (fun x ↦ (x,s (h p) x)))
    (htgraph : ∀p,G p ⁻¹' Set.range (fun y ↦ (t (h p) y,y)) =
      Set.range (fun y ↦ (t p y,y))) :
    JointFiberContDiff e.first e.second id 1 s ∧
      JointFiberContDiff e.second e.first id 1 t := by
  classical
  let : ∀p,CompleteSpace (X p) := fun p ↦ parameter_graph_fibre_complete e.first p
  let : ∀p,CompleteSpace (Y p) := fun p ↦ parameter_graph_fibre_complete e.second p
  have hsmall' : (a:ℝ)*ε<1 := by nlinarith [a.2,ε.2]
  have hden : 0<1-(a:ℝ)*ε := sub_pos.mpr hsmall'
  let c : NNReal := ⟨(a:ℝ)/(1-(a:ℝ)*ε),div_nonneg a.2 hden.le⟩
  have hH (p : A) := parameter_graph_image_step (T p) (S p) (G p) (hzero p)
    a k ε (ha p) (hk p) hsmall' hslope (hR p) (s p) (hs p).1 (hs p).2
  choose H s' hHfirst hHzero hHinv hs'zero hs'lip hHgraph using hH
  have hfirst : ∀p x,(G p (x,s p x)).1=H p x := fun p x ↦ (hHfirst p x).symm
  have hsecond : ∀p x,(G p (x,s p x)).2=s (h p) (H p x) := by
    intro p x
    have hm : G p (x,s p x) ∈ Set.range (fun x ↦ (x,s (h p) x)) := by
      rw [← hsgraph p]
      exact ⟨(x,s p x),⟨x,rfl⟩,rfl⟩
    obtain ⟨u,hu⟩ := hm
    have hx := congrArg Prod.fst hu
    have hy := congrArg Prod.snd hu
    simpa only [Prod.fst,Prod.snd,hfirst] using hy.symm.trans (congrArg (s (h p)) hx)
  have hHtotal : Continuous (fun z : Sigma X ↦ (⟨h z.1,H z.1 z.2⟩ : Sigma X)) := by
    have hc := (parameter_graph_atlas_split_projections_continuous e).1.comp
      ((parameter_graph_joint_value_continuous e.total e.total h h.continuous G r hGj).comp
        (parameter_graph_atlas_pair_continuous e Sigma.fst Sigma.snd (fun z ↦ s z.1 z.2)
          continuous_id hsc))
    simpa only [Function.comp_def,hfirst] using hc
  have hHtotalinv := parameter_graph_fibre_homeomorph_inverse_continuous e.first e.first h H
    hHtotal (c:ℝ) hHinv
  have hHLip : ∀p,LipschitzWith c ((H p).symm : X (h p) → X p) :=
    fun p ↦ lipschitzWith_iff_norm_sub_le.mpr (hHinv p)
  constructor
  · exact parameter_graph_image_c1 X Y e r hr h T S G hGj
      a k ε c ha hk hsmall hjet hinverse hR s (fun p ↦ (hs p).2) hsc H
      hfirst hsecond hHLip hHtotalinv
  · apply parameter_graph_preimage_c1 X Y e r hr h h.continuous T S G hGj
      a k ε ha hk hsmall hjet hR t (fun p ↦ (ht p).2) htc
    intro p y
    have hm : (t p y,y) ∈ G p ⁻¹' Set.range (fun y ↦ (t (h p) y,y)) := by
      rw [htgraph]
      exact ⟨y,rfl⟩
    obtain ⟨v,hv⟩ := hm
    simp only [← hv]

end HolomorphicAnosov
