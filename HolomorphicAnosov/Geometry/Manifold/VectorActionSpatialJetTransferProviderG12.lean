import HolomorphicAnosov.Geometry.Manifold.VectorActionCoordinateSupport
import HolomorphicAnosov.Analysis.Regularity.MontgomeryFiniteDimensionalDerivativeDenseJointContinuity
import Mathlib.Analysis.Calculus.ContDiff.Comp

namespace HolomorphicAnosov.VectorActionSpatialSupport

open Filter
open scoped Topology _root_.Topology ContDiff

/-- Joint continuity of higher spatial jets of the original coordinate action (Montgomery, Lemma 4 and Corollary 1, pp.386–387). -/
theorem action_coordinate_spatial_jet_transfer_provider
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) ∞ M]
    [AddAction V M] [ContinuousVAdd V M]
    (hsmooth : ∀ v : V, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun x : M ↦ v +ᵥ x))
    (e f : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
    (k : ℕ) (s : Set (V × E)) (hs : IsOpen s)
    (hdom : ∀ p ∈ s, p.2 ∈ e.target ∧ (p.1 +ᵥ e.symm p.2) ∈ f.source) :
    ContinuousOn
      (fun p : V × E ↦ iteratedFDeriv ℝ (Nat.succ (Nat.succ k))
        (fun y : E ↦ f (p.1 +ᵥ e.symm y)) p.2) s := by
  suffices hall : ∀ (k : ℕ) (e f : OpenPartialHomeomorph M E),
      e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M →
      f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M →
      ∀ (s : Set (V × E)), IsOpen s →
      (∀ p ∈ s, p.2 ∈ e.target ∧ p.1 +ᵥ e.symm p.2 ∈ f.source) →
      ContinuousOn (fun p : V × E ↦ iteratedFDeriv ℝ k
        (fun y : E ↦ f (p.1 +ᵥ e.symm y)) p.2) s by
    exact hall k.succ.succ e f he hf s hs hdom
  intro k e f he hf s hs hdom
  induction k using Nat.strong_induction_on generalizing e f s with
  | h k ih =>
      cases k with
      | zero =>
        intro p hp
        have hact : ContinuousAt (fun q : V × E ↦ q.1 +ᵥ e.symm q.2) p :=
          continuousAt_fst.vadd ((e.symm.continuousAt (hdom p hp).1).comp continuousAt_snd)
        have hcoord : ContinuousAt (fun q : V × E ↦ f (q.1 +ᵥ e.symm q.2)) p :=
          (f.continuousAt (hdom p hp).2).comp_of_eq hact rfl
        exact ((continuousMultilinearCurryFin0 ℝ E E).symm.continuous.continuousAt.comp
          hcoord).continuousWithinAt
      | succ k =>
        have hlower (i : ℕ) (hi : i < k + 1) : ContinuousOn
            (fun p : V × E ↦ iteratedFDeriv ℝ i
              (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) s :=
          ih i hi e f he hf s hs hdom
        
        
        have hrecoverJets (v : V) (y : E) (hy : y ∈ e.target)
            (hvy : v +ᵥ e.symm y ∈ f.source)
            (hgood : ∀ i ≤ k + 1, ContinuousAt
              (fun p : V × E ↦ iteratedFDeriv ℝ i
                (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) (v, y)) :
            ContinuousAt (fun p : V × E ↦ iteratedFDeriv ℝ (k + 1)
              (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2) (0, y) := by
          let G : E → E := fun z ↦ e ((-v) +ᵥ f.symm z)
          let F : V × E → E := fun p ↦ f ((v + p.1) +ᵥ e.symm p.2)
          have hact : ContinuousAt (fun p : V × E ↦ (v + p.1) +ᵥ e.symm p.2)
              (0, y) := (continuousAt_const.add continuousAt_fst).vadd
            ((e.symm.continuousAt hy).comp continuousAt_snd)
          have hF : ContinuousAt F (0, y) :=
            (f.continuousAt (by simpa using hvy)).comp hact
          have hG : ContDiffAt ℝ ∞ G (F (0, y)) := by
            apply VectorActionSpatialSupport.action_coordinate_contDiffAt hsmooth f e hf he
              (-v) _ (f.map_source (by simpa [F] using hvy))
            simpa [F, f.left_inv hvy] using e.map_target hy
          have hJ : ContinuousAt
              (fun p : V × E ↦ (ftaylorSeries ℝ G (F p)).taylorComp
                (ftaylorSeries ℝ (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)) p.2)
                (k + 1)) (0, y) := by
            unfold FormalMultilinearSeries.taylorComp
            apply tendsto_finsetSum
            intro c _
            have ho : ContinuousAt (fun p : V × E ↦
                ftaylorSeries ℝ G (F p) c.length) (0, y) :=
              (hG.continuousAt_iteratedFDeriv (by simp)).comp hF
            have hi : ContinuousAt (fun p : V × E ↦ fun j : Fin c.length ↦
                ftaylorSeries ℝ (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)) p.2
                  (c.partSize j)) (0, y) := by
              apply continuousAt_pi.mpr
              intro j
              exact (hgood (c.partSize j) (c.partSize_le j)).comp_of_eq
                ((continuousAt_const.add continuousAt_fst).prodMk continuousAt_snd)
                (by simp)
            exact (c.compAlongOrderedFinpartitionL ℝ E E E).continuousAt_uncurry_of_multilinear.comp
              (ho.prodMk hi)
          apply hJ.congr_of_eventuallyEq
          have ht : ∀ᶠ p : V × E in 𝓝 (0, y), p.2 ∈ e.target :=
            continuousAt_snd.preimage_mem_nhds (e.open_target.mem_nhds hy)
          have hf' : ∀ᶠ p : V × E in 𝓝 (0, y),
              (v + p.1) +ᵥ e.symm p.2 ∈ f.source :=
            hact.preimage_mem_nhds (f.open_source.mem_nhds (by simpa using hvy))
          have he' : ∀ᶠ p : V × E in 𝓝 (0, y), p.1 +ᵥ e.symm p.2 ∈ e.source :=
            (continuousAt_fst.vadd ((e.symm.continuousAt hy).comp continuousAt_snd)).preimage_mem_nhds
              (e.open_source.mem_nhds (by simpa using e.map_target hy))
          filter_upwards [ht, hf', he'] with p hp hpF hpE
          have hinner := VectorActionSpatialSupport.action_coordinate_contDiffAt
            hsmooth e f he hf (v + p.1) p.2 hp hpF
          have houter : ContDiffAt ℝ ∞ G (F p) := by
            apply VectorActionSpatialSupport.action_coordinate_contDiffAt hsmooth f e hf he
              (-v) (F p) (f.map_source hpF)
            change (-v) +ᵥ f.symm (f ((v + p.1) +ᵥ e.symm p.2)) ∈ e.source
            rw [f.left_inv hpF, add_vadd, neg_vadd_vadd]
            exact hpE
          have hid : (G ∘ (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)))
              =ᶠ[𝓝 p.2] (fun z : E ↦ e (p.1 +ᵥ e.symm z)) := by
            have hn := (continuousAt_const.vadd (e.symm.continuousAt hp)).preimage_mem_nhds
              (f.open_source.mem_nhds hpF)
            filter_upwards [hn] with z hz
            change e ((-v) +ᵥ f.symm (f ((v + p.1) +ᵥ e.symm z))) = _
            change (v + p.1) +ᵥ e.symm z ∈ f.source at hz
            rw [f.left_inv hz, add_vadd, neg_vadd_vadd]
          exact ((iteratedFDeriv_comp (f := fun z : E ↦ f ((v + p.1) +ᵥ e.symm z))
            (x := p.2) houter hinner (by simp)).symm.trans
            ((hid.iteratedFDeriv ℝ (k + 1)).self_of_nhds)).symm
        have htopGoodToIdentity (v : V) (y : E) (hvy : (v, y) ∈ s)
            (hgood : ContinuousAt (fun p : V × E ↦ iteratedFDeriv ℝ (k + 1)
              (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) (v, y)) :
            ContinuousAt (fun p : V × E ↦ iteratedFDeriv ℝ (k + 1)
              (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2) (0, y) := by
          apply hrecoverJets v y (hdom (v, y) hvy).1 (hdom (v, y) hvy).2
          intro i hi
          rcases lt_or_eq_of_le hi with hi | rfl
          · exact (hlower i hi (v, y) hvy).continuousAt (hs.mem_nhds hvy)
          · exact hgood
        have hidentityToParameter (v : V) (y : E) (hy : y ∈ e.target)
            (hvy : v +ᵥ e.symm y ∈ f.source)
            (hzero : ∀ i ≤ k + 1, ContinuousAt
              (fun p : V × E ↦ iteratedFDeriv ℝ i
                (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2) (0, y)) :
            ContinuousAt (fun p : V × E ↦ iteratedFDeriv ℝ (k + 1)
              (fun z : E ↦ f (p.1 +ᵥ e.symm z)) p.2) (v, y) := by
          let G : E → E := fun z ↦ f (v +ᵥ e.symm z)
          let K : V × E → E := fun p ↦ e (p.1 +ᵥ e.symm p.2)
          have hact : ContinuousAt (fun p : V × E ↦ p.1 +ᵥ e.symm p.2) (0, y) :=
            continuousAt_fst.vadd ((e.symm.continuousAt hy).comp continuousAt_snd)
          have hK : ContinuousAt K (0, y) :=
            (e.continuousAt (by simpa using e.map_target hy)).comp hact
          have hG : ContDiffAt ℝ ∞ G (K (0, y)) := by
            simpa [K, e.right_inv hy] using
              VectorActionSpatialSupport.action_coordinate_contDiffAt hsmooth e f he hf v y hy hvy
          have hJ : ContinuousAt (fun p : V × E ↦
              (ftaylorSeries ℝ G (K p)).taylorComp
                (ftaylorSeries ℝ (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2)
                (k + 1)) (0, y) := by
            unfold FormalMultilinearSeries.taylorComp
            apply tendsto_finsetSum
            intro c _
            have ho : ContinuousAt (fun p : V × E ↦
                ftaylorSeries ℝ G (K p) c.length) (0, y) :=
              (hG.continuousAt_iteratedFDeriv (by simp)).comp hK
            have hi : ContinuousAt (fun p : V × E ↦ fun j : Fin c.length ↦
                ftaylorSeries ℝ (fun z : E ↦ e (p.1 +ᵥ e.symm z)) p.2
                  (c.partSize j)) (0, y) :=
              continuousAt_pi.mpr (fun j ↦ hzero _ (c.partSize_le j))
            exact (c.compAlongOrderedFinpartitionL ℝ E E E).continuousAt_uncurry_of_multilinear.comp
              (ho.prodMk hi)
          have htranslated : ContinuousAt (fun p : V × E ↦ iteratedFDeriv ℝ (k + 1)
              (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)) p.2) (0, y) := by
            apply hJ.congr_of_eventuallyEq
            have ht : ∀ᶠ p : V × E in 𝓝 (0, y), p.2 ∈ e.target :=
              continuousAt_snd.preimage_mem_nhds (e.open_target.mem_nhds hy)
            have he' : ∀ᶠ p : V × E in 𝓝 (0, y), p.1 +ᵥ e.symm p.2 ∈ e.source :=
              hact.preimage_mem_nhds (e.open_source.mem_nhds (by simpa using e.map_target hy))
            have hf' : ∀ᶠ p : V × E in 𝓝 (0, y),
                (v + p.1) +ᵥ e.symm p.2 ∈ f.source :=
              ((continuousAt_const.add continuousAt_fst).vadd
                ((e.symm.continuousAt hy).comp continuousAt_snd)).preimage_mem_nhds
                (f.open_source.mem_nhds (by simpa using hvy))
            filter_upwards [ht, he', hf'] with p hp hpE hpF
            have hinner := VectorActionSpatialSupport.action_coordinate_contDiffAt
              hsmooth e e he he p.1 p.2 hp hpE
            have houter : ContDiffAt ℝ ∞ G (K p) := by
              apply VectorActionSpatialSupport.action_coordinate_contDiffAt hsmooth e f he hf
                v (K p) (e.map_source hpE)
              change v +ᵥ e.symm (e (p.1 +ᵥ e.symm p.2)) ∈ f.source
              rw [e.left_inv hpE, ← add_vadd]
              exact hpF
            have hid : (G ∘ (fun z : E ↦ e (p.1 +ᵥ e.symm z)))
                =ᶠ[𝓝 p.2] (fun z : E ↦ f ((v + p.1) +ᵥ e.symm z)) := by
              have hn := (continuousAt_const.vadd (e.symm.continuousAt hp)).preimage_mem_nhds
                (e.open_source.mem_nhds hpE)
              filter_upwards [hn] with z hz
              change p.1 +ᵥ e.symm z ∈ e.source at hz
              change f (v +ᵥ e.symm (e (p.1 +ᵥ e.symm z))) = _
              rw [e.left_inv hz, add_vadd]
            exact ((iteratedFDeriv_comp (f := fun z : E ↦ e (p.1 +ᵥ e.symm z))
              (x := p.2) houter hinner (by simp)).symm.trans
              ((hid.iteratedFDeriv ℝ (k + 1)).self_of_nhds)).symm
          have htranslate : ContinuousAt (fun p : V × E ↦ (p.1 - v, p.2)) (v, y) :=
            (continuousAt_fst.sub continuousAt_const).prodMk continuousAt_snd
          simpa only [Function.comp_def, ← add_sub_assoc, add_sub_cancel_left] using
            htranslated.comp_of_eq htranslate (by simp)
        suffices hgoodParameter : ∀ p ∈ s, ∃ v : V, (v, p.2) ∈ s ∧
            ContinuousAt (fun q : V × E ↦ iteratedFDeriv ℝ (k + 1)
              (fun z : E ↦ f (q.1 +ᵥ e.symm z)) q.2) (v, p.2) by
          intro p hp
          obtain ⟨v, hv, hgood⟩ := hgoodParameter p hp
          have htop := htopGoodToIdentity v p.2 hv hgood
          obtain ⟨hy, hpy⟩ := hdom p hp
          apply (hidentityToParameter p.1 p.2 hy hpy ?_).continuousWithinAt
          intro i hi
          rcases lt_or_eq_of_le hi with hi | rfl
          · obtain ⟨r, hr, hproduct⟩ := VectorActionSpatialSupport.exists_action_coordinate_product
              e e (0 : V) p.2 hy (by simpa using e.map_target hy)
            let t : Set (V × E) := Metric.ball 0 r ×ˢ Metric.ball p.2 r
            have ht : IsOpen t := Metric.isOpen_ball.prod Metric.isOpen_ball
            have hmem : (0, p.2) ∈ t := ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩
            have hderiv := ih i hi e e he he t ht (by
              intro q hq
              exact hproduct q.1 hq.1 q.2 hq.2)
            exact (hderiv (0, p.2) hmem).continuousAt (ht.mem_nhds hmem)
          · exact htop
        
        intro p hp
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs p hp
        let W : Set V := Metric.ball p.1 r
        let B : Set E := Metric.ball p.2 r
        have hWB : W ×ˢ B ⊆ s := by
          intro q hq
          apply hball
          simpa only [W, B, Set.mem_prod, Metric.mem_ball, Prod.dist_eq, max_lt_iff] using hq
        have hfinite (j : ℕ) : FiniteDimensional ℝ (E [×j]→L[ℝ] E) := by
          induction j with
          | zero =>
            exact (continuousMultilinearCurryFin0 ℝ E E).symm.toLinearEquiv.finiteDimensional
          | succ j hj =>
            have := hj
            exact (continuousMultilinearCurryLeftEquiv ℝ
              (fun _ : Fin (j + 1) ↦ E) E).symm.toLinearEquiv.finiteDimensional
        have := hfinite k
        have hd := Analysis.Regularity.montgomery_finiteDimensional_derivative_dense_joint_continuity
          W Metric.isOpen_ball p.2 r
          (fun v ↦ iteratedFDeriv ℝ k (fun z : E ↦ f (v +ᵥ e.symm z)))
          ((hlower k (Nat.lt_succ_self k)).mono hWB)
          (by
            intro v hv y hy
            have hdom' := hdom (v, y) (hWB ⟨hv, hy⟩)
            exact (action_coordinate_contDiffAt hsmooth e f he hf v y
              hdom'.1 hdom'.2).iteratedFDeriv_right (by simp))
          p.2 (Metric.mem_ball_self hr)
        let : Nonempty W := ⟨⟨p.1, Metric.mem_ball_self hr⟩⟩
        obtain ⟨v, hv⟩ := hd.nonempty
        refine ⟨v.val, hWB ⟨v.property, Metric.mem_ball_self hr⟩, ?_⟩
        change ContinuousAt (fun q : V × E ↦ fderiv ℝ
          (iteratedFDeriv ℝ k (fun z : E ↦ f (q.1 +ᵥ e.symm z))) q.2) (v.val, p.2) at hv
        have hc := (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (k + 1) ↦ E) E).symm.continuous.continuousAt.comp hv
        simpa only [fderiv_iteratedFDeriv, Function.comp_apply,
          LinearIsometryEquiv.symm_apply_apply, Function.comp_def] using hc


end HolomorphicAnosov.VectorActionSpatialSupport

