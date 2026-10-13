import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHorizontalInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphInvariantSectionDerivative
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFibreBoundedForcing
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeSmoothness
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeSpatialComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageDerivativeSlope
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphDerivativeBlocks
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphBoundedEvaluationContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- HPS pp.32–35: a bounded invariant preimage slope is differentiable on an
invariant open spatial domain when its derivative blocks are C¹ and uniformly
Lipschitz there. The rational action contracts the unit slope ball; spatial
block comparison bounds its forcing by 4bL. Its strict invariant slope bound
allows differentiation inside the unit ball. The bounded invariant section
criterion constructs and identifies the derivative, with bound 4bL/(1-qc). -/
theorem parameter_graph_preimage_slope_differentiable_on
    {I : Type*} (X Y : I → Type*)
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,CompleteSpace (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    (h : I → I) (R : ∀p,Y p → Y (h p))
    (U : ∀p,Set (Y p)) (hU : ∀p,IsOpen (U p))
    (hRU : ∀p,MapsTo (R p) (U p) (U (h p)))
    (T : ∀p,X p ≃L[ℝ] X (h p))
    (AA : ∀p,Y p → X p →L[ℝ] X (h p))
    (BB : ∀p,Y p → Y p →L[ℝ] X (h p))
    (CC : ∀p,Y p → X p →L[ℝ] Y (h p))
    (DD : ∀p,Y p → Y p →L[ℝ] Y (h p))
    (a k ε c L : NNReal)
    (ha : ∀p,‖(T p).symm.toContinuousLinearMap‖≤a)
    (hA : ∀p y,y∈U p → ‖AA p y-(T p).toContinuousLinearMap‖≤ε)
    (hB : ∀p y,y∈U p → ‖BB p y‖≤ε)
    (hC : ∀p y,y∈U p → ‖CC p y‖≤ε)
    (hD : ∀p y,y∈U p → ‖DD p y‖≤(k:ℝ)+ε)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (hreturn : ((a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε))*c<1)
    (hblocks : ∀p y,y∈U p → ContDiffAt ℝ 1 (AA p) y ∧
      ContDiffAt ℝ 1 (BB p) y ∧ ContDiffAt ℝ 1 (CC p) y ∧ ContDiffAt ℝ 1 (DD p) y)
    (hLip : ∀p,LipschitzOnWith L (AA p) (U p) ∧
      LipschitzOnWith L (BB p) (U p) ∧ LipschitzOnWith L (CC p) (U p) ∧
      LipschitzOnWith L (DD p) (U p))
    (hR : ∀p,LipschitzOnWith c (R p) (U p))
    (hdR : ∀p y,y∈U p → DifferentiableAt ℝ (R p) y)
    (P : ∀p,Y p → Y p →L[ℝ] X p)
    (hP : ∀p y,y∈U p → ‖P p y‖≤1)
    (heq : ∀p y,y∈U p →
      (AA p y-(P (h p) (R p y)).comp (CC p y)).comp (P p y)=
        (P (h p) (R p y)).comp (DD p y)-BB p y) :
    (∀p y,y∈U p → DifferentiableAt ℝ (P p) y) ∧
      ∀p y,y∈U p → ‖fderiv ℝ (P p) y‖≤
        (4*((a:ℝ)/(1-2*(a:ℝ)*ε))*L)/
          (1-((a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε))*c) := by
  let b : NNReal := ⟨(a:ℝ)/(1-2*(a:ℝ)*ε),div_nonneg a.2 (sub_pos.mpr hsmall).le⟩
  let q : NNReal := b*(k+2*ε)
  let M : NNReal := 4*b*L
  have hqeq : (q:ℝ)=(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) := by
    change ((a:ℝ)/(1-2*(a:ℝ)*ε))*((k:ℝ)+2*ε)=_
    ring
  have hq : (q:ℝ)<1 := hqeq ▸ hjet
  have hqc : (q:ℝ)*c<1 := by rwa [hqeq]
  let F (p : I) (z : Y p × (Y (h p) →L[ℝ] X (h p))) : Y p →L[ℝ] X p :=
    (ContinuousLinearMap.inverse (AA p z.1-z.2.comp (CC p z.1))).comp
      (z.2.comp (DD p z.1)-BB p z.1)
  have hInv (p : I) (y : Y p) (hy : y∈U p) (V : Y (h p) →L[ℝ] X (h p)) (hV : ‖V‖≤1) :
      ∃J : X p ≃L[ℝ] X (h p), J.toContinuousLinearMap=AA p y-V.comp (CC p y) ∧
        ‖J.symm.toContinuousLinearMap‖≤b :=
    (parameter_graph_horizontal_inverse (T p) (AA p y) (BB p y) (CC p y)
      a ε (ha p) hsmall (hA p y hy) (hB p y hy) (hC p y hy)).2 V hV
  have hFeq (p : I) (y : Y p) (hy : y∈U p) (V : Y (h p) →L[ℝ] X (h p)) (hV : ‖V‖≤1) :
      (AA p y-V.comp (CC p y)).comp (F p (y,V))=V.comp (DD p y)-BB p y := by
    obtain ⟨J,hJ,_⟩ := hInv p y hy V hV
    dsimp [F]
    rw [← hJ,ContinuousLinearMap.inverse_equiv]
    ext v
    simp
  have hFn (p : I) (y : Y p) (hy : y∈U p) (V : Y (h p) →L[ℝ] X (h p)) (hV : ‖V‖≤1) :
      ‖F p (y,V)‖≤q := by
    rw [hqeq]
    exact (parameter_graph_preimage_slope_interior (T p) (AA p y) (BB p y)
      (CC p y) (DD p y) a k ε (ha p) (hA p y hy) (hB p y hy) (hC p y hy)
      (hD p y hy) hsmall hjet V (F p (y,V)) hV (hFeq p y hy V hV)).1
  have hFv (p : I) (y : Y p) (hy : y∈U p)
      (V W : Y (h p) →L[ℝ] X (h p)) (hV : ‖V‖≤1) (hW : ‖W‖≤1) :
      ‖F p (y,V)-F p (y,W)‖≤(q:ℝ)*‖V-W‖ := by
    obtain ⟨J,hJ,hJn⟩ := hInv p y hy V hV
    have hh := (parameter_graph_slope_comparison (AA p y) (BB p y) (CC p y) (DD p y)
      b (k+ε) ε (by simpa using hD p y hy)).2 V W (F p (y,V)) (F p (y,W))
      J hJ hJn (hFeq p y hy V hV) (hFeq p y hy W hW)
      ((hFn p y hy W hW).trans hq.le) (hC p y hy)
    convert hh using 1
    dsimp [q]
    ring
  have hFs (p : I) (x : Y p) (hx : x∈U p) (y : Y p) (hy : y∈U p)
      (V : Y (h p) →L[ℝ] X (h p)) (hV : ‖V‖≤1) :
      ‖F p (x,V)-F p (y,V)‖≤(M:ℝ)*dist x y := by
    obtain ⟨J,hJ,hJn⟩ := hInv p x hx V hV
    let δ : NNReal := L*nndist x y
    have hδ : (δ:ℝ)=(L:ℝ)*dist x y := by simp [δ]
    have hh := (parameter_graph_slope_spatial_comparison
      (AA p x) (AA p y) (BB p x) (BB p y) (CC p x) (CC p y) (DD p x) (DD p y) b δ
      (by rw [hδ]; simpa [dist_eq_norm] using (hLip p).1.dist_le_mul x hx y hy)
      (by rw [hδ]; simpa [dist_eq_norm] using (hLip p).2.1.dist_le_mul x hx y hy)
      (by rw [hδ]; simpa [dist_eq_norm] using (hLip p).2.2.1.dist_le_mul x hx y hy)
      (by rw [hδ]; simpa [dist_eq_norm] using (hLip p).2.2.2.dist_le_mul x hx y hy)).2
      V (F p (x,V)) (F p (y,V)) J hV ((hFn p y hy V hV).trans hq.le)
      hJ hJn (hFeq p x hx V hV) (hFeq p y hy V hV)
    convert hh using 1
    rw [hδ]
    dsimp [M]
    ring
  have hfix (p : I) (y : Y p) (hy : y∈U p) : P p y=F p (y,P (h p) (R p y)) := by
    obtain ⟨J,hJ,_⟩ := hInv p y hy _ (hP _ _ (hRU p hy))
    have hh := heq p y hy
    rw [← hJ] at hh
    dsimp [F]
    rw [← hJ,ContinuousLinearMap.inverse_equiv]
    ext v
    have hv := congrArg J.symm (DFunLike.congr_fun hh v)
    simpa using hv
  have hPn (p : I) (y : Y p) (hy : y∈U p) : ‖P p y‖<1 := by
    rw [hfix p y hy]
    exact (hFn p y hy _ (hP _ _ (hRU p hy))).trans_lt hq
  have hFd (p : I) (y : Y p) (hy : y∈U p) :
      DifferentiableAt ℝ (F p) (y,P (h p) (R p y)) := by
    obtain ⟨J,hJ,_⟩ := hInv p y hy _ (hP _ _ (hRU p hy))
    have hb := hblocks p y hy
    have hh := (parameter_graph_slope_contDiffAt 1 (y,P (h p) (R p y))
      (fun z ↦ AA p z.1) (fun z ↦ BB p z.1) (fun z ↦ CC p z.1) (fun z ↦ DD p z.1)
      (hb.1.comp _ contDiffAt_fst) (hb.2.1.comp _ contDiffAt_fst)
      (hb.2.2.1.comp _ contDiffAt_fst) (hb.2.2.2.comp _ contDiffAt_fst)).2
      (fun z ↦ z.2) contDiffAt_snd ⟨J,hJ⟩
    exact hh.differentiableAt (by simp)
  have hout := parameter_graph_bounded_invariant_section_differentiable_on
    Y (fun p ↦ Y p →L[ℝ] X p) h R F P U hU hRU M q c M 1 hq hqc hP hR
    (by
      intro p x hx y hy
      rw [hfix p x hx,hfix p y hy]
      calc
        _ ≤ dist (F p (x,P (h p) (R p x))) (F p (x,P (h p) (R p y))) +
            dist (F p (x,P (h p) (R p y))) (F p (y,P (h p) (R p y))) := dist_triangle _ _ _
        _ ≤ _ := add_le_add
          (by simpa [dist_eq_norm] using hFv p x hx _ _ (hP _ _ (hRU p hx)) (hP _ _ (hRU p hy)))
          (by simpa [dist_eq_norm] using hFs p x hx y hy _ (hP _ _ (hRU p hy))))
    hfix (fun p y ↦ fderiv ℝ (R p) y) (fun p y hy ↦ (hdR p y hy).hasFDerivAt)
    (fun p y ↦ fderiv ℝ (F p) (y,P (h p) (R p y)))
    (fun p y hy ↦ (hFd p y hy).hasFDerivAt)
    (fun p y hy ↦ parameter_graph_vertical_derivative_bound (F p) y _ q (hFd p y hy)
      (hPn _ _ (hRU p hy)) (hFv p y hy))
    (by
      intro p y hy
      have hd := (hFd p y hy).hasFDerivAt.comp y
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) y (P (h p) (R p y)))
      apply hd.le_of_lipschitzOn ((hU p).mem_nhds hy)
      apply LipschitzOnWith.of_dist_le_mul
      intro v hv w hw
      simpa only [Function.comp_def,dist_eq_norm] using
        hFs p v hv w hw _ (hP _ _ (hRU p hy)))
  refine ⟨hout.1,?_⟩
  intro p y hy
  convert hout.2 p y hy using 1
  rw [hqeq]
  change _ = (4*((a:ℝ)/(1-2*(a:ℝ)*ε))*L)/(1-((a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε))*c)
  rfl

/-- HPS pp.32–35: the actual preimage graph acquires a second fibre derivative
on each contracting original disc. Its C¹ graph embedding takes that disc
inside the original product disc. The C² ambient derivative gives C¹ block
families, and its uniform Lipschitz bound gives the same bound for each block.
The previous rational-section theorem then differentiates the actual first
derivative, with the explicit uniform bound below. -/
theorem parameter_graph_preimage_c2
    {I : Type*} (X Y : I → Type*)
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,CompleteSpace (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    (h : I → I) (T : ∀p,X p ≃L[ℝ] X (h p))
    (S : ∀p,Y p →L[ℝ] Y (h p))
    (G : ∀p,X p × Y p → X (h p) × Y (h p))
    (hG : ∀p,ContDiff ℝ 2 (G p)) (hzero : ∀p,G p 0=0)
    (t : ∀p,Y p → X p) (ht : ∀p,ContDiff ℝ 1 (t p))
    (htL : ∀p,LipschitzWith 1 (t p)) (ht0 : ∀p,t p 0=0)
    (hgraph : ∀p y,(G p (t p y,y)).1=t (h p) (G p (t p y,y)).2)
    (a k ε L : NNReal) (d : ℝ) (hd : 0<d)
    (ha : ∀p,‖(T p).symm.toContinuousLinearMap‖≤a) (hk : ∀p,‖S p‖≤k)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (hcontract : (k:ℝ)+ε<1)
    (hrem : ∀p,LipschitzWith ε (fun z ↦ G p z-(T p z.1,S p z.2)))
    (hDG : ∀p,LipschitzOnWith L (fderiv ℝ (G p)) (Metric.closedBall 0 d)) :
    (∀p y,y∈Metric.ball (0:Y p) d → DifferentiableAt ℝ (fderiv ℝ (t p)) y) ∧
      ∀p y,y∈Metric.ball (0:Y p) d → ‖fderiv ℝ (fderiv ℝ (t p)) y‖≤
        (4*((a:ℝ)/(1-2*(a:ℝ)*ε))*L)/
          (1-((a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε))*((k:ℝ)+ε)) := by
  let U (p : I) := Metric.ball (0:Y p) d
  let E (p : I) (y : Y p) := (t p y,y)
  let F (p : I) (y : Y p) := fderiv ℝ (G p) (E p y)
  let A (p : I) (y : Y p) := ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp (F p y)).comp
    (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let B (p : I) (y : Y p) := ((ContinuousLinearMap.fst ℝ (X (h p)) (Y (h p))).comp (F p y)).comp
    (ContinuousLinearMap.inr ℝ (X p) (Y p))
  let C (p : I) (y : Y p) := ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp (F p y)).comp
    (ContinuousLinearMap.inl ℝ (X p) (Y p))
  let D (p : I) (y : Y p) := ((ContinuousLinearMap.snd ℝ (X (h p)) (Y (h p))).comp (F p y)).comp
    (ContinuousLinearMap.inr ℝ (X p) (Y p))
  let R (p : I) (y : Y p) := (G p (E p y)).2
  have hEL (p : I) : LipschitzWith 1 (E p) := by
    simpa only [E,max_self,id_eq] using (htL p).prodMk LipschitzWith.id
  have hE0 (p : I) : E p 0=0 := by simp [E,ht0]
  have hEn (p : I) (y : Y p) : ‖E p y‖≤‖y‖ := by
    simpa [hE0] using (hEL p).norm_sub_le y 0
  have hEball (p : I) {y : Y p} (hy : y∈U p) : E p y∈Metric.closedBall 0 d := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact (hEn p y).trans (le_of_lt (by simpa [U,Metric.mem_ball,dist_zero_right] using hy))
  have hGd (p : I) (y : Y p) : HasFDerivAt (G p) (F p y) (E p y) :=
    ((hG p).differentiable (by norm_num) (E p y)).hasFDerivAt
  have hb (p : I) (y : Y p) :
      ‖A p y-(T p).toContinuousLinearMap‖≤ε ∧ ‖B p y‖≤ε ∧ ‖C p y‖≤ε ∧
      ‖D p y-S p‖≤ε := by
    simpa [A,B,C,D] using parameter_graph_derivative_blocks
      (T p).toContinuousLinearMap (S p) (G p) ε (hrem p) (E p y) (F p y) (hGd p y)
  have hDn (p : I) (y : Y p) : ‖D p y‖≤(k:ℝ)+ε := by
    have hh := norm_le_norm_sub_add (D p y) (S p)
    linarith [(hb p y).2.2.2,hk p]
  have hFc (p : I) : ContDiff ℝ 1 (F p) :=
    ((hG p).fderiv_right (show (1:ℕ∞ω)+1≤2 by norm_num)).comp ((ht p).prodMk contDiff_id)
  have hbl (p : I) : ContDiff ℝ 1 (A p) ∧ ContDiff ℝ 1 (B p) ∧
      ContDiff ℝ 1 (C p) ∧ ContDiff ℝ 1 (D p) := by
    exact ⟨(contDiff_const.clm_comp (hFc p)).clm_comp contDiff_const,
      (contDiff_const.clm_comp (hFc p)).clm_comp contDiff_const,
      (contDiff_const.clm_comp (hFc p)).clm_comp contDiff_const,
      (contDiff_const.clm_comp (hFc p)).clm_comp contDiff_const⟩
  have hFL (p : I) : LipschitzOnWith L (F p) (U p) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact ((hDG p).dist_le_mul (E p x) (hEball p hx) (E p y) (hEball p hy)).trans
      (mul_le_mul_of_nonneg_left (by simpa using (hEL p).dist_le_mul x y) L.2)
  have hblocksL (p : I) : LipschitzOnWith L (A p) (U p) ∧ LipschitzOnWith L (B p) (U p) ∧
      LipschitzOnWith L (C p) (U p) ∧ LipschitzOnWith L (D p) (U p) := by
    have hbnd (x y : Y p) : ‖A p x-A p y‖≤‖F p x-F p y‖ ∧
        ‖B p x-B p y‖≤‖F p x-F p y‖ ∧ ‖C p x-C p y‖≤‖F p x-F p y‖ ∧
        ‖D p x-D p y‖≤‖F p x-F p y‖ := by
      let J := F p x-F p y
      have hj := parameter_graph_derivative_blocks
        (0 : X p →L[ℝ] X (h p)) (0 : Y p →L[ℝ] Y (h p)) J ‖J‖₊
        (by simpa only [zero_apply,← Prod.zero_eq_mk,sub_zero] using J.lipschitzWith) 0 J J.hasFDerivAt
      simpa only [J,A,B,C,D,ContinuousLinearMap.comp_sub,ContinuousLinearMap.sub_comp,sub_zero,coe_nnnorm] using hj
    refine ⟨?_,?_,?_,?_⟩ <;> apply LipschitzOnWith.of_dist_le_mul <;> intro x hx y hy
    · simpa [dist_eq_norm] using (hbnd x y).1.trans (by simpa [dist_eq_norm] using (hFL p).dist_le_mul x hx y hy)
    · simpa [dist_eq_norm] using (hbnd x y).2.1.trans (by simpa [dist_eq_norm] using (hFL p).dist_le_mul x hx y hy)
    · simpa [dist_eq_norm] using (hbnd x y).2.2.1.trans (by simpa [dist_eq_norm] using (hFL p).dist_le_mul x hx y hy)
    · simpa [dist_eq_norm] using (hbnd x y).2.2.2.trans (by simpa [dist_eq_norm] using (hFL p).dist_le_mul x hx y hy)
  have hRL (p : I) : LipschitzWith (k+ε) (R p) := by
    have hr : LipschitzWith ε (fun y ↦ R p y-S p y) := by
      have hh := LipschitzWith.prod_snd.comp ((hrem p).comp (hEL p))
      simpa only [one_mul,mul_one,Function.comp_def,Prod.snd_sub,ContinuousLinearEquiv.coe_coe] using hh
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hn := hr.norm_sub_le x y
    have hS := (S p).le_opNorm (x-y)
    have he : R p x-R p y=(R p x-S p x-(R p y-S p y))+S p (x-y) := by rw [map_sub]; abel
    rw [dist_eq_norm,he]
    calc
      _ ≤ ‖R p x-S p x-(R p y-S p y)‖+‖S p (x-y)‖ := norm_add_le _ _
      _ ≤ (ε:ℝ)*‖x-y‖+(k:ℝ)*‖x-y‖ := add_le_add hn (hS.trans (mul_le_mul_of_nonneg_right (hk p) (norm_nonneg _)))
      _ = _ := by rw [dist_eq_norm]; push_cast; ring
  have hR0 (p : I) : R p 0=0 := by simp [R,hE0,hzero]
  have hRU (p : I) : MapsTo (R p) (U p) (U (h p)) := by
    intro y hy
    have hn := (hRL p).norm_sub_le y 0
    simp only [hR0,sub_zero] at hn
    have hy' : ‖y‖<d := by simpa [U,Metric.mem_ball,dist_zero_right] using hy
    simp only [U,Metric.mem_ball,dist_zero_right]
    apply hn.trans_lt
    have hc : ((k+ε:NNReal):ℝ)<1 := by exact_mod_cast hcontract
    nlinarith [norm_nonneg y]
  have hRD (p : I) (y : Y p) : DifferentiableAt ℝ (R p) y :=
    (((hG p).differentiable (by norm_num)).comp
      (((ht p).differentiable (by norm_num)).prodMk differentiable_id)).snd y
  have hq0 : 0≤(a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε) :=
    div_nonneg (mul_nonneg a.2 (by positivity)) (sub_pos.mpr hsmall).le
  have hqc : ((a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε))*((k+ε:NNReal):ℝ)<1 := by
    have hc : ((k+ε:NNReal):ℝ)<1 := by exact_mod_cast hcontract
    exact (mul_le_of_le_one_right hq0 hc.le).trans_lt hjet
  have hout := parameter_graph_preimage_slope_differentiable_on X Y h R U
    (fun _ ↦ Metric.isOpen_ball) hRU T A B C D a k ε (k+ε) L ha
    (fun p y _ ↦ by simpa using (hb p y).1) (fun p y _ ↦ (hb p y).2.1)
    (fun p y _ ↦ (hb p y).2.2.1) (fun p y _ ↦ hDn p y) hsmall hjet hqc
    (fun p y _ ↦ ⟨(hbl p).1.contDiffAt,(hbl p).2.1.contDiffAt,
      (hbl p).2.2.1.contDiffAt,(hbl p).2.2.2.contDiffAt⟩) hblocksL
    (fun p ↦ (hRL p).lipschitzOnWith) (fun p y _ ↦ hRD p y)
    (fun p ↦ fderiv ℝ (t p)) (fun p y _ ↦ norm_fderiv_le_of_lipschitz ℝ (htL p))
    (by
      intro p y hy
      apply parameter_graph_preimage_derivative_equation (G p) (t p) (t (h p)) y
        (F p y) (hGd p y) ((ht p).differentiable (by norm_num) y)
        ((ht (h p)).differentiable (by norm_num) _) (hgraph p)
      · intro x v
        change (F p y (x,v)).1=(F p y (x,0)).1+(F p y (0,v)).1
        rw [← Prod.fst_add,← map_add]
        simp
      · intro x v
        change (F p y (x,v)).2=(F p y (x,0)).2+(F p y (0,v)).2
        rw [← Prod.snd_add,← map_add]
        simp)
  exact hout

/-- Continuous original vector evaluations of the affine derivative fixed
section. No continuity of the candidate derivative D is assumed: geometric
Picard convergence constructs a continuous-evaluation fixed section, and
bounded uniqueness identifies it with D. The continuity-preservation premise
concerns only the explicit affine action H+V∘Dnext∘W, so joint continuous
evaluations of the action derivatives and return derivative verify it without
assuming the derivative being proved continuous. HPS pp.32–35 and62. -/
theorem parameter_graph_affine_derivative_evaluation_continuous
    {I Z A : Type*} [TopologicalSpace Z] [TopologicalSpace A]
    (X Y : A → Type*)
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [∀p,CompleteSpace (Y p)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := Y))
    (p : I → A) (R : I → I)
    (H : ∀i,X (p i) →L[ℝ] Y (p i))
    (V : ∀i,Y (p (R i)) →L[ℝ] Y (p i))
    (W : ∀i,X (p i) →L[ℝ] X (p (R i)))
    (B q c : NNReal) (hqc : (q:ℝ)*c<1)
    (hH : ∀i,‖H i‖≤B) (hV : ∀i,‖V i‖≤q) (hW : ∀i,‖W i‖≤c)
    (a : Z → I) (ha : Continuous (fun z ↦ p (a z)))
    (v : ∀z,X (p (a z))) (hv : Continuous (fun z ↦ ‖v z‖))
    (hpreserve : ∀D : ∀i,X (p i) →L[ℝ] Y (p i),
      Continuous (fun z ↦ (⟨p (a z),D (a z) (v z)⟩ : Sigma Y)) →
      Continuous (fun z ↦ (⟨p (a z),H (a z) (v z)+
        V (a z) (D (R (a z)) (W (a z) (v z)))⟩ : Sigma Y)))
    (D : ∀i,X (p i) →L[ℝ] Y (p i))
    (hDb : ∃M : ℝ,∀i,‖D i‖≤M)
    (hDi : ∀i,D i=H i+(V i).comp ((D (R i)).comp (W i))) :
    Continuous (fun z ↦ (⟨p (a z),D (a z) (v z)⟩ : Sigma Y)) := by
  let E (i : I) := X (p i) →L[ℝ] Y (p i)
  let Φ (i : I) (D : E (R i)) : E i := H i+(V i).comp (D.comp (W i))
  have hΦ (i : I) : LipschitzWith (q*c) (Φ i) := by
    apply LipschitzWith.of_dist_le_mul
    intro D D'
    rw [dist_eq_norm,dist_eq_norm]
    have heq : Φ i D-Φ i D'=(V i).comp ((D-D').comp (W i)) := by
      ext x
      simp [Φ,map_sub]
    rw [heq]
    calc
      _ ≤ ‖V i‖*‖(D-D').comp (W i)‖ := (V i).opNorm_comp_le _
      _ ≤ (q:ℝ)*(‖D-D'‖*(c:ℝ)) := mul_le_mul (hV i)
        (((D-D').opNorm_comp_le _).trans
          (mul_le_mul_of_nonneg_left (hW i) (norm_nonneg _))) (norm_nonneg _) q.2
      _ = _ := by simp only [NNReal.coe_mul]; ring
  let L (z : Z) : E (a z) →L[ℝ] Y (p (a z)) := ContinuousLinearMap.apply ℝ _ (v z)
  have hL (z : Z) : ‖L z‖≤‖v z‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro D
    exact (D.le_opNorm _).trans_eq (mul_comm _ _)
  obtain ⟨D',_,_,hunique,hcont⟩ := parameter_graph_bounded_evaluation_continuity
    E e R Φ (q*c) B (by exact_mod_cast hqc) hΦ (fun i ↦ by simpa [Φ] using hH i)
    a (fun z ↦ p (a z)) ha L (fun z ↦ ‖v z‖) hv (fun z ↦ norm_nonneg _) hL
    (by simpa [L] using parameter_graph_atlas_zero_continuous e (fun z ↦ p (a z)) ha)
    (fun D hD ↦ hpreserve D hD)
  have heq := hunique D hDb (fun i ↦ (hDi i).symm)
  rw [heq]
  change Continuous (fun z ↦ (⟨p (a z),D' (a z) (v z)⟩ : Sigma Y)) at hcont
  exact hcont

/-- Differentiating an already differentiable invariant section on an open
invariant domain gives the affine fixed equation for its actual derivative.
The return need not be invertible. This is the equation used with bounded
uniqueness in the preceding evaluation-continuity bridge, HPS pp.32–35. -/
theorem parameter_graph_actual_derivative_affine_equation_on
    {I : Type*} (X Y : I → Type*)
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    (h : I → I) (R : ∀p,X p → X (h p))
    (F : ∀p,X p × Y (h p) → Y p) (P : ∀p,X p → Y p)
    (U : ∀p,Set (X p)) (hU : ∀p,IsOpen (U p))
    (hRU : ∀p,MapsTo (R p) (U p) (U (h p)))
    (hP : ∀p x,x∈U p → DifferentiableAt ℝ (P p) x)
    (hR : ∀p x,x∈U p → DifferentiableAt ℝ (R p) x)
    (hF : ∀p x,x∈U p → DifferentiableAt ℝ (F p) (x,P (h p) (R p x)))
    (hfix : ∀p x,x∈U p → P p x=F p (x,P (h p) (R p x))) :
    ∀p x,x∈U p →
      fderiv ℝ (P p) x =
        (fderiv ℝ (F p) (x,P (h p) (R p x))).comp (ContinuousLinearMap.inl ℝ _ _) +
        ((fderiv ℝ (F p) (x,P (h p) (R p x))).comp (ContinuousLinearMap.inr ℝ _ _)).comp
          ((fderiv ℝ (P (h p)) (R p x)).comp (fderiv ℝ (R p) x)) := by
  intro p x hx
  have hc := (hF p x hx).hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk
    ((hP (h p) (R p x) (hRU p hx)).hasFDerivAt.comp x (hR p x hx).hasFDerivAt))
  have he : (F p ∘ fun y ↦ (y,P (h p) (R p y))) =ᶠ[𝓝 x] P p := by
    filter_upwards [(hU p).mem_nhds hx] with y hy
    exact (hfix p y hy).symm
  have hd := hc.congr_of_eventuallyEq he.symm
  have hh := (hP p x hx).hasFDerivAt.unique hd
  rw [hh]
  ext v
  change fderiv ℝ (F p) (x,P (h p) (R p x))
      (v,fderiv ℝ (P (h p)) (R p x) (fderiv ℝ (R p) x v)) =
    fderiv ℝ (F p) (x,P (h p) (R p x)) (v,0)+
      fderiv ℝ (F p) (x,P (h p) (R p x))
        (0,fderiv ℝ (P (h p)) (R p x) (fderiv ℝ (R p) x v))
  rw [← map_add]
  simp

/-- Explicit coefficient version of affine derivative evaluation continuity.
A continuous lifted tangent return transports anchor and input vector exactly;
H has continuous evaluation and V sends continuous receiving vectors to
continuous output vectors. These hypotheses imply continuity preservation of
the affine action, without referring to continuity of the unknown derivative.
The compatibility equality is literal for the usual tangent return
(point,vector) ↦ (R(point),DR(point)vector). HPS pp.32–35,62. -/
theorem parameter_graph_affine_derivative_evaluation_continuous_of_return
    {I Z A : Type*} [TopologicalSpace Z] [TopologicalSpace A]
    (X Y : A → Type*)
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [∀p,CompleteSpace (Y p)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := Y))
    (p : I → A) (R : I → I)
    (H : ∀i,X (p i) →L[ℝ] Y (p i))
    (V : ∀i,Y (p (R i)) →L[ℝ] Y (p i))
    (W : ∀i,X (p i) →L[ℝ] X (p (R i)))
    (B q c : NNReal) (hqc : (q:ℝ)*c<1)
    (hH : ∀i,‖H i‖≤B) (hV : ∀i,‖V i‖≤q) (hW : ∀i,‖W i‖≤c)
    (a : Z → I) (ha : Continuous (fun z ↦ p (a z)))
    (v : ∀z,X (p (a z))) (hv : Continuous (fun z ↦ ‖v z‖))
    (ρ : Z → Z) (hρ : Continuous ρ)
    (htransport : ∀D : ∀i,X (p i) →L[ℝ] Y (p i),∀z,
      (⟨p (R (a z)),D (R (a z)) (W (a z) (v z))⟩ : Sigma Y)=
        (⟨p (a (ρ z)),D (a (ρ z)) (v (ρ z))⟩ : Sigma Y))
    (hHc : Continuous (fun z ↦ (⟨p (a z),H (a z) (v z)⟩ : Sigma Y)))
    (hVc : ∀u : ∀z,Y (p (R (a z))),
      Continuous (fun z ↦ (⟨p (R (a z)),u z⟩ : Sigma Y)) →
      Continuous (fun z ↦ (⟨p (a z),V (a z) (u z)⟩ : Sigma Y)))
    (D : ∀i,X (p i) →L[ℝ] Y (p i))
    (hDb : ∃M : ℝ,∀i,‖D i‖≤M)
    (hDi : ∀i,D i=H i+(V i).comp ((D (R i)).comp (W i))) :
    Continuous (fun z ↦ (⟨p (a z),D (a z) (v z)⟩ : Sigma Y)) := by
  apply parameter_graph_affine_derivative_evaluation_continuous X Y e p R H V W
    B q c hqc hH hV hW a ha v hv _ D hDb hDi
  intro D hD
  have hu : Continuous (fun z ↦
      (⟨p (R (a z)),D (R (a z)) (W (a z) (v z))⟩ : Sigma Y)) :=
    (hD.comp hρ).congr (fun z ↦ (htransport D z).symm)
  exact parameter_graph_atlas_add_continuous e (fun z ↦ p (a z)) ha
    (fun z ↦ H (a z) (v z)) (fun z ↦ V (a z) (D (R (a z)) (W (a z) (v z))))
    hHc (hVc _ hu)

end HolomorphicAnosov
