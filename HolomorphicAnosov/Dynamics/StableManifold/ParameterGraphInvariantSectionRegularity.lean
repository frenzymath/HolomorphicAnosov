import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalSectionDifferentiability
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphProductAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPullbackAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalSectionC1
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointTangentAction

noncomputable section
open Set
open scoped _root_.Topology ContDiff
namespace HolomorphicAnosov
universe u v w

/-- The finite-order local invariant-section theorem in original finite-rank
bundles. A centered contracting return preserves every smaller original ball.
Induct on the requested order: first obtain C¹ and a bounded actual derivative,
then apply the preceding order to the original section and to its affine tangent
section on a smaller closed rectangle. The tangent action loses exactly one
order and contracts by q*c. Continuity and derivatives are always those of the
original atlases. The value universe is closed under Hom from the source, so
the induction applies literally to the actual derivative bundle.
Source: HPS, Invariant Manifolds, pp.32–36,62, differentiable-section induction. -/
theorem parameter_graph_invariant_section_regularity
    {A : Type w} [TopologicalSpace A] [CompactSpace A] {X : A → Type u}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [TopologicalSpace (Sigma X)] (e : FiniteRankNormedAtlas (E := X))
    (h : A→A) (hh : Continuous h) (R : ∀p,X p→X (h p))
    (c : NNReal) (hc : (c:ℝ)<1) (hzero : ∀p,R p 0=0) (n : ℕ) :
    ∀ {Y : A → Type (max u v)} [∀p,NormedAddCommGroup (Y p)]
      [∀p,NormedSpace ℝ (Y p)] [∀p,CompleteSpace (Y p)] [TopologicalSpace (Sigma Y)]
      (f : FiniteRankNormedAtlas (E := Y))
      (F : ∀p,X p×Y (h p)→Y p) (P : ∀p,X p→Y p)
      (d M M₀ : ℝ) (q : NNReal),
      0<d → M<M₀ → (q:ℝ)<1 →
      (∀p,LipschitzOnWith c (R p) (Metric.ball 0 d)) →
      JointFiberContDiffOn e e h n {z : Sigma X | ‖z.2‖<d} R →
      ContinuousOn (fun z : Sigma X ↦ (⟨z.1,P z.1 z.2⟩ : Sigma Y))
        {z : Sigma X | ‖z.2‖<d} →
      (∀p x,‖x‖<d → ‖P p x‖≤M) →
      (∀p x,‖x‖<d → P p x=F p (x,P (h p) (R p x))) →
      (∀p x,‖x‖≤d → LipschitzOnWith q (fun v ↦ F p (x,v)) (Metric.closedBall 0 M₀)) →
      ∀ W : Set (Sigma (fun p ↦ X p×Y (h p))),
      (letI := ParameterGraphPullbackAtlas.topology f h hh;
        @IsOpen _ (ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))) W) →
      (letI := ParameterGraphPullbackAtlas.topology f h hh;
        letI := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p));
        JointFiberContDiffOn
          (ParameterGraphProductAtlas.atlas e (ParameterGraphPullbackAtlas.atlas f h hh))
          f id n W F) →
      (∀p (x:X p) (v:Y (h p)),‖x‖≤d → ‖v‖≤M₀ →
        (⟨p,(x,v)⟩ : Sigma (fun p ↦ X p×Y (h p)))∈W) →
      ∃δ : ℝ,0<δ ∧ δ≤d ∧ JointFiberContDiffOn e f id n {z : Sigma X | ‖z.2‖<δ} P := by
  induction n with
  | zero =>
    intro Y _ _ _ _ f F P d M M₀ q hd _ _ _ _ hPc _ _ _ W _ _ _
    exact ⟨d,hd,le_refl d,(parameter_graph_local_joint_zero_iff e f id continuous_id P _
      (isOpen_lt e.continuous_norm continuous_const)).mpr hPc⟩
  | succ n ih =>
    intro Y _ _ _ _ f F P d M M₀ q hd hM hq hR hRj hPc hP hinv hvertical W hW hF hrect
    let := ParameterGraphPullbackAtlas.topology f h hh
    let fh := ParameterGraphPullbackAtlas.atlas f h hh
    let := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
    have hqc : (q:ℝ)*c<1 :=
      (mul_le_mul_of_nonneg_left hc.le q.2).trans_lt (by simpa using hq)
    have hRU (p : A) : MapsTo (R p) (Metric.ball 0 d) (Metric.ball 0 d) :=
      (parameter_graph_return_smaller_ball (R p) c d d hd (le_refl d) hc.le (hR p) (hzero p)).1
    have hR1 := hRj.of_le (show 1≤n+1 by omega)
    have hF1 := hF.of_le (show 1≤n+1 by omega)
    have hP1 := parameter_graph_local_section_c1 e f h hh R F P d M M₀ q c hM hq hqc
      hP hRU hR hR1 hPc hinv hvertical W hW hF1 hrect
    have hRd (p : A) (x : X p) (hx : ‖x‖<d) : DifferentiableAt ℝ (R p) x :=
      (hR1.1 ⟨p,x⟩ hx).differentiableAt (by simp)
    obtain ⟨B,hPd,hDb⟩ := parameter_graph_local_section_differentiable h e f fh R F P
      d M M₀ q c hM hq hqc hP hRU hR hRd hinv hvertical W hW hF1 hrect
    obtain ⟨δ,hδ,hδd,hPn⟩ := ih f F P d M M₀ q hd hM hq hR
      (hRj.of_le (Nat.le_succ n)) hPc hP hinv hvertical W hW
      (hF.of_le (Nat.le_succ n)) hrect
    let d₁ := δ/2
    have hd₁ : 0<d₁ := half_pos hδ
    have hd₁δ : d₁<δ := half_lt_self hδ
    have hd₁d : d₁≤d := hd₁δ.le.trans hδd
    let Uδ : Set (Sigma X) := {z | ‖z.2‖<δ}
    have hUδ : IsOpen Uδ := isOpen_lt e.continuous_norm continuous_const
    have hRδ (p : A) := parameter_graph_return_smaller_ball (R p) c d δ hd hδd hc.le (hR p) (hzero p)
    have hRd₁ (p : A) := parameter_graph_return_smaller_ball (R p) c d d₁ hd hd₁d hc.le (hR p) (hzero p)
    have hRP (p : A) (x : X p) (hx : ‖x‖<d) : ‖P (h p) (R p x)‖≤M :=
      hP (h p) (R p x) (by simpa only [Metric.mem_ball,dist_zero_right] using
        (hRU p (by simpa only [Metric.mem_ball,dist_zero_right] using hx)))
    have hFd (p : A) (x : X p) (hx : ‖x‖<d) :
        DifferentiableAt ℝ (F p) (x,P (h p) (R p x)) :=
      (hF1.1 ⟨p,(x,P (h p) (R p x))⟩
        (hrect p x _ hx.le ((hRP p x hx).trans hM.le))).differentiableAt (by simp)
    let D (p : A) := fderiv ℝ (P p)
    let Θ (p : A) (a : X p×(X (h p)→L[ℝ] Y (h p))) : X p→L[ℝ] Y p :=
      (fderiv ℝ (F p) (a.1,P (h p) (R p a.1))).comp
        ((ContinuousLinearMap.id ℝ (X p)).prod (a.2.comp (fderiv ℝ (R p) a.1)))
    have hDinv (p : A) (x : X p) (hx : ‖x‖<d₁) :
        D p x=Θ p (x,D (h p) (R p x)) := by
      have hx' := hx.trans_le hd₁d
      have he := parameter_graph_actual_derivative_affine_equation_on X Y h R F P
        (fun _ ↦ Metric.ball 0 d) (fun _ ↦ Metric.isOpen_ball) hRU
        (fun p x hx ↦ hPd p x (by simpa using hx))
        (fun p x hx ↦ hRd p x (by simpa using hx))
        (fun p x hx ↦ hFd p x (by simpa using hx))
        (fun p x hx ↦ hinv p x (by simpa using hx)) p x (by simpa using hx')
      change fderiv ℝ (P p) x = _
      rw [he]
      ext v
      change fderiv ℝ (F p) (x,P (h p) (R p x)) (v,0)+
        fderiv ℝ (F p) (x,P (h p) (R p x)) (0,fderiv ℝ (P (h p)) (R p x) (fderiv ℝ (R p) x v)) =
        fderiv ℝ (F p) (x,P (h p) (R p x)) (v,fderiv ℝ (P (h p)) (R p x) (fderiv ℝ (R p) x v))
      rw [← map_add]
      simp
    let := ParameterGraphHomAtlas.topology e f
    let df := ParameterGraphHomAtlas.atlas e f
    let := ParameterGraphPullbackAtlas.topology df h hh
    let dfh := ParameterGraphPullbackAtlas.atlas df h hh
    let := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ X (h p)→L[ℝ] Y (h p))
    let Ω : Set (Sigma (fun p ↦ X p×(X (h p)→L[ℝ] Y (h p)))) :=
      {a | (⟨a.1,a.2.1⟩ : Sigma X)∈Uδ}
    have hΩ : IsOpen Ω := hUδ.preimage ParameterGraphProductAtlas.fst_continuous
    have hΘ : JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e dfh) df id n Ω Θ :=
      parameter_graph_local_joint_tangent_action e f h hh n Uδ hUδ R P
        (hRj.mono (fun _ hz ↦ hz.trans_le hδd)) hPn
        (fun a ha ↦ by
          change ‖R a.1 a.2‖<δ
          have hz : a.2∈Metric.ball 0 δ := by
            simpa only [Metric.mem_ball,dist_zero_right] using (show ‖a.2‖<δ from ha)
          simpa only [Metric.mem_ball,dist_zero_right] using ((hRδ a.1).1 hz))
        F W hW hF
        (fun a ha ↦ hrect _ _ _ (ha.trans_le hδd).le
          ((hRP _ _ (ha.trans_le hδd)).trans hM.le))
    let M₁ := (B:ℝ)/(1-(q:ℝ)*c)
    have hDc : ContinuousOn (fun z : Sigma X ↦ (⟨z.1,D z.1 z.2⟩ : Sigma (fun p ↦ X p→L[ℝ] Y p)))
        {z : Sigma X | ‖z.2‖<d₁} := by
      have hj := parameter_graph_local_joint_derivative e f P 0 _
        (isOpen_lt e.continuous_norm continuous_const) hP1
      exact (parameter_graph_local_joint_zero_iff e df id continuous_id D _
        (isOpen_lt e.continuous_norm continuous_const)).mp hj |>.mono
        (fun _ hz ↦ hz.trans_le hd₁d)
    have hΘL (p : A) (x : X p) (hx : ‖x‖≤d₁) :
        LipschitzOnWith (q*c) (fun Q ↦ Θ p (x,Q)) (Metric.closedBall 0 (M₁+1)) := by
      have hx' : ‖x‖<d := (hx.trans_lt hd₁δ).trans_le hδd
      apply (parameter_graph_tangent_action_lipschitz
        (fderiv ℝ (F p) (x,P (h p) (R p x))) (fderiv ℝ (R p) x) q c ?_ ?_).lipschitzOnWith
      · exact parameter_graph_vertical_derivative_bound_on_ball (F p) x
          (P (h p) (R p x)) M₀ q (hFd p x hx') ((hRP p x hx').trans_lt hM)
          (hvertical p x hx'.le)
      · exact norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds
          (by simpa only [Metric.mem_ball,dist_zero_right] using hx')) (hR p)
    obtain ⟨η,hη,hηd,hDn⟩ := ih df Θ D d₁ M₁ (M₁+1) (q*c) hd₁ (by linarith)
      (by exact_mod_cast hqc) (fun p ↦ (hRd₁ p).2)
      ((hRj.of_le (Nat.le_succ n)).mono (fun _ hz ↦ hz.trans_le hd₁d)) hDc
      (fun p x hx ↦ hDb p x (hx.trans_le hd₁d)) hDinv hΘL Ω hΩ hΘ
      (fun p x Q hx _ ↦ hx.trans_lt hd₁δ)
    refine ⟨η,hη,hηd.trans hd₁d,?_⟩
    exact parameter_graph_local_joint_of_derivative e f P n _
      (isOpen_lt e.continuous_norm continuous_const)
      (hPc.mono (fun _ hz ↦ hz.trans_le (hηd.trans hd₁d)))
      (fun z hz ↦ hPd z.1 z.2 (hz.trans_le (hηd.trans hd₁d))) hDn

end HolomorphicAnosov
