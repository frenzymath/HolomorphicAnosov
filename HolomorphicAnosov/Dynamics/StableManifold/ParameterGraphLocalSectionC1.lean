import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCompactForcing
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphProductAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPullbackAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalSectionDifferentiability
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageC2
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointContinuity

noncomputable section
open Set
open scoped _root_.Topology ContDiff
namespace HolomorphicAnosov

/-- Local continuity of actual derivative evaluations on the tangent domain
upgrades fibre differentiability to joint C¹. The genuine finite-rank Hom
atlas reconstructs operator continuity from fixed-frame evaluations. -/
theorem parameter_graph_local_c1_of_tangent_evaluation
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (g : ∀p,E p→F p) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : ContinuousOn (fun z : Sigma E ↦ (⟨z.1,g z.1 z.2⟩ : Sigma F)) U)
    (hd : ∀z∈U,DifferentiableAt ℝ (g z.1) z.2)
    (heval : Continuous (fun z : {z : ParameterGraphTangentPoint E //
        (⟨z.base,z.point⟩ : Sigma E)∈U} ↦
      (⟨z.1.base,fderiv ℝ (g z.1.base) z.1.point z.1.vector⟩ : Sigma F))) :
    JointFiberContDiffOn e f id 1 U g := by
  let := ParameterGraphHomAtlas.topology e f
  apply parameter_graph_local_joint_of_derivative e f g 0 U hU hg hd
  apply (parameter_graph_local_joint_zero_iff e (ParameterGraphHomAtlas.atlas e f)
    id continuous_id (fun p ↦ fderiv ℝ (g p)) U hU).mpr
  rw [continuousOn_iff_continuous_domRestrict]
  apply ParameterGraphHomAtlas.continuous_of_evaluation e f
    (fun z : U ↦ z.1.1)
    ((parameter_graph_atlas_projection_continuous e).comp continuous_subtype_val)
  intro i v
  let S := {z : U // z.1.1∈(e.chart i).baseSet}
  have hx : Continuous (fun z : S ↦ (z.1.1 : Sigma E)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hv : Continuous (fun z : S ↦
      (⟨z.1.1.1,(e.coordinates i z.1.1.1 z.2).symm v⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp
      (((parameter_graph_atlas_projection_continuous e).comp hx).subtype_mk
        (fun z ↦ z.2) |>.prodMk continuous_const)
  exact heval.comp ((ParameterGraphTangentPoint.continuous_mk
    (fun z : S ↦ z.1.1.1) (fun z ↦ z.1.1.2)
    (fun z ↦ (e.coordinates i z.1.1.1 z.2).symm v) hx hv).subtype_mk (fun z ↦ z.1.2))

/-- A continuous bounded invariant section of a jointly C¹ fibre action is
jointly C¹ on the original invariant ball. Quantitative differentiability is
supplied by bounded forcing. Its actual derivative satisfies an affine section
contraction; the continuous tangent return and continuous first-jet evaluations
of the action preserve continuity. Weighted Picard convergence and bounded
uniqueness then prove continuity of the actual derivative, HPS pp.32–36,62. -/
theorem parameter_graph_local_section_c1
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {X Y : A → Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)] [∀p,CompleteSpace (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := X)) (f : FiniteRankNormedAtlas (E := Y))
    (h : A→A) (hh : Continuous h)
    (R : ∀p,X p→X (h p)) (F : ∀p,X p×Y (h p)→Y p) (P : ∀p,X p→Y p)
    (d M M₀ : ℝ) (q c : NNReal) (hM : M<M₀)
    (hq : (q:ℝ)<1) (hqc : (q:ℝ)*c<1)
    (hP : ∀p x,‖x‖<d → ‖P p x‖≤M)
    (hRU : ∀p,MapsTo (R p) (Metric.ball 0 d) (Metric.ball 0 d))
    (hR : ∀p,LipschitzOnWith c (R p) (Metric.ball 0 d))
    (hRj : JointFiberContDiffOn e e h 1 {z : Sigma X | ‖z.2‖<d} R)
    (hPc : ContinuousOn (fun z : Sigma X ↦ (⟨z.1,P z.1 z.2⟩ : Sigma Y))
      {z : Sigma X | ‖z.2‖<d})
    (hinv : ∀p x,‖x‖<d → P p x=F p (x,P (h p) (R p x)))
    (hvertical : ∀p x,‖x‖≤d →
      LipschitzOnWith q (fun v ↦ F p (x,v)) (Metric.closedBall 0 M₀))
    (W : Set (Sigma (fun p ↦ X p×Y (h p))))
    (hW : letI := ParameterGraphPullbackAtlas.topology f h hh
      @IsOpen _ (ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))) W)
    (hF : letI := ParameterGraphPullbackAtlas.topology f h hh
      letI := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
      JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e (ParameterGraphPullbackAtlas.atlas f h hh)) f id 1 W F)
    (hrect : ∀p (x:X p) (v:Y (h p)), ‖x‖≤d → ‖v‖≤M₀ →
      (⟨p,(x,v)⟩ : Sigma (fun p ↦ X p×Y (h p)))∈W) :
    JointFiberContDiffOn e f id 1 {z : Sigma X | ‖z.2‖<d} P := by
  let := ParameterGraphPullbackAtlas.topology f h hh
  let fh := ParameterGraphPullbackAtlas.atlas f h hh
  let := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
  let U : Set (Sigma X) := {z | ‖z.2‖<d}
  have hU : IsOpen U := isOpen_lt e.continuous_norm continuous_const
  have hRd (p : A) (x : X p) (hx : ‖x‖<d) : DifferentiableAt ℝ (R p) x :=
    (hRj.1 ⟨p,x⟩ hx).differentiableAt (by simp)
  obtain ⟨B,hPd,hDb⟩ := parameter_graph_local_section_differentiable h e f fh R F P
    d M M₀ q c hM hq hqc hP hRU hR hRd hinv hvertical W hW hF hrect
  obtain ⟨C,hC,_⟩ := parameter_graph_compact_rectangular_forcing e fh f id continuous_id
    F 1 (le_refl 1) W d M₀ hW hF hrect
  have hRP (p : A) (x : X p) (hx : ‖x‖<d) : ‖P (h p) (R p x)‖≤M :=
    hP (h p) (R p x) (by simpa using hRU p (by simpa using hx))
  have hFd (p : A) (x : X p) (hx : ‖x‖<d) :
      DifferentiableAt ℝ (F p) (x,P (h p) (R p x)) :=
    (hF.1 ⟨p,(x,P (h p) (R p x))⟩
      (hrect p x _ hx.le ((hRP p x hx).trans hM.le))).differentiableAt (by simp)
  apply parameter_graph_local_c1_of_tangent_evaluation e f P U hU hPc
    (fun z hz ↦ hPd z.1 z.2 hz)
  let I := U
  let Z := {z : ParameterGraphTangentPoint X // (⟨z.base,z.point⟩ : Sigma X)∈U}
  let a : Z → I := fun z ↦ ⟨⟨z.1.base,z.1.point⟩,z.2⟩
  let p : I → A := fun i ↦ i.1.1
  let R' : I → I := fun i ↦ ⟨⟨h i.1.1,R i.1.1 i.1.2⟩,
    by
      change ‖R i.1.1 i.1.2‖<d
      simpa only [Metric.mem_ball,dist_zero_right] using hRU i.1.1
        (by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖i.1.2‖<d from i.2))⟩
  let D (i : I) := fderiv ℝ (P (p i)) i.1.2
  let J (i : I) := fderiv ℝ (F (p i)) (i.1.2,P (h (p i)) (R (p i) i.1.2))
  let H (i : I) := (J i).comp (ContinuousLinearMap.inl ℝ (X (p i)) (Y (h (p i))))
  let V (i : I) := (J i).comp (ContinuousLinearMap.inr ℝ (X (p i)) (Y (h (p i))))
  let W' (i : I) := fderiv ℝ (R (p i)) i.1.2
  have hHb (i : I) : ‖H i‖≤C := by
    apply ContinuousLinearMap.opNorm_le_bound _ C.2
    intro v
    have hJi : ‖J i‖≤C := hC (p i) (i.1.2,P (h (p i)) (R (p i) i.1.2))
      i.2.le ((hRP (p i) i.1.2 i.2).trans hM.le)
    calc
      ‖H i v‖ = ‖J i (v,0)‖ := rfl
      _ ≤ ‖J i‖*‖(v,(0:Y (h (p i))))‖ := (J i).le_opNorm _
      _ = ‖J i‖*‖v‖ := by rw [Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg v)]
      _ ≤ (C:ℝ)*‖v‖ := mul_le_mul_of_nonneg_right hJi (norm_nonneg v)
  have hVb (i : I) : ‖V i‖≤q :=
    parameter_graph_vertical_derivative_bound_on_ball (F (p i)) i.1.2
      (P (h (p i)) (R (p i) i.1.2)) M₀ q (hFd (p i) i.1.2 i.2)
      ((hRP (p i) i.1.2 i.2).trans_lt hM) (hvertical (p i) i.1.2 i.2.le)
  have hWb (i : I) : ‖W' i‖≤c :=
    norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds
      (by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖i.1.2‖<d from i.2))) (hR (p i))
  have hDi (i : I) : D i=H i+(V i).comp ((D (R' i)).comp (W' i)) :=
    parameter_graph_actual_derivative_affine_equation_on X Y h R F P
      (fun _ ↦ Metric.ball 0 d) (fun _ ↦ Metric.isOpen_ball) hRU
      (fun p x hx ↦ hPd p x (by simpa using hx))
      (fun p x hx ↦ hRd p x (by simpa using hx))
      (fun p x hx ↦ hFd p x (by simpa using hx))
      (fun p x hx ↦ hinv p x (by simpa using hx)) (p i) i.1.2 (by simpa only [Metric.mem_ball,dist_zero_right] using (show ‖i.1.2‖<d from i.2))
  have hx : Continuous (fun z : Z ↦ (⟨z.1.base,z.1.point⟩ : Sigma X)) :=
    ParameterGraphTangentPoint.continuous_point.comp continuous_subtype_val
  have hv : Continuous (fun z : Z ↦ (⟨z.1.base,z.1.vector⟩ : Sigma X)) :=
    ParameterGraphTangentPoint.continuous_vector.comp continuous_subtype_val
  have hp : Continuous (fun z : Z ↦ z.1.base) :=
    (parameter_graph_atlas_projection_continuous e).comp hx
  have hRx : Continuous (fun z : Z ↦ (⟨h z.1.base,R z.1.base z.1.point⟩ : Sigma X)) :=
    (parameter_graph_local_joint_value_continuous e e h hh R 1 U hU hRj).comp_continuous hx
      (fun z ↦ z.2)
  have hRv : Continuous (fun z : Z ↦
      (⟨h z.1.base,fderiv ℝ (R z.1.base) z.1.point z.1.vector⟩ : Sigma X)) := by
    have hc := parameter_graph_local_jet_evaluation_continuous e e h hh R 1 1 (le_refl 1)
      U hU hRj (fun z : Z ↦ z.1.base) hp (fun z ↦ z.1.point) hx (fun z ↦ z.2)
      (fun z _ ↦ z.1.vector) (fun _ ↦ hv)
    simpa only [iteratedFDeriv_one_apply] using hc
  let ρ : Z → Z := fun z ↦ ⟨⟨h z.1.base,R z.1.base z.1.point,
    fderiv ℝ (R z.1.base) z.1.point z.1.vector⟩,(R' (a z)).2⟩
  have hρ : Continuous ρ := (ParameterGraphTangentPoint.continuous_mk
    (fun z : Z ↦ h z.1.base) (fun z ↦ R z.1.base z.1.point)
    (fun z ↦ fderiv ℝ (R z.1.base) z.1.point z.1.vector) hRx hRv).subtype_mk _
  have hnext : Continuous (fun z : Z ↦
      (⟨h z.1.base,P (h z.1.base) (R z.1.base z.1.point)⟩ : Sigma Y)) :=
    hPc.comp_continuous hRx (fun z ↦ (R' (a z)).2)
  have hnext' : Continuous (fun z : Z ↦
      (⟨z.1.base,P (h z.1.base) (R z.1.base z.1.point)⟩ : Sigma (fun p ↦ Y (h p)))) :=
    (ParameterGraphPullbackAtlas.continuous_mk_iff f h hh _ _).mpr ⟨hp,hnext⟩
  have hanchor : Continuous (fun z : Z ↦
      (⟨z.1.base,(z.1.point,P (h z.1.base) (R z.1.base z.1.point))⟩ :
        Sigma (fun p ↦ X p×Y (h p)))) :=
    ParameterGraphProductAtlas.continuous_mk _ _ _ hx hnext'
  have heval (v : ∀z : Z,X z.1.base×Y (h z.1.base))
      (hv : Continuous (fun z ↦ (⟨z.1.base,v z⟩ : Sigma (fun p ↦ X p×Y (h p))))) :
      Continuous (fun z ↦ (⟨z.1.base,J (a z) (v z)⟩ : Sigma Y)) := by
    have hc := parameter_graph_local_jet_evaluation_continuous
      (ParameterGraphProductAtlas.atlas e fh) f id continuous_id F 1 1 (le_refl 1)
      W hW hF (fun z : Z ↦ z.1.base) hp
      (fun z ↦ (z.1.point,P (h z.1.base) (R z.1.base z.1.point))) hanchor
      (fun z ↦ hrect _ _ _ z.2.le ((hRP _ _ z.2).trans hM.le))
      (fun z _ ↦ v z) (fun _ ↦ hv)
    simpa only [iteratedFDeriv_one_apply, J, a, p, id_eq] using hc
  apply parameter_graph_affine_derivative_evaluation_continuous_of_return X Y f
    p R' H V W' C q c hqc hHb hVb hWb a hp (fun z ↦ z.1.vector)
    (e.continuous_norm.comp hv) ρ hρ (fun _ _ ↦ rfl) _ _ D
    ⟨(B:ℝ)/(1-(q:ℝ)*c),fun i ↦ hDb (p i) i.1.2 i.2⟩ hDi
  · exact heval (fun z ↦ (z.1.vector,0)) (ParameterGraphProductAtlas.continuous_mk _ _ _
      hv (parameter_graph_atlas_zero_continuous fh _ hp))
  · intro u hu
    have hu' : Continuous (fun z : Z ↦
        (⟨z.1.base,u z⟩ : Sigma (fun p ↦ Y (h p)))) :=
      (ParameterGraphPullbackAtlas.continuous_mk_iff f h hh _ _).mpr ⟨hp,hu⟩
    exact heval (fun z ↦ (0,u z)) (ParameterGraphProductAtlas.continuous_mk _ _ _
      (parameter_graph_atlas_zero_continuous e _ hp) hu')

end HolomorphicAnosov


