import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointContinuity

noncomputable section
open Set Filter
open scoped _root_.Topology ContDiff
namespace HolomorphicAnosov

/-- One exact invariant-section equation transports local joint regularity
backwards along its spatial return. The receiving section is evaluated after
the return, paired with the original source point, then inserted into the
known smooth action. All three are actual local joint composition rules. -/
theorem parameter_graph_section_regular_preimage
    {A : Type*} [TopologicalSpace A] {X Y : A→Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := X)) (f : FiniteRankNormedAtlas (E := Y))
    (h : A→A) (hh : Continuous h) (R : ∀p,X p→X (h p))
    (F : ∀p,X p×Y (h p)→Y p) (P : ∀p,X p→Y p) (r:ℕ)
    (hR : JointFiberContDiff e e h r R)
    (hinv : ∀p x,P p x=F p (x,P (h p) (R p x)))
    (W : Set (Sigma (fun p ↦ X p×Y (h p))))
    (hW : letI := ParameterGraphPullbackAtlas.topology f h hh
      @IsOpen _ (ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))) W)
    (hF : letI := ParameterGraphPullbackAtlas.topology f h hh
      letI := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
      JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e
        (ParameterGraphPullbackAtlas.atlas f h hh)) f id r W F)
    (hgraph : ∀p x,(⟨p,(x,P (h p) (R p x))⟩ : Sigma (fun p ↦ X p×Y (h p)))∈W)
    (U : Set (Sigma X)) (hU : IsOpen U) (hP : JointFiberContDiffOn e f id r U P) :
    JointFiberContDiffOn e f id r
      {z : Sigma X | (⟨h z.1,R z.1 z.2⟩ : Sigma X)∈U} P := by
  let := ParameterGraphPullbackAtlas.topology f h hh
  let := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
  let fh := ParameterGraphPullbackAtlas.atlas f h hh
  let V : Set (Sigma X) := {z | (⟨h z.1,R z.1 z.2⟩ : Sigma X)∈U}
  have hRc : Continuous (fun z : Sigma X ↦ (⟨h z.1,R z.1 z.2⟩ : Sigma X)) :=
    continuousOn_univ.mp (parameter_graph_local_joint_value_continuous e e h hh R r univ
      isOpen_univ (jointFiberContDiffOn_univ_iff.mpr hR))
  have hV : IsOpen V := hU.preimage hRc
  have hRl : JointFiberContDiffOn e e h r V R :=
    (jointFiberContDiffOn_univ_iff.mpr hR).mono (subset_univ V)
  have hPR : JointFiberContDiffOn e f h r V (fun p x ↦ P (h p) (R p x)) := by
    simpa only [Function.comp_def,id_eq] using parameter_graph_local_joint_comp
      e e f h hh id continuous_id R P r V U hV hU hRl hP (fun z hz ↦ hz)
  have hPR' : JointFiberContDiffOn e fh id r V (fun p x ↦ P (h p) (R p x)) :=
    (parameter_graph_local_joint_pullback_iff e f h hh r V hV _).mpr hPR
  have hi : JointFiberContDiffOn e e id r V (fun _ x ↦ x) :=
    (jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_id e r)).mono (subset_univ V)
  have hp := parameter_graph_local_joint_pair e e fh id continuous_id r V hV
    (fun _ x ↦ x) (fun p x ↦ P (h p) (R p x)) hi hPR'
  have hc := parameter_graph_local_joint_comp e (ParameterGraphProductAtlas.atlas e fh)
    f id continuous_id id continuous_id (fun p x ↦ (x,P (h p) (R p x))) F
    r V W hV hW hp hF (fun z _ ↦ hgraph z.1 z.2)
  have he : (fun p x ↦ F p (x,P (h p) (R p x))) = P :=
    funext (fun p ↦ funext (fun x ↦ (hinv p x).symm))
  change JointFiberContDiffOn e f id r V (fun p x ↦ F p (x,P (h p) (R p x))) at hc
  rw [he] at hc
  exact hc

/-- A common regular germ of an invariant section propagates to every fibre
point when the centered spatial return contracts. The inverse images of the
germ under successive returns are open and carry the same joint order by
one-step propagation. Every point belongs to one of them because its original
norm decays geometrically. Local joint regularity then glues globally.
Source: HPS, Invariant Manifolds, pp.35–36 and62. -/
theorem parameter_graph_section_local_to_global
    {A : Type*} [TopologicalSpace A] {X Y : A→Type*}
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    (e : FiniteRankNormedAtlas (E := X)) (f : FiniteRankNormedAtlas (E := Y))
    (h : A→A) (hh : Continuous h) (R : ∀p,X p→X (h p))
    (F : ∀p,X p×Y (h p)→Y p) (P : ∀p,X p→Y p) (r:ℕ)
    (hR : JointFiberContDiff e e h r R)
    (c:NNReal) (hc:(c:ℝ)<1) (hRL : ∀p,LipschitzWith c (R p)) (hzero : ∀p,R p 0=0)
    (hinv : ∀p x,P p x=F p (x,P (h p) (R p x)))
    (W : Set (Sigma (fun p ↦ X p×Y (h p))))
    (hW : letI := ParameterGraphPullbackAtlas.topology f h hh
      @IsOpen _ (ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))) W)
    (hF : letI := ParameterGraphPullbackAtlas.topology f h hh
      letI := ParameterGraphProductAtlas.topology (E := X) (F := fun p ↦ Y (h p))
      JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e
        (ParameterGraphPullbackAtlas.atlas f h hh)) f id r W F)
    (hgraph : ∀p x,(⟨p,(x,P (h p) (R p x))⟩ : Sigma (fun p ↦ X p×Y (h p)))∈W)
    (δ:ℝ) (hδ:0<δ)
    (hP : JointFiberContDiffOn e f id r {z:Sigma X | ‖z.2‖<δ} P) :
    JointFiberContDiff e f id r P := by
  let T : Sigma X→Sigma X := fun z ↦ ⟨h z.1,R z.1 z.2⟩
  have hT : Continuous T := continuousOn_univ.mp
    (parameter_graph_local_joint_value_continuous e e h hh R r univ isOpen_univ
      (jointFiberContDiffOn_univ_iff.mpr hR))
  let U : ℕ→Set (Sigma X) := fun n ↦ {z | ‖((T^[n]) z).2‖<δ}
  have hU (n:ℕ) : IsOpen (U n) :=
    isOpen_lt (e.continuous_norm.comp (hT.iterate n)) continuous_const
  have hreg (n:ℕ) : JointFiberContDiffOn e f id r (U n) P := by
    induction n with
    | zero => exact hP
    | succ n ih =>
        have hs := parameter_graph_section_regular_preimage e f h hh R F P r hR
          hinv W hW hF hgraph (U n) (hU n) ih
        have hUn : U (n+1) = {z | T z∈U n} := by
          ext z
          simp only [U,mem_ofPred_eq,Function.iterate_succ_apply]
          exact Iff.rfl
        rw [hUn]
        simpa only [id_eq] using hs
  have hnorm (z:Sigma X) : ‖(T z).2‖≤(c:ℝ)*‖z.2‖ := by
    simpa only [T,hzero,dist_zero_right] using (hRL z.1).dist_le_mul z.2 0
  have hiter (n:ℕ) (z:Sigma X) : ‖((T^[n]) z).2‖≤(c:ℝ)^n*‖z.2‖ := by
    induction n with
    | zero =>
        simp only [Function.iterate_zero_apply,pow_zero,one_mul]
        exact le_rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc
          _ ≤ (c:ℝ)*‖((T^[n]) z).2‖ := hnorm _
          _ ≤ (c:ℝ)*((c:ℝ)^n*‖z.2‖) := mul_le_mul_of_nonneg_left ih c.2
          _ = _ := by rw [pow_succ]; ring
  apply jointFiberContDiffOn_univ_iff.mp
  apply JointFiberContDiffOn.of_locally continuous_id
  intro z _
  have ht : Tendsto (fun n:ℕ ↦ (c:ℝ)^n*‖z.2‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one c.2 hc).mul_const ‖z.2‖
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  exact ⟨U n,hU n,(hiter n z).trans_lt hn,hreg n⟩

end HolomorphicAnosov
