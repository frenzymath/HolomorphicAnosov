import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm

noncomputable section
open Set Topology
open scoped ContDiff
namespace HolomorphicAnosov

/-- The tangent-section induction in HPS p.35 gains one order when the actual
derivative family has the preceding joint order. Fibrewise this is the usual
ContDiff successor criterion. For a positive-order chart jet, curry off its
last input: it is the corresponding jet of the derivative field evaluated on
that input. The genuine Hom atlas preserves evaluation continuity, so the
original jet criterion supplies all joint chart jets, including order zero
from the assumed total value continuity. -/
theorem parameter_graph_joint_of_derivative
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (g : ∀p,E p→F p) (n : ℕ)
    (hg : Continuous (fun z : Sigma E ↦ (⟨z.1,g z.1 z.2⟩ : Sigma F)))
    (hd : ∀p,Differentiable ℝ (g p))
    (hD : letI := ParameterGraphHomAtlas.topology e f
      JointFiberContDiff e (ParameterGraphHomAtlas.atlas e f)
        id n (fun p ↦ fderiv ℝ (g p))) :
    JointFiberContDiff e f id (n+1) g := by
  let := ParameterGraphHomAtlas.topology e f
  have hgc : ∀p,ContDiff ℝ (n+1) (g p) := by
    intro p
    rw [contDiff_succ_iff_fderiv]
    exact ⟨hd p,by simp,hD.1 p⟩
  apply parameter_graph_joint_jet_criterion e f id g (n+1) hgc
  intro i m hm
  let Z := (e.chart i).baseSet ×
    (FiniteFiberModel (e.rank i) × (Fin m→FiniteFiberModel (e.rank i)))
  let p : Z→A := fun z ↦ z.1.1
  let x : ∀z:Z,E (p z) := fun z ↦ (e.coordinates i z.1.1 z.1.2).symm z.2.1
  let v : ∀z:Z,Fin m→E (p z) := fun z k ↦ (e.coordinates i z.1.1 z.1.2).symm (z.2.2 k)
  have hp : Continuous p := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun z:Z ↦ (⟨p z,x z⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hv (k:Fin m) : Continuous (fun z:Z ↦ (⟨p z,v z k⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp (continuous_fst.prodMk
      ((continuous_apply k).comp (continuous_snd.comp continuous_snd)))
  change Continuous (fun z:Z ↦ (⟨p z,iteratedFDeriv ℝ m (g (p z)) (x z) (v z)⟩ : Sigma F))
  cases m with
  | zero =>
      simpa only [iteratedFDeriv_zero_apply,Function.comp_def] using hg.comp hx
  | succ m =>
      have hmc : m≤n := Nat.le_of_succ_le_succ hm
      have hJ := parameter_graph_joint_jet_evaluation_continuous e
        (ParameterGraphHomAtlas.atlas e f) id continuous_id
        (fun p ↦ fderiv ℝ (g p)) n m hmc hD p hp x hx
        (fun z ↦ Fin.init (v z)) (fun k ↦ hv k.castSucc)
      have he := ParameterGraphHomAtlas.continuous_apply e f p hp
        (fun z ↦ iteratedFDeriv ℝ m (fderiv ℝ (g (p z))) (x z) (Fin.init (v z)))
        (fun z ↦ v z (Fin.last m)) hJ (hv (Fin.last m))
      simpa only [iteratedFDeriv_succ_apply_right] using he

/-- The same successor criterion holds on an original open total-space domain.
All derivative evaluations and differentiability assertions are restricted to
that domain, which is the form used after shrinking an inward fibre disc. -/
theorem parameter_graph_local_joint_of_derivative
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (g : ∀p,E p→F p) (n : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : ContinuousOn (fun z : Sigma E ↦ (⟨z.1,g z.1 z.2⟩ : Sigma F)) U)
    (hd : ∀z∈U,DifferentiableAt ℝ (g z.1) z.2)
    (hD : letI := ParameterGraphHomAtlas.topology e f
      JointFiberContDiffOn e (ParameterGraphHomAtlas.atlas e f)
        id n U (fun p ↦ fderiv ℝ (g p))) :
    JointFiberContDiffOn e f id (n+1) U g := by
  let := ParameterGraphHomAtlas.topology e f
  have hgc : ∀z∈U,ContDiffAt ℝ (n+1) (g z.1) z.2 := by
    intro z hz
    let V := {x : E z.1 | (⟨z.1,x⟩ : Sigma E)∈U}
    have hV : IsOpen V := hU.preimage (e.fibre_inducing z.1).continuous
    have hf : ContDiffOn ℝ (n+1) (g z.1) V := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hV]
      exact ⟨fun x hx ↦ (hd ⟨z.1,x⟩ hx).differentiableWithinAt,by simp,
        fun x hx ↦ (hD.1 ⟨z.1,x⟩ hx).contDiffWithinAt⟩
    exact (hf z.2 hz).contDiffAt (hV.mem_nhds hz)
  apply parameter_graph_local_joint_jet_criterion e f id g (n+1) U hgc
  intro i m hm
  rw [continuousOn_iff_continuous_domRestrict]
  let S : Set ((e.chart i).baseSet ×
    (FiniteFiberModel (e.rank i) × (Fin m→FiniteFiberModel (e.rank i)))) :=
    {z | (⟨z.1.1,(e.coordinates i z.1.1 z.1.2).symm z.2.1⟩ : Sigma E)∈U}
  let p : S→A := fun z ↦ z.1.1.1
  let x : ∀z:S,E (p z) := fun z ↦ (e.coordinates i z.1.1.1 z.1.1.2).symm z.1.2.1
  let v : ∀z:S,Fin m→E (p z) := fun z k ↦ (e.coordinates i z.1.1.1 z.1.1.2).symm (z.1.2.2 k)
  have hp : Continuous p := continuous_subtype_val.comp continuous_subtype_val.fst
  have hx : Continuous (fun z:S ↦ (⟨p z,x z⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp
      (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.fst)
  have hxU (z:S) : (⟨p z,x z⟩ : Sigma E)∈U := z.2
  have hv (k:Fin m) : Continuous (fun z:S ↦ (⟨p z,v z k⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp (continuous_subtype_val.fst.prodMk
      ((continuous_apply k).comp continuous_subtype_val.snd.snd))
  change Continuous (fun z:S ↦ (⟨p z,iteratedFDeriv ℝ m (g (p z)) (x z) (v z)⟩ : Sigma F))
  cases m with
  | zero =>
      simpa only [iteratedFDeriv_zero_apply,Function.comp_def] using hg.comp_continuous hx hxU
  | succ m =>
      have hmc : m≤n := Nat.le_of_succ_le_succ hm
      have hJ := parameter_graph_local_jet_evaluation_continuous e
        (ParameterGraphHomAtlas.atlas e f) id continuous_id
        (fun p ↦ fderiv ℝ (g p)) n m hmc U hU hD p hp x hx hxU
        (fun z ↦ Fin.init (v z)) (fun k ↦ hv k.castSucc)
      have he := ParameterGraphHomAtlas.continuous_apply e f p hp
        (fun z ↦ iteratedFDeriv ℝ m (fderiv ℝ (g (p z))) (x z) (Fin.init (v z)))
        (fun z ↦ v z (Fin.last m)) hJ (hv (Fin.last m))
      simpa only [iteratedFDeriv_succ_apply_right] using he

/-- Extracting the derivative loses exactly one joint fibre order. The Hom
coordinates are justified by evaluation: append one inverse-frame vector to
the original jet tuple and use the successor identity for iterated derivatives. -/
theorem parameter_graph_local_joint_derivative
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (g : ∀p,E p→F p) (n : ℕ) (U : Set (Sigma E)) (hU : IsOpen U)
    (hg : JointFiberContDiffOn e f id (n+1) U g) :
    letI := ParameterGraphHomAtlas.topology e f
    JointFiberContDiffOn e (ParameterGraphHomAtlas.atlas e f)
      id n U (fun p ↦ fderiv ℝ (g p)) := by
  let := ParameterGraphHomAtlas.topology e f
  apply parameter_graph_local_joint_jet_criterion e (ParameterGraphHomAtlas.atlas e f)
    id (fun p ↦ fderiv ℝ (g p)) n U
  · intro z hz
    exact ContDiffAt.fderiv_right_succ (by simpa using hg.1 z hz)
  intro i m hm
  rw [continuousOn_iff_continuous_domRestrict]
  let S : Set ((e.chart i).baseSet ×
    (FiniteFiberModel (e.rank i) × (Fin m→FiniteFiberModel (e.rank i)))) :=
    {z | (⟨z.1.1,(e.coordinates i z.1.1 z.1.2).symm z.2.1⟩ : Sigma E)∈U}
  let p : S→A := fun z ↦ z.1.1.1
  let x : ∀z:S,E (p z) := fun z ↦ (e.coordinates i z.1.1.1 z.1.1.2).symm z.1.2.1
  let v : ∀z:S,Fin m→E (p z) := fun z k ↦ (e.coordinates i z.1.1.1 z.1.1.2).symm (z.1.2.2 k)
  have hp : Continuous p := continuous_subtype_val.comp continuous_subtype_val.fst
  have hx : Continuous (fun z:S ↦ (⟨p z,x z⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp
      (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.fst)
  have hxU (z:S) : (⟨p z,x z⟩ : Sigma E)∈U := z.2
  have hv (k:Fin m) : Continuous (fun z:S ↦ (⟨p z,v z k⟩ : Sigma E)) :=
    (atlas_frame_continuous e i).comp (continuous_subtype_val.fst.prodMk
      ((continuous_apply k).comp continuous_subtype_val.snd.snd))
  change Continuous (fun z:S ↦ (⟨p z,
    iteratedFDeriv ℝ m (fderiv ℝ (g (p z))) (x z) (v z)⟩ :
      Sigma (fun p ↦ E p →L[ℝ] F p)))
  apply ParameterGraphHomAtlas.continuous_of_evaluation e f p hp
  intro k w
  let T := {z:S // p z∈(e.chart k).baseSet}
  let w' : ∀z:T,E (p z.1) := fun z ↦ (e.coordinates k (p z.1) z.2).symm w
  have hw : Continuous (fun z:T ↦ (⟨p z.1,w' z⟩ : Sigma E)) :=
    (atlas_frame_continuous e k).comp
      (((hp.comp continuous_subtype_val).subtype_mk (fun z:T ↦ z.2)).prodMk continuous_const)
  have hv' (j:Fin (m+1)) : Continuous (fun z:T ↦
      (⟨p z.1,Fin.snoc (α := fun _ ↦ E (p z.1)) (v z.1) (w' z) j⟩ : Sigma E)) := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simpa only [Fin.snoc_last] using hw
    · simpa only [Fin.snoc_castSucc,Function.comp_def] using (hv j).comp (continuous_subtype_val : Continuous (Subtype.val : T→S))
  have he := parameter_graph_local_jet_evaluation_continuous e f id continuous_id
    g (n+1) (m+1) (Nat.succ_le_succ hm) U hU hg
    (fun z:T ↦ p z.1) (hp.comp continuous_subtype_val)
    (fun z:T ↦ x z.1) (hx.comp continuous_subtype_val) (fun z ↦ hxU z.1)
    (fun z:T ↦ Fin.snoc (α := fun _ ↦ E (p z.1)) (v z.1) (w' z)) hv'
  simpa only [iteratedFDeriv_succ_apply_right,Fin.init_snoc,Fin.snoc_last, id_eq] using he

end HolomorphicAnosov
