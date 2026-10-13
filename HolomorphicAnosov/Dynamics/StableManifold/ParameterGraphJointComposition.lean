import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalFiberRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetNorm
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointJetCriterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.FiniteSpatialJetCompositionContinuous
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff BigOperators
namespace HolomorphicAnosov

/-- Finite sums of continuous original bundle sections are continuous. -/
theorem parameter_graph_atlas_sum_continuous
    {A Z I : Type*} [TopologicalSpace A] [TopologicalSpace Z]
    {E : A → Type*} [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)] (e : FiniteRankNormedAtlas (E := E))
    (b : Z → A) (hb : Continuous b) (s : Finset I) (u : I → ∀ z, E (b z))
    (hu : ∀ i ∈ s, Continuous (fun z ↦ (⟨b z,u i z⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨b z,∑ i ∈ s, u i z⟩ : Sigma E)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using parameter_graph_atlas_zero_continuous e b hb
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact parameter_graph_atlas_add_continuous e b hb (u i) (fun z ↦ ∑ j ∈ s,u j z)
      (hu i (Finset.mem_insert_self _ _)) (ih (fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)))

/-- HPS pp.32–36,62: original local jets of a composite have continuous total
evaluation. The finite Faà di Bruno formula is a finite sum over ordered
partitions. Each inner jet evaluation is continuous; these give the vector
arguments for a continuous outer jet evaluation. Original bundle addition
makes their finite sum continuous. No derivative of a base map is taken. -/
theorem parameter_graph_local_composition_jet_evaluation
    {A B C Z : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace Z]
    {E : A → Type*} {F : B → Type*} {H : C → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [∀ p, NormedAddCommGroup (H p)] [∀ p, NormedSpace ℝ (H p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma H)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h : FiniteRankNormedAtlas (E := H)) (b : A → B) (hb : Continuous b)
    (c : B → C) (hc : Continuous c) (g : ∀ p, E p → F (b p)) (k : ∀ q, F q → H (c q))
    (r m : ℕ) (hm : m ≤ r) (U : Set (Sigma E)) (V : Set (Sigma F))
    (hU : IsOpen U) (hV : IsOpen V)
    (hg : JointFiberContDiffOn e f b r U g) (hk : JointFiberContDiffOn f h c r V k)
    (hmap : ∀ z ∈ U, (⟨b z.1,g z.1 z.2⟩ : Sigma F) ∈ V)
    (p : Z → A) (hp : Continuous p) (x : ∀ z, E (p z))
    (hx : Continuous (fun z ↦ (⟨p z,x z⟩ : Sigma E)))
    (hxU : ∀ z, (⟨p z,x z⟩ : Sigma E) ∈ U)
    (v : ∀ z, Fin m → E (p z))
    (hv : ∀ i, Continuous (fun z ↦ (⟨p z,v z i⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨c (b (p z)),
      iteratedFDeriv ℝ m (fun y ↦ k (b (p z)) (g (p z) y)) (x z) (v z)⟩ : Sigma H)) := by
  have hxg : Continuous (fun z ↦ (⟨b (p z),g (p z) (x z)⟩ : Sigma F)) := by
    have ht := parameter_graph_local_jet_evaluation_continuous e f b hb g r 0 (Nat.zero_le r)
      U hU hg p hp x hx hxU (fun _ ↦ (0 : Fin 0 → _)) (fun i ↦ Fin.elim0 i)
    simpa only [iteratedFDeriv_zero_apply] using ht
  let term (d : OrderedFinpartition m) (z : Z) : H (c (b (p z))) :=
    iteratedFDeriv ℝ d.length (k (b (p z))) (g (p z) (x z))
      (fun j ↦ iteratedFDeriv ℝ (d.partSize j) (g (p z)) (x z) (v z ∘ d.emb j))
  have hterm (d : OrderedFinpartition m) :
      Continuous (fun z ↦ (⟨c (b (p z)),term d z⟩ : Sigma H)) := by
    apply parameter_graph_local_jet_evaluation_continuous f h c hc k r d.length
      (d.length_le.trans hm) V hV hk (fun z ↦ b (p z)) (hb.comp hp)
      (fun z ↦ g (p z) (x z)) hxg (fun z ↦ hmap _ (hxU z))
    intro j
    exact parameter_graph_local_jet_evaluation_continuous e f b hb g r (d.partSize j)
      ((d.partSize_le j).trans hm) U hU hg p hp x hx hxU
      (fun z ↦ v z ∘ d.emb j) (fun a ↦ hv (d.emb j a))
  have hsum := parameter_graph_atlas_sum_continuous h (fun z ↦ c (b (p z)))
    (hc.comp (hb.comp hp)) Finset.univ term (fun d _ ↦ hterm d)
  apply hsum.congr
  intro z
  congr 1
  have hs : IsOpen {y : E (p z) | (⟨p z,y⟩ : Sigma E) ∈ U} :=
    hU.preimage (e.fibre_inducing (p z)).continuous
  have ht : IsOpen {y : F (b (p z)) | (⟨b (p z),y⟩ : Sigma F) ∈ V} :=
    hV.preimage (f.fibre_inducing (b (p z))).continuous
  have hg' : ContDiffOn ℝ r (g (p z)) {y | (⟨p z,y⟩ : Sigma E) ∈ U} :=
    fun y hy ↦ (hg.1 _ hy).contDiffWithinAt
  have hk' : ContDiffOn ℝ r (k (b (p z))) {y | (⟨b (p z),y⟩ : Sigma F) ∈ V} :=
    fun y hy ↦ (hk.1 _ hy).contDiffWithinAt
  have hformula := iteratedFDeriv_comp_of_contDiffOn_finite hs ht m
    (hg'.of_le (by exact_mod_cast hm)) (hk'.of_le (by exact_mod_cast hm))
    (fun y hy ↦ hmap ⟨p z,y⟩ hy) (hxU z)
  have heval := congrArg (fun L ↦ L (v z)) hformula
  simpa only [FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries,term,Function.comp_def] using heval.symm

/-- HPS pp.32–36,62: composition preserves joint fibre C^r regularity on
original open domains. Fibre germs compose by the ordinary chain rule.
Continuous original jet evaluation follows from the finite composition formula;
the local jet criterion recovers exactly the supplied chart definition. -/
theorem parameter_graph_local_joint_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {E : A → Type*} {F : B → Type*} {H : C → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [∀ p, NormedAddCommGroup (H p)] [∀ p, NormedSpace ℝ (H p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma H)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h : FiniteRankNormedAtlas (E := H)) (b : A → B) (hb : Continuous b)
    (c : B → C) (hc : Continuous c) (g : ∀ p, E p → F (b p)) (k : ∀ q, F q → H (c q))
    (r : ℕ) (U : Set (Sigma E)) (V : Set (Sigma F)) (hU : IsOpen U) (hV : IsOpen V)
    (hg : JointFiberContDiffOn e f b r U g) (hk : JointFiberContDiffOn f h c r V k)
    (hmap : ∀ z ∈ U, (⟨b z.1,g z.1 z.2⟩ : Sigma F) ∈ V) :
    JointFiberContDiffOn e h (c ∘ b) r U (fun p x ↦ k (b p) (g p x)) := by
  apply parameter_graph_local_joint_jet_criterion
  · intro z hz
    exact ContDiffAt.comp z.2 (hk.1 _ (hmap z hz)) (hg.1 z hz)
  · intro i m hm
    rw [continuousOn_iff_continuous_domRestrict]
    let S : Set ((e.chart i).baseSet ×
        (FiniteFiberModel (e.rank i) × (Fin m → FiniteFiberModel (e.rank i)))) :=
      {z | (⟨z.1.val,(e.coordinates i z.1.val z.1.property).symm z.2.1⟩ : Sigma E) ∈ U}
    let p : S → A := fun z ↦ z.1.1.1
    let x (z : S) := (e.coordinates i z.1.1.1 z.1.1.2).symm z.1.2.1
    let v (z : S) (a : Fin m) := (e.coordinates i z.1.1.1 z.1.1.2).symm (z.1.2.2 a)
    have hp : Continuous p := continuous_subtype_val.comp continuous_subtype_val.fst
    have hx : Continuous (fun z : S ↦ (⟨p z,x z⟩ : Sigma E)) :=
      (atlas_frame_continuous e i).comp
        (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.fst)
    have hv (a : Fin m) : Continuous (fun z : S ↦ (⟨p z,v z a⟩ : Sigma E)) :=
      (atlas_frame_continuous e i).comp (continuous_subtype_val.fst.prodMk
        ((continuous_apply a).comp continuous_subtype_val.snd.snd))
    exact parameter_graph_local_composition_jet_evaluation e f h b hb c hc g k
      r m hm U V hU hV hg hk hmap p hp x hx (fun z ↦ z.2) v hv

/-- The global joint composition rule is the local rule on the whole original
total spaces. No compactness or base differentiability is needed. -/
theorem parameter_graph_joint_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {E : A → Type*} {F : B → Type*} {H : C → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [∀ p, NormedAddCommGroup (H p)] [∀ p, NormedSpace ℝ (H p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma H)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h : FiniteRankNormedAtlas (E := H)) (b : A → B) (hb : Continuous b)
    (c : B → C) (hc : Continuous c) (g : ∀ p, E p → F (b p)) (k : ∀ q, F q → H (c q))
    (r : ℕ) (hg : JointFiberContDiff e f b r g) (hk : JointFiberContDiff f h c r k) :
    JointFiberContDiff e h (c ∘ b) r (fun p x ↦ k (b p) (g p x)) := by
  apply jointFiberContDiffOn_univ_iff.mp
  exact parameter_graph_local_joint_comp e f h b hb c hc g k r univ univ isOpen_univ isOpen_univ
    (jointFiberContDiffOn_univ_iff.mpr hg) (jointFiberContDiffOn_univ_iff.mpr hk) (fun _ _ ↦ mem_univ _)

end HolomorphicAnosov
