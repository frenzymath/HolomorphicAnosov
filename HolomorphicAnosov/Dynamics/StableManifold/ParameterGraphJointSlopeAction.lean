import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphHomAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointComposition
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointProductPullback
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphProductAtlas
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointBilinearOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointInverse
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphLocalJointContinuity

noncomputable section
open Set
open scoped _root_.Topology ContDiff
namespace HolomorphicAnosov

/-- Negation preserves local joint regularity by composition with the original
negative identity family, whose value evaluation is continuous. -/
theorem parameter_graph_local_joint_neg
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (r : ℕ) (Ω : Set (Sigma E)) (hΩ : IsOpen Ω) (g : ∀p,E p→F p)
    (hg : JointFiberContDiffOn e f id r Ω g) :
    JointFiberContDiffOn e f id r Ω (fun p z ↦ -g p z) := by
  have hn : JointFiberContDiff f f id r (fun _ v ↦ -v) := by
    apply parameter_graph_joint_linear f f id continuous_id
      (fun p ↦ -(ContinuousLinearMap.id ℝ (F p))) _ r
    have hc := parameter_graph_atlas_sub_continuous f (fun z : Sigma F ↦ z.1)
      (parameter_graph_atlas_projection_continuous f) (fun _ ↦ 0) (fun z ↦ z.2)
      (parameter_graph_atlas_zero_continuous f _ (parameter_graph_atlas_projection_continuous f))
      continuous_id
    simpa using hc
  exact parameter_graph_local_joint_comp e f f id continuous_id id continuous_id g
    (fun _ v ↦ -v) r Ω univ hΩ isOpen_univ hg (jointFiberContDiffOn_univ_iff.mpr hn)
    (fun _ _ ↦ mem_univ _)

/-- Subtraction preserves local joint regularity in the original atlas. -/
theorem parameter_graph_local_joint_sub
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (r : ℕ) (Ω : Set (Sigma E)) (hΩ : IsOpen Ω) (g k : ∀p,E p→F p)
    (hg : JointFiberContDiffOn e f id r Ω g) (hk : JointFiberContDiffOn e f id r Ω k) :
    JointFiberContDiffOn e f id r Ω (fun p z ↦ g p z-k p z) := by
  simpa only [sub_eq_add_neg] using parameter_graph_local_joint_add e f r Ω hΩ g
    (fun p z ↦ -k p z) hg (parameter_graph_local_joint_neg e f r Ω hΩ k hk)

/-- A locally jointly regular original operator field has a locally jointly
regular inverse wherever it is invertible. The genuine Hom invertible locus
is open; ordinary local composition with native inversion gives the result. -/
theorem parameter_graph_local_joint_clm_inverse
    {A : Type*} [TopologicalSpace A] {Z E F : A → Type*}
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (z : FiniteRankNormedAtlas (E := Z)) (e : FiniteRankNormedAtlas (E := E))
    (f : FiniteRankNormedAtlas (E := F)) (r : ℕ) (Ω : Set (Sigma Z)) (hΩ : IsOpen Ω)
    (J : ∀p,Z p→E p→L[ℝ] F p)
    (hJ : letI := ParameterGraphHomAtlas.topology e f
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas e f) id r Ω J) :
    letI := ParameterGraphHomAtlas.topology f e
    let Ω' := {w : Sigma Z | w∈Ω ∧ (J w.1 w.2).IsInvertible}
    IsOpen Ω' ∧ JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas f e) id r Ω'
      (fun p w ↦ (J p w).inverse) := by
  let := ParameterGraphHomAtlas.topology e f
  let := ParameterGraphHomAtlas.topology f e
  let Ω' := {w : Sigma Z | w∈Ω ∧ (J w.1 w.2).IsInvertible}
  have ho : IsOpen Ω' :=
    (parameter_graph_local_joint_value_continuous z (ParameterGraphHomAtlas.atlas e f)
      id continuous_id J r Ω hΩ hJ).isOpen_inter_preimage hΩ
      (ParameterGraphHomAtlas.isOpen_invertible e f)
  refine ⟨ho,?_⟩
  exact parameter_graph_local_joint_comp z (ParameterGraphHomAtlas.atlas e f)
    (ParameterGraphHomAtlas.atlas f e) id continuous_id id continuous_id J
    (fun _ ↦ ContinuousLinearMap.inverse) r Ω'
    {w : Sigma (fun p ↦ E p→L[ℝ] F p) | w.2.IsInvertible}
    ho (ParameterGraphHomAtlas.isOpen_invertible e f) (hJ.mono (fun _ hw ↦ hw.1))
    (ParameterGraphHomAtlas.joint_inverse e f r) (fun _ hw ↦ hw.2)

/-- Pull a known local fibre map back by the first native product projection. -/
theorem parameter_graph_local_joint_comp_fst
    {A : Type*} [TopologicalSpace A] {E F K : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,NormedAddCommGroup (K p)] [∀p,NormedSpace ℝ (K p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)] [TopologicalSpace (Sigma K)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (k : FiniteRankNormedAtlas (E := K)) (r : ℕ) (Ω : Set (Sigma E)) (hΩ : IsOpen Ω)
    (g : ∀p,E p→K p) (hg : JointFiberContDiffOn e k id r Ω g) :
    letI := ParameterGraphProductAtlas.topology (E := E) (F := F)
    JointFiberContDiffOn (ParameterGraphProductAtlas.atlas e f) k id r
      {z : Sigma (fun p ↦ E p×F p) | (⟨z.1,z.2.1⟩ : Sigma E)∈Ω}
      (fun p z ↦ g p z.1) := by
  let := ParameterGraphProductAtlas.topology (E := E) (F := F)
  exact parameter_graph_local_joint_comp (ParameterGraphProductAtlas.atlas e f) e k
    id continuous_id id continuous_id (fun _ z ↦ z.1) g r _ Ω
    (hΩ.preimage ParameterGraphProductAtlas.fst_continuous) hΩ
    ((jointFiberContDiffOn_univ_iff.mpr (parameter_graph_joint_native_fst e f r)).mono
      (fun _ _ ↦ mem_univ _)) hg (fun _ hz ↦ hz)

/-- The rational preimage slope action is locally jointly C^r for original
operator families on the open locus where its horizontal operator is invertible.
All operations occur in genuine Hom atlases and retain the original norms. -/
theorem parameter_graph_local_joint_preimage_rational
    {A : Type*} [TopologicalSpace A] {Z X Y U V : A → Type*}
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [∀p,NormedAddCommGroup (U p)] [∀p,NormedSpace ℝ (U p)]
    [∀p,NormedAddCommGroup (V p)] [∀p,NormedSpace ℝ (V p)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma U)] [TopologicalSpace (Sigma V)]
    (z : FiniteRankNormedAtlas (E := Z)) (x : FiniteRankNormedAtlas (E := X))
    (y : FiniteRankNormedAtlas (E := Y)) (u : FiniteRankNormedAtlas (E := U))
    (v : FiniteRankNormedAtlas (E := V)) (r : ℕ) (Ω : Set (Sigma Z)) (hΩ : IsOpen Ω)
    (AA : ∀p,Z p→X p→L[ℝ] U p) (BB : ∀p,Z p→Y p→L[ℝ] U p)
    (CC : ∀p,Z p→X p→L[ℝ] V p) (DD : ∀p,Z p→Y p→L[ℝ] V p)
    (P : ∀p,Z p→V p→L[ℝ] U p)
    (hAA : letI := ParameterGraphHomAtlas.topology x u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x u) id r Ω AA)
    (hBB : letI := ParameterGraphHomAtlas.topology y u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y u) id r Ω BB)
    (hCC : letI := ParameterGraphHomAtlas.topology x v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x v) id r Ω CC)
    (hDD : letI := ParameterGraphHomAtlas.topology y v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y v) id r Ω DD)
    (hP : letI := ParameterGraphHomAtlas.topology v u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas v u) id r Ω P)
    : letI := ParameterGraphHomAtlas.topology y x
    let Ω' := {w : Sigma Z | w∈Ω ∧ (AA w.1 w.2-(P w.1 w.2).comp (CC w.1 w.2)).IsInvertible}
    IsOpen Ω' ∧ JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y x) id r Ω'
      (fun p w ↦ (AA p w-(P p w).comp (CC p w)).inverse.comp ((P p w).comp (DD p w)-BB p w)) := by
  let := ParameterGraphHomAtlas.topology x u
  let := ParameterGraphHomAtlas.topology y u
  let := ParameterGraphHomAtlas.topology x v
  let := ParameterGraphHomAtlas.topology y v
  let := ParameterGraphHomAtlas.topology v u
  let := ParameterGraphHomAtlas.topology u x
  let := ParameterGraphHomAtlas.topology y x
  let J (p : A) (w : Z p) := AA p w-(P p w).comp (CC p w)
  let N (p : A) (w : Z p) := (P p w).comp (DD p w)-BB p w
  have hJ : JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x u) id r Ω J :=
    parameter_graph_local_joint_sub z (ParameterGraphHomAtlas.atlas x u) r Ω hΩ AA
      (fun p w ↦ (P p w).comp (CC p w)) hAA
      (parameter_graph_local_joint_clm_comp z x v u r Ω hΩ P CC hP hCC)
  have hN : JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y u) id r Ω N :=
    parameter_graph_local_joint_sub z (ParameterGraphHomAtlas.atlas y u) r Ω hΩ
      (fun p w ↦ (P p w).comp (DD p w)) BB
      (parameter_graph_local_joint_clm_comp z y v u r Ω hΩ P DD hP hDD) hBB
  obtain ⟨ho,hi⟩ := parameter_graph_local_joint_clm_inverse z x u r Ω hΩ J hJ
  refine ⟨ho,?_⟩
  exact parameter_graph_local_joint_clm_comp z y u x r _ ho
    (fun p w ↦ (J p w).inverse) N hi (hN.mono (fun _ hw ↦ hw.1))

/-- The rational image slope action is locally jointly C^r for original
operator families on the open locus where its horizontal operator is invertible.
All operations occur in genuine Hom atlases and retain the original norms. -/
theorem parameter_graph_local_joint_image_rational
    {A : Type*} [TopologicalSpace A] {Z X Y U V : A → Type*}
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [∀p,NormedAddCommGroup (U p)] [∀p,NormedSpace ℝ (U p)]
    [∀p,NormedAddCommGroup (V p)] [∀p,NormedSpace ℝ (V p)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma U)] [TopologicalSpace (Sigma V)]
    (z : FiniteRankNormedAtlas (E := Z)) (x : FiniteRankNormedAtlas (E := X))
    (y : FiniteRankNormedAtlas (E := Y)) (u : FiniteRankNormedAtlas (E := U))
    (v : FiniteRankNormedAtlas (E := V)) (r : ℕ) (Ω : Set (Sigma Z)) (hΩ : IsOpen Ω)
    (AA : ∀p,Z p→X p→L[ℝ] U p) (BB : ∀p,Z p→Y p→L[ℝ] U p)
    (CC : ∀p,Z p→X p→L[ℝ] V p) (DD : ∀p,Z p→Y p→L[ℝ] V p)
    (P : ∀p,Z p→X p→L[ℝ] Y p)
    (hAA : letI := ParameterGraphHomAtlas.topology x u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x u) id r Ω AA)
    (hBB : letI := ParameterGraphHomAtlas.topology y u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y u) id r Ω BB)
    (hCC : letI := ParameterGraphHomAtlas.topology x v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x v) id r Ω CC)
    (hDD : letI := ParameterGraphHomAtlas.topology y v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y v) id r Ω DD)
    (hP : letI := ParameterGraphHomAtlas.topology x y
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x y) id r Ω P)
    : letI := ParameterGraphHomAtlas.topology u v
    let Ω' := {w : Sigma Z | w∈Ω ∧ (AA w.1 w.2+(BB w.1 w.2).comp (P w.1 w.2)).IsInvertible}
    IsOpen Ω' ∧ JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas u v) id r Ω'
      (fun p w ↦ (CC p w+(DD p w).comp (P p w)).comp (AA p w+(BB p w).comp (P p w)).inverse) := by
  let := ParameterGraphHomAtlas.topology x u
  let := ParameterGraphHomAtlas.topology y u
  let := ParameterGraphHomAtlas.topology x v
  let := ParameterGraphHomAtlas.topology y v
  let := ParameterGraphHomAtlas.topology x y
  let := ParameterGraphHomAtlas.topology u x
  let := ParameterGraphHomAtlas.topology u v
  let J (p : A) (w : Z p) := AA p w+(BB p w).comp (P p w)
  let N (p : A) (w : Z p) := CC p w+(DD p w).comp (P p w)
  have hJ : JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x u) id r Ω J :=
    parameter_graph_local_joint_add z (ParameterGraphHomAtlas.atlas x u) r Ω hΩ AA
      (fun p w ↦ (BB p w).comp (P p w)) hAA
      (parameter_graph_local_joint_clm_comp z x y u r Ω hΩ BB P hBB hP)
  have hN : JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x v) id r Ω N :=
    parameter_graph_local_joint_add z (ParameterGraphHomAtlas.atlas x v) r Ω hΩ CC
      (fun p w ↦ (DD p w).comp (P p w)) hCC
      (parameter_graph_local_joint_clm_comp z x y v r Ω hΩ DD P hDD hP)
  obtain ⟨ho,hi⟩ := parameter_graph_local_joint_clm_inverse z x u r Ω hΩ J hJ
  refine ⟨ho,?_⟩
  exact parameter_graph_local_joint_clm_comp z u x v r _ ho
    N (fun p w ↦ (J p w).inverse) (hN.mono (fun _ hw ↦ hw.1)) hi

/-- The actual preimage rational slope action, with the slope as an
independent variable, is jointly C^r on its open original invertible domain.
Anchor blocks are pulled back by the first product projection; the slope is
the native second projection. The general rational-family theorem applies. -/
theorem parameter_graph_joint_preimage_slope_action
    {A : Type*} [TopologicalSpace A] {Z X Y U V : A → Type*}
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [∀p,NormedAddCommGroup (U p)] [∀p,NormedSpace ℝ (U p)]
    [∀p,NormedAddCommGroup (V p)] [∀p,NormedSpace ℝ (V p)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma U)] [TopologicalSpace (Sigma V)]
    (z : FiniteRankNormedAtlas (E := Z)) (x : FiniteRankNormedAtlas (E := X))
    (y : FiniteRankNormedAtlas (E := Y)) (u : FiniteRankNormedAtlas (E := U))
    (v : FiniteRankNormedAtlas (E := V)) (r : ℕ) (Ω : Set (Sigma Z)) (hΩ : IsOpen Ω)
    (AA : ∀p,Z p→X p→L[ℝ] U p) (BB : ∀p,Z p→Y p→L[ℝ] U p)
    (CC : ∀p,Z p→X p→L[ℝ] V p) (DD : ∀p,Z p→Y p→L[ℝ] V p)
    (hAA : letI := ParameterGraphHomAtlas.topology x u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x u) id r Ω AA)
    (hBB : letI := ParameterGraphHomAtlas.topology y u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y u) id r Ω BB)
    (hCC : letI := ParameterGraphHomAtlas.topology x v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x v) id r Ω CC)
    (hDD : letI := ParameterGraphHomAtlas.topology y v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y v) id r Ω DD)
    : letI := ParameterGraphHomAtlas.topology v u
    letI := ParameterGraphHomAtlas.topology y x
    letI := ParameterGraphProductAtlas.topology (E := Z) (F := fun p ↦ V p→L[ℝ] U p)
    let Ω' := {w : Sigma (fun p ↦ Z p×(V p→L[ℝ] U p)) |
      (⟨w.1,w.2.1⟩ : Sigma Z)∈Ω ∧ (AA w.1 w.2.1-w.2.2.comp (CC w.1 w.2.1)).IsInvertible}
    IsOpen Ω' ∧ JointFiberContDiffOn
      (ParameterGraphProductAtlas.atlas z (ParameterGraphHomAtlas.atlas v u))
      (ParameterGraphHomAtlas.atlas y x) id r Ω'
      (fun p w ↦ (AA p w.1-w.2.comp (CC p w.1)).inverse.comp (w.2.comp (DD p w.1)-BB p w.1)) := by
  let := ParameterGraphHomAtlas.topology x u
  let := ParameterGraphHomAtlas.topology y u
  let := ParameterGraphHomAtlas.topology x v
  let := ParameterGraphHomAtlas.topology y v
  let := ParameterGraphHomAtlas.topology v u
  let := ParameterGraphHomAtlas.topology y x
  let := ParameterGraphProductAtlas.topology (E := Z) (F := fun p ↦ V p→L[ℝ] U p)
  let z' := ParameterGraphProductAtlas.atlas z (ParameterGraphHomAtlas.atlas v u)
  let Ω₀ : Set (Sigma (fun p ↦ Z p×(V p→L[ℝ] U p))) :=
    {w | (⟨w.1,w.2.1⟩ : Sigma Z)∈Ω}
  have ho : IsOpen Ω₀ := hΩ.preimage ParameterGraphProductAtlas.fst_continuous
  exact parameter_graph_local_joint_preimage_rational z' x y u v r Ω₀ ho
    (fun p w ↦ AA p w.1) (fun p w ↦ BB p w.1)
    (fun p w ↦ CC p w.1) (fun p w ↦ DD p w.1) (fun _ w ↦ w.2)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas v u)
      (ParameterGraphHomAtlas.atlas x u) r Ω hΩ AA hAA)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas v u)
      (ParameterGraphHomAtlas.atlas y u) r Ω hΩ BB hBB)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas v u)
      (ParameterGraphHomAtlas.atlas x v) r Ω hΩ CC hCC)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas v u)
      (ParameterGraphHomAtlas.atlas y v) r Ω hΩ DD hDD)
    ((jointFiberContDiffOn_univ_iff.mpr
      (parameter_graph_joint_native_snd z (ParameterGraphHomAtlas.atlas v u) r)).mono
      (fun _ _ ↦ mem_univ _))

/-- The actual image rational slope action, with the slope as an
independent variable, is jointly C^r on its open original invertible domain.
Anchor blocks are pulled back by the first product projection; the slope is
the native second projection. The general rational-family theorem applies. -/
theorem parameter_graph_joint_image_slope_action
    {A : Type*} [TopologicalSpace A] {Z X Y U V : A → Type*}
    [∀p,NormedAddCommGroup (Z p)] [∀p,NormedSpace ℝ (Z p)]
    [∀p,NormedAddCommGroup (X p)] [∀p,NormedSpace ℝ (X p)]
    [∀p,NormedAddCommGroup (Y p)] [∀p,NormedSpace ℝ (Y p)]
    [∀p,NormedAddCommGroup (U p)] [∀p,NormedSpace ℝ (U p)]
    [∀p,NormedAddCommGroup (V p)] [∀p,NormedSpace ℝ (V p)]
    [TopologicalSpace (Sigma Z)] [TopologicalSpace (Sigma X)] [TopologicalSpace (Sigma Y)]
    [TopologicalSpace (Sigma U)] [TopologicalSpace (Sigma V)]
    (z : FiniteRankNormedAtlas (E := Z)) (x : FiniteRankNormedAtlas (E := X))
    (y : FiniteRankNormedAtlas (E := Y)) (u : FiniteRankNormedAtlas (E := U))
    (v : FiniteRankNormedAtlas (E := V)) (r : ℕ) (Ω : Set (Sigma Z)) (hΩ : IsOpen Ω)
    (AA : ∀p,Z p→X p→L[ℝ] U p) (BB : ∀p,Z p→Y p→L[ℝ] U p)
    (CC : ∀p,Z p→X p→L[ℝ] V p) (DD : ∀p,Z p→Y p→L[ℝ] V p)
    (hAA : letI := ParameterGraphHomAtlas.topology x u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x u) id r Ω AA)
    (hBB : letI := ParameterGraphHomAtlas.topology y u
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y u) id r Ω BB)
    (hCC : letI := ParameterGraphHomAtlas.topology x v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas x v) id r Ω CC)
    (hDD : letI := ParameterGraphHomAtlas.topology y v
      JointFiberContDiffOn z (ParameterGraphHomAtlas.atlas y v) id r Ω DD)
    : letI := ParameterGraphHomAtlas.topology x y
    letI := ParameterGraphHomAtlas.topology u v
    letI := ParameterGraphProductAtlas.topology (E := Z) (F := fun p ↦ X p→L[ℝ] Y p)
    let Ω' := {w : Sigma (fun p ↦ Z p×(X p→L[ℝ] Y p)) |
      (⟨w.1,w.2.1⟩ : Sigma Z)∈Ω ∧ (AA w.1 w.2.1+(BB w.1 w.2.1).comp w.2.2).IsInvertible}
    IsOpen Ω' ∧ JointFiberContDiffOn
      (ParameterGraphProductAtlas.atlas z (ParameterGraphHomAtlas.atlas x y))
      (ParameterGraphHomAtlas.atlas u v) id r Ω'
      (fun p w ↦ (CC p w.1+(DD p w.1).comp w.2).comp (AA p w.1+(BB p w.1).comp w.2).inverse) := by
  let := ParameterGraphHomAtlas.topology x u
  let := ParameterGraphHomAtlas.topology y u
  let := ParameterGraphHomAtlas.topology x v
  let := ParameterGraphHomAtlas.topology y v
  let := ParameterGraphHomAtlas.topology x y
  let := ParameterGraphHomAtlas.topology u v
  let := ParameterGraphProductAtlas.topology (E := Z) (F := fun p ↦ X p→L[ℝ] Y p)
  let z' := ParameterGraphProductAtlas.atlas z (ParameterGraphHomAtlas.atlas x y)
  let Ω₀ : Set (Sigma (fun p ↦ Z p×(X p→L[ℝ] Y p))) :=
    {w | (⟨w.1,w.2.1⟩ : Sigma Z)∈Ω}
  have ho : IsOpen Ω₀ := hΩ.preimage ParameterGraphProductAtlas.fst_continuous
  exact parameter_graph_local_joint_image_rational z' x y u v r Ω₀ ho
    (fun p w ↦ AA p w.1) (fun p w ↦ BB p w.1)
    (fun p w ↦ CC p w.1) (fun p w ↦ DD p w.1) (fun _ w ↦ w.2)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas x y)
      (ParameterGraphHomAtlas.atlas x u) r Ω hΩ AA hAA)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas x y)
      (ParameterGraphHomAtlas.atlas y u) r Ω hΩ BB hBB)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas x y)
      (ParameterGraphHomAtlas.atlas x v) r Ω hΩ CC hCC)
    (parameter_graph_local_joint_comp_fst z (ParameterGraphHomAtlas.atlas x y)
      (ParameterGraphHomAtlas.atlas y v) r Ω hΩ DD hDD)
    ((jointFiberContDiffOn_univ_iff.mpr
      (parameter_graph_joint_native_snd z (ParameterGraphHomAtlas.atlas x y) r)).mono
      (fun _ _ ↦ mem_univ _))

end HolomorphicAnosov
