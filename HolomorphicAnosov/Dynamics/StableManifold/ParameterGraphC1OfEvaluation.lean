import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasDerivative
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointC1Criterion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity

noncomputable section
open Set Topology
namespace HolomorphicAnosov

/-- HPS pp.35 and 61–62: continuity of the actual derivative evaluation yields
joint fibre C¹ regularity in a finite rank atlas. On each chart overlap conjugate
the actual derivative by the two linear frames. Its evaluation on each fixed
model vector is continuous, by the assumed continuity of the total derivative
evaluation and the target chart. Finite dimensionality upgrades this to operator
norm continuity. The continuous total map similarly supplies continuous value
coordinates. The joint C¹ chart criterion then identifies the actual first jets.
No derivative in the base parameter or topology on a moving Hom bundle is used. -/
theorem parameter_graph_c1_of_evaluation
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀ p, E p → F (b p))
    (hg : Continuous (fun z : Sigma E ↦ (⟨b z.1, g z.1 z.2⟩ : Sigma F)))
    (D : ∀ p, E p → E p →L[ℝ] F (b p))
    (hD : ∀ p x, HasFDerivAt (g p) (D p x) x)
    (hDc : ∀ i, Continuous
      (fun z : {p // p ∈ (e.chart i).baseSet} ×
          (FiniteFiberModel (e.rank i) × FiniteFiberModel (e.rank i)) ↦
        (⟨b z.1.1, D z.1.1 ((e.coordinates i z.1.1 z.1.2).symm z.2.1)
          ((e.coordinates i z.1.1 z.1.2).symm z.2.2)⟩ : Sigma F))) :
    JointFiberContDiff e f b 1 g := by
  let L i j (z : A × FiniteFiberModel (e.rank i)) :=
    fderiv ℝ (fibreChartExpression e f b g i j z.1) z.2
  have hL i j p (hp : p ∈ (e.chart i).baseSet)
      (hbp : b p ∈ (f.chart j).baseSet) x :
      L i j (p, x) = (f.coordinates j (b p) hbp).toContinuousLinearMap.comp
        ((D p ((e.coordinates i p hp).symm x)).comp
          (e.coordinates i p hp).symm.toContinuousLinearMap) :=
    (parameter_graph_atlas_derivative e f b g i j p hp hbp x _ (hD p _)).fderiv
  apply parameter_graph_joint_c1_criterion e f b g D hD L hL
  · intro i j
    rw [continuousOn_iff_continuous_domRestrict, continuous_clm_apply]
    intro v
    let S := (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i))))
    let H : S → {p // p ∈ (e.chart i).baseSet} ×
        (FiniteFiberModel (e.rank i) × FiniteFiberModel (e.rank i)) :=
      fun z ↦ (⟨z.1.1, z.2.1.1⟩, (z.1.2, v))
    have hH : Continuous H := by
      exact (continuous_subtype_val.fst.subtype_mk _).prodMk
        (continuous_subtype_val.snd.prodMk continuous_const)
    have heval := (hDc i).comp hH
    have hchart := (f.chart j).toOpenPartialHomeomorph.continuousOn.comp_continuous heval
      (fun z : S ↦ (f.chart j).mem_source.mpr z.2.1.2)
    have heq : (fun z : S ↦ L i j z.1 v) =
        fun z : S ↦ ((f.chart j)
          (⟨b z.1.1, D z.1.1 ((e.coordinates i z.1.1 z.2.1.1).symm z.1.2)
            ((e.coordinates i z.1.1 z.2.1.1).symm v)⟩ : Sigma F)).2 := by
      funext z
      rw [hL i j z.1.1 z.2.1.1 z.2.1.2 z.1.2,
        f.chart_apply j (b z.1.1) z.2.1.2]
      rfl
    change Continuous (fun z : S ↦ L i j z.1 v)
    rw [heq]
    exact hchart.snd
  · intro i j
    rw [continuousOn_iff_continuous_domRestrict]
    let S := (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ
      (univ : Set (FiniteFiberModel (e.rank i))))
    have hinv (z : S) : (e.chart i).toOpenPartialHomeomorph.symm z.1 =
        (⟨z.1.1, (e.coordinates i z.1.1 z.2.1.1).symm z.1.2⟩ : Sigma E) := by
      have happly : (e.chart i)
          (⟨z.1.1, (e.coordinates i z.1.1 z.2.1.1).symm z.1.2⟩ : Sigma E) = z.1 := by
        rw [e.chart_apply i z.1.1 z.2.1.1]
        simp
      exact (congrArg (e.chart i).toOpenPartialHomeomorph.symm happly.symm).trans
        ((e.chart i).toOpenPartialHomeomorph.left_inv
          ((e.chart i).mem_source.mpr z.2.1.1))
    have hc : Continuous (fun z : S ↦ (e.chart i).toOpenPartialHomeomorph.symm z.1) :=
      (e.chart i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        continuous_subtype_val (fun z ↦ (e.chart i).mem_target.mpr z.2.1.1)
    have hout := hg.comp hc
    have hcoord := (f.chart j).toOpenPartialHomeomorph.continuousOn.comp_continuous hout (fun z : S ↦ by
      apply (f.chart j).mem_source.mpr
      change b ((e.chart i).toOpenPartialHomeomorph.symm z.1).1 ∈ (f.chart j).baseSet
      rw [hinv]
      exact z.2.1.2)
    exact hcoord.snd

/-- Continuous evaluation on the original point-and-tangent-vector space
suffices for joint fibre C¹. The two inverse source frames are continuous,
so they give a continuous map into ParameterGraphTangentPoint. Pull the
assumed derivative evaluation back along that map and use the chart-level
C¹ evaluation criterion. This is the direct interface for the invariant
slope field constructed by the contracting section theorem. -/
theorem parameter_graph_c1_of_tangent_evaluation
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {E : A → Type*} {F : B → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (b : A → B) (g : ∀ p, E p → F (b p))
    (hg : Continuous (fun z : Sigma E ↦ (⟨b z.1, g z.1 z.2⟩ : Sigma F)))
    (D : ∀ p, E p → E p →L[ℝ] F (b p))
    (hD : ∀ p x, HasFDerivAt (g p) (D p x) x)
    (hDc : Continuous (fun z : ParameterGraphTangentPoint E ↦
      (⟨b z.base, D z.base z.point z.vector⟩ : Sigma F))) :
    JointFiberContDiff e f b 1 g := by
  apply parameter_graph_c1_of_evaluation e f b g hg D hD
  intro i
  exact hDc.comp (ParameterGraphTangentPoint.continuous_mk
    (fun z : (e.chart i).baseSet ×
        (FiniteFiberModel (e.rank i) × FiniteFiberModel (e.rank i)) ↦ z.1.1)
    (fun z ↦ (e.coordinates i z.1.1 z.1.2).symm z.2.1)
    (fun z ↦ (e.coordinates i z.1.1 z.1.2).symm z.2.2)
    ((atlas_frame_continuous e i).comp (continuous_fst.prodMk continuous_snd.fst))
    ((atlas_frame_continuous e i).comp (continuous_fst.prodMk continuous_snd.snd)))

/-- Reindex continuous receiving-slope evaluation by the actual inverse
horizontal graph map. This is dependent-fibre transport only: the inverse
anchor has receiving base equal to the tested tangent point's base, and its
forward anchor and transported vector are exactly the original point and vector. -/
theorem parameter_graph_receiving_evaluation_continuous
    {A : Type*} [TopologicalSpace A]
    {E F : A → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (h : A ≃ₜ A)
    (H : ∀ p, E p ≃ₜ E (h p))
    (hR : Continuous (Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)).symm)
    (Q : ∀ p, E p → E p →L[ℝ] F p)
    (heval : ∀ p : ParameterGraphTangentPoint E → A, Continuous p →
      ∀ x : ∀ z, E (p z), Continuous (fun z ↦ (⟨p z, x z⟩ : Sigma E)) →
      ∀ v : ∀ z, E (h (p z)), Continuous (fun z ↦ (⟨h (p z), v z⟩ : Sigma E)) →
      Continuous (fun z ↦ (⟨h (p z), Q (h (p z)) (H (p z) (x z)) (v z)⟩ : Sigma F))) :
    Continuous (fun z : ParameterGraphTangentPoint E ↦
      (⟨z.base, Q z.base z.point z.vector⟩ : Sigma F)) := by
  let R := Equiv.sigmaCongr h.toEquiv (fun p ↦ (H p).toEquiv)
  let anchor (z : ParameterGraphTangentPoint E) := R.symm ⟨z.base, z.point⟩
  let p (z : ParameterGraphTangentPoint E) := (anchor z).1
  let x (z : ParameterGraphTangentPoint E) : E (p z) := (anchor z).2
  have ha : Continuous anchor := hR.comp ParameterGraphTangentPoint.continuous_point
  have hp : Continuous p := (parameter_graph_atlas_projection_continuous e).comp ha
  have hb (z : ParameterGraphTangentPoint E) : h (p z) = z.base :=
    congrArg Sigma.fst (R.apply_symm_apply (⟨z.base,z.point⟩ : Sigma E))
  let v (z : ParameterGraphTangentPoint E) : E (h (p z)) :=
    cast (congrArg E (hb z).symm) z.vector
  have hv (z : ParameterGraphTangentPoint E) :
      (⟨h (p z), v z⟩ : Sigma E) = ⟨z.base,z.vector⟩ :=
    Sigma.ext (hb z) (cast_heq _ _)
  have hvc : Continuous (fun z ↦ (⟨h (p z), v z⟩ : Sigma E)) := by
    simpa only [hv] using
      (ParameterGraphTangentPoint.continuous_vector (E := E))
  have hc := heval p hp x ha v hvc
  apply hc.congr
  intro z
  have hz : (⟨h (p z), H (p z) (x z), v z⟩ : ParameterGraphTangentPoint E) = z := by
    have hz1 : (⟨h (p z), H (p z) (x z)⟩ : Sigma E) = ⟨z.base,z.point⟩ :=
      R.apply_symm_apply (⟨z.base,z.point⟩ : Sigma E)
    have hinj : Function.Injective (fun w : ParameterGraphTangentPoint E ↦
        ((⟨w.base,w.point⟩ : Sigma E),(⟨w.base,w.vector⟩ : Sigma E))) := by
      rintro ⟨a,u,w⟩ ⟨b,u',w'⟩ hh
      obtain ⟨h1,h2⟩ := Prod.mk.inj hh
      obtain ⟨hab, huu⟩ := Sigma.mk.inj_iff.mp h1
      cases hab
      have hu : u = u' := eq_of_heq huu
      cases hu
      have hw : w = w' := eq_of_heq (Sigma.mk.inj_iff.mp h2).2
      cases hw
      rfl
    apply hinj
    exact Prod.ext hz1 (hv z)
  exact congrArg (fun w : ParameterGraphTangentPoint E ↦
    (⟨w.base, Q w.base w.point w.vector⟩ : Sigma F)) hz



end HolomorphicAnosov
