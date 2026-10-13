import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnitSectionFixedPoint
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphWeightedLimitContinuity
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Set Filter Topology
namespace HolomorphicAnosov

/-- A point and a tangent vector in the same original fibre. -/
structure ParameterGraphTangentPoint {A : Type*} (E : A → Type*) where
  base : A
  point : E base
  vector : E base

namespace ParameterGraphTangentPoint
variable {A Z : Type*} {E : A → Type*} [TopologicalSpace (Sigma E)]
instance : TopologicalSpace (ParameterGraphTangentPoint E) :=
  TopologicalSpace.induced (fun z ↦ ((⟨z.base,z.point⟩ : Sigma E),
    (⟨z.base,z.vector⟩ : Sigma E))) inferInstance

theorem continuous_pair : Continuous (fun z : ParameterGraphTangentPoint E ↦
    ((⟨z.base,z.point⟩ : Sigma E),(⟨z.base,z.vector⟩ : Sigma E))) := continuous_induced_dom

theorem continuous_point : Continuous (fun z : ParameterGraphTangentPoint E ↦
    (⟨z.base,z.point⟩ : Sigma E)) := continuous_pair.fst

theorem continuous_vector : Continuous (fun z : ParameterGraphTangentPoint E ↦
    (⟨z.base,z.vector⟩ : Sigma E)) := continuous_pair.snd

theorem continuous_mk [TopologicalSpace Z] (b : Z → A) (x v : ∀z,E (b z))
    (hx : Continuous (fun z ↦ (⟨b z,x z⟩ : Sigma E)))
    (hv : Continuous (fun z ↦ (⟨b z,v z⟩ : Sigma E))) :
    Continuous (fun z ↦ (⟨b z,x z,v z⟩ : ParameterGraphTangentPoint E)) := by
  apply continuous_induced_rng.mpr
  exact hx.prodMk hv
end ParameterGraphTangentPoint

/-- A contracting slope action that preserves continuous evaluation has a continuous invariant slope field (HPS, pp.25, 35, 62). -/
theorem parameter_graph_continuous_invariant_slope
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,CompleteSpace (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (R : Sigma E → Sigma E)
    (Φ : ∀i : Sigma E, {P : E (R i).1 →L[ℝ] F (R i).1 // ‖P‖≤1} →
      {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1})
    (q : NNReal) (hq : q<1) (hΦ : ∀i,LipschitzWith q (Φ i))
    (hpreserve : ∀P : ∀i : Sigma E, {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1},
      Continuous (fun z : ParameterGraphTangentPoint E ↦
        (⟨z.base,(P ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma F)) →
      Continuous (fun z : ParameterGraphTangentPoint E ↦
        (⟨z.base,(Φ ⟨z.base,z.point⟩ (P (R ⟨z.base,z.point⟩))).1 z.vector⟩ : Sigma F))) :
    ∃P : ∀i : Sigma E, {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1},
      (∀i,Φ i (P (R i))=P i) ∧
      Continuous (fun z : ParameterGraphTangentPoint E ↦
        (⟨z.base,(P ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma F)) := by
  obtain ⟨P,hfix,_,herr⟩ := parameter_graph_unit_section_fixed_point
    (fun i : Sigma E ↦ E i.1 →L[ℝ] F i.1) R Φ q hq hΦ
  let Q : ℕ → ∀i : Sigma E, {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1} :=
    fun n ↦ (fun s i ↦ Φ i (s (R i)))^[n] (fun _ ↦ ⟨0,by simp⟩)
  have hc : ∀n,Continuous (fun z : ParameterGraphTangentPoint E ↦
      (⟨z.base,(Q n ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma F)) := by
    intro n
    induction n with
    | zero =>
        exact parameter_graph_atlas_zero_continuous f
          (fun z : ParameterGraphTangentPoint E ↦ z.base)
          ((parameter_graph_atlas_projection_continuous e).comp
            ParameterGraphTangentPoint.continuous_point)
    | succ n ih =>
        simpa only [Q, Function.iterate_succ_apply'] using hpreserve (Q n) ih
  refine ⟨P,hfix,?_⟩
  apply parameter_graph_weighted_limit_continuity f (fun z : ParameterGraphTangentPoint E ↦ z.base)
    ((parameter_graph_atlas_projection_continuous e).comp ParameterGraphTangentPoint.continuous_point)
    (fun n z ↦ (Q n ⟨z.base,z.point⟩).1 z.vector)
    (fun z ↦ (P ⟨z.base,z.point⟩).1 z.vector) hc
    (fun z ↦ ‖z.vector‖) (e.continuous_norm.comp ParameterGraphTangentPoint.continuous_vector)
    (fun z ↦ norm_nonneg z.vector) (fun n ↦ (q : ℝ)^n) (fun _ ↦ by positivity)
    (tendsto_pow_atTop_nhds_zero_of_lt_one q.2 (by exact_mod_cast hq))
  intro n z
  calc
    _ = ‖((Q n ⟨z.base,z.point⟩).1-(P ⟨z.base,z.point⟩).1) z.vector‖ := rfl
    _ ≤ ‖(Q n ⟨z.base,z.point⟩).1-(P ⟨z.base,z.point⟩).1‖ * ‖z.vector‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (q : ℝ)^n * ‖z.vector‖ := mul_le_mul_of_nonneg_right (herr n _) (norm_nonneg _)

/-- Forward image version: the anchor return is an equivalence, and the continuity-preservation hypothesis is expressed by the exact forward equation. -/
theorem parameter_graph_continuous_invariant_slope_forward
    {A : Type*} [TopologicalSpace A] {E F : A → Type*}
    [∀p,NormedAddCommGroup (E p)] [∀p,NormedSpace ℝ (E p)]
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [∀p,CompleteSpace (F p)]
    [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (T : Sigma E ≃ Sigma E)
    (Φ : ∀i : Sigma E, {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1} →
      {P : E (T i).1 →L[ℝ] F (T i).1 // ‖P‖≤1})
    (q : NNReal) (hq : q<1) (hΦ : ∀i,LipschitzWith q (Φ i))
    (hpreserve : ∀P Q : ∀i : Sigma E, {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1},
      (∀i,Φ i (P i)=Q (T i)) →
      Continuous (fun z : ParameterGraphTangentPoint E ↦
        (⟨z.base,(P ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma F)) →
      Continuous (fun z : ParameterGraphTangentPoint E ↦
        (⟨z.base,(Q ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma F))) :
    ∃P : ∀i : Sigma E, {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1},
      (∀i,Φ i (P i)=P (T i)) ∧
      Continuous (fun z : ParameterGraphTangentPoint E ↦
        (⟨z.base,(P ⟨z.base,z.point⟩).1 z.vector⟩ : Sigma F)) := by
  let S (i : Sigma E) := {P : E i.1 →L[ℝ] F i.1 // ‖P‖≤1}
  let transport {i j : Sigma E} (h : i=j) (v : S i) : S j := h ▸ v
  have htransport {i j : Sigma E} (h : i=j) : LipschitzWith 1 (transport h) := by
    subst j
    exact LipschitzWith.id
  have htransport_heq {i j : Sigma E} (h : i=j) (v : S i) : HEq (transport h v) v := by
    subst j
    rfl
  let Ψ (i : Sigma E) (v : S (T.symm i)) : S i :=
    transport (T.apply_symm_apply i) (Φ (T.symm i) v)
  have hΨ (i : Sigma E) : LipschitzWith q (Ψ i) := by
    simpa only [Ψ,Function.comp_def,one_mul] using
      (htransport (T.apply_symm_apply i)).comp (hΦ (T.symm i))
  have hforward (P : ∀i,S i) (i : Sigma E) :
      Φ i (P i) = Ψ (T i) (P (T.symm (T i))) := by
    have he := (htransport_heq (T.apply_symm_apply (T i))
      (Φ (T.symm (T i)) (P (T.symm (T i))))).symm
    have hcongr (j k : Sigma E) (h : j=k) : HEq (Φ j (P j)) (Φ k (P k)) := by
      subst k
      rfl
    exact eq_of_heq ((hcongr _ _ (T.symm_apply_apply i)).symm.trans he)
  obtain ⟨P,hfix,hPc⟩ := parameter_graph_continuous_invariant_slope e f T.symm Ψ q hq hΨ
    (fun P hP ↦ hpreserve P (fun i ↦ Ψ i (P (T.symm i))) (hforward P) hP)
  refine ⟨P,?_,hPc⟩
  intro i
  rw [hforward P i,hfix]


end HolomorphicAnosov
