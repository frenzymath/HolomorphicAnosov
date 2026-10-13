import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphBoundedSectionFixedPoint
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphWeightedLimitContinuity
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- A uniformly contracting jet action with bounded forcing has a unique bounded invariant section
with continuous vector evaluations if the action preserves evaluation continuity. The section
has norm at most `B / (1 - q)` (Hirsch–Pugh–Shub, pp. 25, 32–35, 62). -/
theorem parameter_graph_bounded_evaluation_continuity
    {I Z A : Type*} [TopologicalSpace Z] [TopologicalSpace A]
    (S : I → Type*)
    [∀i,NormedAddCommGroup (S i)] [∀i,NormedSpace ℝ (S i)]
    [∀i,CompleteSpace (S i)]
    {F : A → Type*}
    [∀p,NormedAddCommGroup (F p)] [∀p,NormedSpace ℝ (F p)]
    [TopologicalSpace (Sigma F)]
    (f : FiniteRankNormedAtlas (E := F))
    (R : I → I) (Φ : ∀i,S (R i) → S i)
    (q B : NNReal) (hq : q<1)
    (hΦ : ∀i,LipschitzWith q (Φ i)) (hzero : ∀i,‖Φ i 0‖≤B)
    (a : Z → I) (b : Z → A) (hb : Continuous b)
    (L : ∀z,S (a z) →L[ℝ] F (b z))
    (w : Z → ℝ) (hw : Continuous w) (hw0 : ∀z,0≤w z)
    (hL : ∀z,‖L z‖≤w z)
    (hseed : Continuous (fun z ↦ (⟨b z,L z 0⟩ : Sigma F)))
    (hpreserve : ∀s : ∀i,S i,
      Continuous (fun z ↦ (⟨b z,L z (s (a z))⟩ : Sigma F)) →
      Continuous (fun z ↦ (⟨b z,L z (Φ (a z) (s (R (a z))))⟩ : Sigma F))) :
    ∃s : ∀i,S i,
      (∀i,Φ i (s (R i))=s i) ∧
      (∀i,‖s i‖≤(B:ℝ)/(1-q)) ∧
      (∀t : ∀i,S i,(∃M : ℝ,∀i,‖t i‖≤M) →
        (∀i,Φ i (t (R i))=t i) → t=s) ∧
      Continuous (fun z ↦ (⟨b z,L z (s (a z))⟩ : Sigma F)) := by
  obtain ⟨s,hs,hbound,hunique,herr⟩ :=
    parameter_graph_bounded_section_fixed_point S R Φ q B hq hΦ hzero
  let Q : ℕ → ∀i,S i := fun n ↦
    (fun t : ∀i,S i ↦ fun i ↦ Φ i (t (R i)))^[n] (fun _ ↦ 0)
  have hc : ∀n,Continuous (fun z ↦ (⟨b z,L z (Q n (a z))⟩ : Sigma F)) := by
    intro n
    induction n with
    | zero => exact hseed
    | succ n ih =>
        simpa only [Q,Function.iterate_succ_apply'] using hpreserve (Q n) ih
  refine ⟨s,hs,hbound,hunique,?_⟩
  apply parameter_graph_weighted_limit_continuity f b hb
    (fun n z ↦ L z (Q n (a z))) (fun z ↦ L z (s (a z))) hc
    w hw hw0 (fun n ↦ (q:ℝ)^n*((B:ℝ)/(1-q)))
    (fun n ↦ mul_nonneg (pow_nonneg q.2 n)
      (div_nonneg B.2 (sub_nonneg.mpr (le_of_lt (by exact_mod_cast hq)))))
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one q.2
      (show (q:ℝ)<1 by exact_mod_cast hq)).mul_const ((B:ℝ)/(1-q)))
  intro n z
  calc
    _ = ‖L z (Q n (a z)-s (a z))‖ := by rw [map_sub]
    _ ≤ ‖L z‖*‖Q n (a z)-s (a z)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ w z*((q:ℝ)^n*((B:ℝ)/(1-q))) :=
      mul_le_mul (hL z) (herr n (a z)) (norm_nonneg _) (hw0 z)
    _ = _ := mul_comm _ _

end HolomorphicAnosov
