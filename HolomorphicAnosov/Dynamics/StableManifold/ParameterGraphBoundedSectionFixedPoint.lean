import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov

/-- HPS, Invariant Manifolds, p.25 and the affine tangent induction pp.32–35:
a uniformly contracting fibre action with bounded forcing has a unique bounded
invariant section for any point-valued return. It need not preserve the unit
ball or have an invertible return. The action on the complete dependent lp∞
space is well-defined since ||Φ_i(v)||≤q||v||+B. Banach's theorem supplies its
fixed point. Its norm inequality gives ||s||≤B/(1-q), and pointwise contraction
iterated from zero gives the geometric error bound q^n B/(1-q). A bounded
competitor lies in the same lp∞ space, so fixed-point uniqueness identifies it.
No continuity on the index set is asserted here. -/
theorem parameter_graph_bounded_section_fixed_point
    {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    (R : I → I) (Φ : ∀ i, E (R i) → E i)
    (q B : NNReal) (hq : q < 1)
    (hΦ : ∀ i, LipschitzWith q (Φ i))
    (hzero : ∀ i, ‖Φ i 0‖ ≤ B) :
    ∃ s : ∀ i, E i,
      (∀ i, Φ i (s (R i)) = s i) ∧
      (∀ i, ‖s i‖ ≤ (B : ℝ)/(1-q)) ∧
      (∀ t : ∀ i, E i, (∃ M : ℝ, ∀ i, ‖t i‖ ≤ M) →
        (∀ i, Φ i (t (R i)) = t i) → t = s) ∧
      ∀ (n : ℕ) (i : I),
        ‖((fun t : ∀ i, E i ↦ fun i ↦ Φ i (t (R i)))^[n]
          (fun _ ↦ 0) i) - s i‖ ≤ (q : ℝ)^n*((B : ℝ)/(1-q)) := by
  have hqR : (q : ℝ) < 1 := by exact_mod_cast hq
  have hden : 0 < 1-(q : ℝ) := sub_pos.mpr hqR
  have hbound (i : I) (v : E (R i)) : ‖Φ i v‖ ≤ (q : ℝ)*‖v‖+B := by
    calc
      _ ≤ ‖Φ i v-Φ i 0‖+‖Φ i 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (q : ℝ)*‖v‖+B := add_le_add
        (by simpa only [sub_zero] using (hΦ i).norm_sub_le v 0) (hzero i)
  let T : lp E ⊤ → lp E ⊤ := fun s ↦
    ⟨fun i ↦ Φ i (s (R i)), memℓp_infty_iff.mpr ⟨(q : ℝ)*‖s‖+B, by
      rintro _ ⟨i,rfl⟩
      exact (hbound i _).trans (add_le_add
        (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero s (R i)) q.2) le_rfl)⟩⟩
  have hTc : ContractingWith q T := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul ?_⟩
    intro s t
    rw [dist_eq_norm, dist_eq_norm]
    apply lp.norm_le_of_forall_le (mul_nonneg q.2 (norm_nonneg _))
    intro i
    exact ((hΦ i).norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero (s-t) (R i)) q.2)
  let s := hTc.fixedPoint T
  have hfix : T s = s := hTc.fixedPoint_isFixedPt
  have hs (i : I) : Φ i (s (R i)) = s i := congrArg (fun t : lp E ⊤ ↦ t i) hfix
  have hnorm : ‖s‖ ≤ (B : ℝ)/(1-q) := by
    have hineq : ‖T s‖ ≤ (q : ℝ)*‖s‖+B := by
      apply lp.norm_le_of_forall_le (add_nonneg (mul_nonneg q.2 (norm_nonneg _)) B.2)
      intro i
      exact (hbound i _).trans (add_le_add
        (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm ENNReal.top_ne_zero s (R i)) q.2) le_rfl)
    rw [hfix] at hineq
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hsnorm (i : I) : ‖s i‖ ≤ (B : ℝ)/(1-q) :=
    (lp.norm_apply_le_norm ENNReal.top_ne_zero s i).trans hnorm
  refine ⟨fun i ↦ s i,hs,hsnorm,?_,?_⟩
  · intro t ht htf
    obtain ⟨M,hM⟩ := ht
    let t' : lp E ⊤ := ⟨t,memℓp_infty_iff.mpr ⟨M,by rintro _ ⟨i,rfl⟩; exact hM i⟩⟩
    have htfix : T t' = t' := by
      apply Subtype.ext
      funext i
      exact htf i
    exact congrArg (fun u : lp E ⊤ ↦ (fun i ↦ u i)) (hTc.fixedPoint_unique htfix)
  · intro n
    induction n with
    | zero =>
        intro i
        simpa using hsnorm i
    | succ n ih =>
        intro i
        rw [Function.iterate_succ_apply']
        change ‖Φ i _ - s i‖ ≤ _
        rw [← hs i]
        exact ((hΦ i).norm_sub_le _ _).trans (by
          rw [pow_succ', mul_assoc]
          exact mul_le_mul_of_nonneg_left (ih (R i)) q.2)

end HolomorphicAnosov
