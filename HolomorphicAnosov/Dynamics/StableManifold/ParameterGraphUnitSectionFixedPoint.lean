import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
namespace HolomorphicAnosov

/-- A contracting point-valued return has a unique invariant section in the closed unit ball (HPS, p.25, pp.36, 57–58). -/
theorem parameter_graph_unit_section_fixed_point
    {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    (R : I → I)
    (Φ : ∀ i, {v : E (R i) // ‖v‖ ≤ 1} → {v : E i // ‖v‖ ≤ 1})
    (q : NNReal) (hq : q < 1) (hΦ : ∀ i, LipschitzWith q (Φ i)) :
    ∃ s : ∀ i, {v : E i // ‖v‖ ≤ 1},
      (∀ i, Φ i (s (R i)) = s i) ∧
      (∀ t : ∀ i, {v : E i // ‖v‖ ≤ 1},
        (∀ i, Φ i (t (R i)) = t i) → t = s) ∧
      ∀ (n : ℕ) (i : I),
        ‖((fun t : ∀ i, {v : E i // ‖v‖ ≤ 1} ↦ fun i ↦ Φ i (t (R i)))^[n]
          (fun i ↦ ⟨0, by simp⟩) i).1 - (s i).1‖ ≤ (q : ℝ) ^ n := by
  classical
  let S := {s : lp E ⊤ // ∀ i, ‖s i‖ ≤ 1}
  have hclosed : IsClosed {s : lp E ⊤ | ∀ i, ‖s i‖ ≤ 1} := by
    have heq : {s : lp E ⊤ | ∀ i, ‖s i‖ ≤ 1} =
        ⋂ i, {s : lp E ⊤ | ‖s i‖ ≤ 1} := by ext s; simp
    rw [heq]
    exact isClosed_iInter (fun i ↦
      isClosed_le (lp.evalCLM ℝ E ⊤ i).continuous.norm continuous_const)
  let : CompleteSpace S := hclosed.completeSpace_coe
  let z : S := ⟨0, by intro i; simp⟩
  let : Nonempty S := ⟨z⟩
  let T : S → S := fun s ↦
    ⟨⟨fun i ↦ (Φ i ⟨s.1 (R i), s.2 (R i)⟩).1, memℓp_infty_iff.mpr
      ⟨1, by rintro _ ⟨i, rfl⟩; exact (Φ i ⟨s.1 (R i), s.2 (R i)⟩).2⟩⟩,
      fun i ↦ (Φ i ⟨s.1 (R i), s.2 (R i)⟩).2⟩
  have hcontract (i : I) (v w : {v : E (R i) // ‖v‖ ≤ 1}) :
      ‖(Φ i v).1 - (Φ i w).1‖ ≤ (q : ℝ) * ‖v.1 - w.1‖ := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using (hΦ i).dist_le_mul v w
  have hTc : ContractingWith q T := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul ?_⟩
    intro s t
    change dist (T s).1 (T t).1 ≤ (q : ℝ) * dist s.1 t.1
    rw [dist_eq_norm, dist_eq_norm]
    apply lp.norm_le_of_forall_le (mul_nonneg q.2 (norm_nonneg _))
    intro i
    exact (hcontract i _ _).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero (s.1 - t.1) (R i)) q.2)
  let s₀ := hTc.fixedPoint T
  have hfix : T s₀ = s₀ := hTc.fixedPoint_isFixedPt
  let s : ∀ i, {v : E i // ‖v‖ ≤ 1} := fun i ↦ ⟨s₀.1 i, s₀.2 i⟩
  have hs (i : I) : Φ i (s (R i)) = s i := by
    apply Subtype.ext
    exact congrArg (fun t : S ↦ t.1 i) hfix
  refine ⟨s, hs, ?_, ?_⟩
  · intro t ht
    let t' : S := ⟨⟨fun i ↦ (t i).1, memℓp_infty_iff.mpr
      ⟨1, by rintro _ ⟨i, rfl⟩; exact (t i).2⟩⟩, fun i ↦ (t i).2⟩
    have htfix : T t' = t' := by
      apply Subtype.ext
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (ht i)
    have heq := hTc.fixedPoint_unique htfix
    funext i
    apply Subtype.ext
    exact congrArg (fun t : S ↦ t.1 i) heq
  · intro n
    induction n with
    | zero =>
      intro i
      simpa using (s i).2
    | succ n ih =>
      intro i
      rw [Function.iterate_succ_apply', ← hs i]
      exact (hcontract i _ _).trans (by
        simpa [pow_succ, mul_comm] using mul_le_mul_of_nonneg_left (ih (R i)) q.2)


/-- The forward-equivalence form follows by reindexing the bounded invariant-section theorem (HPS, p.25). -/
theorem parameter_graph_unit_section_fixed_point_forward
    {I : Type*} (E : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    (T : I ≃ I)
    (Φ : ∀ i, {v : E i // ‖v‖ ≤ 1} → {v : E (T i) // ‖v‖ ≤ 1})
    (q : NNReal) (hq : q < 1) (hΦ : ∀ i, LipschitzWith q (Φ i)) :
    ∃ s : ∀ i, {v : E i // ‖v‖ ≤ 1},
      (∀ i, Φ i (s i) = s (T i)) ∧
      ∀ t : ∀ i, {v : E i // ‖v‖ ≤ 1},
        (∀ i, Φ i (t i) = t (T i)) → t = s := by
  let transport {i j : I} (h : i = j) (v : {v : E i // ‖v‖ ≤ 1}) :
      {v : E j // ‖v‖ ≤ 1} := h ▸ v
  have htransport {i j : I} (h : i = j) : LipschitzWith 1 (transport h) := by
    subst j
    exact LipschitzWith.id
  have htransport_heq {i j : I} (h : i = j) (v : {v : E i // ‖v‖ ≤ 1}) :
      HEq (transport h v) v := by subst j; rfl
  have htransport_section (t : ∀ i, {v : E i // ‖v‖ ≤ 1})
      {i j : I} (h : i = j) : transport h (t i) = t j := by subst j; rfl
  let Ψ (i : I) (v : {v : E (T.symm i) // ‖v‖ ≤ 1}) : {v : E i // ‖v‖ ≤ 1} :=
    transport (T.apply_symm_apply i) (Φ (T.symm i) v)
  have hΨ (i : I) : LipschitzWith q (Ψ i) := by
    simpa only [Ψ, Function.comp_def, one_mul] using
      (htransport (T.apply_symm_apply i)).comp (hΦ (T.symm i))
  obtain ⟨s, hs, hunique, _⟩ := parameter_graph_unit_section_fixed_point E T.symm Ψ q hq hΨ
  have hforward (i : I) : Φ i (s i) = s (T i) := by
    have hi := hs (T i)
    have he := (htransport_heq (T.apply_symm_apply (T i))
      (Φ (T.symm (T i)) (s (T.symm (T i))))).symm.trans (heq_of_eq hi)
    have hcongr (j k : I) (h : j = k) : HEq (Φ j (s j)) (Φ k (s k)) := by
      subst k
      rfl
    exact eq_of_heq ((hcongr _ _ (T.symm_apply_apply i)).symm.trans he)
  refine ⟨s, hforward, ?_⟩
  intro t ht
  apply hunique t
  intro i
  dsimp only [Ψ]
  rw [ht (T.symm i)]
  exact htransport_section t (T.apply_symm_apply i)

end HolomorphicAnosov
