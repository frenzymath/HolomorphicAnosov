import HolomorphicAnosov.Dynamics.Bowen.FactOneProductScales

namespace HolomorphicAnosov.BowenBasicSetCoding

/-- Bowen's eight refinement scales with an arbitrary upper mesh bound.

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
the descending-scale definition after Lemma 5, p.728, and the small initial
rectangles preceding Lemma 13, p.731. DAG node:
`dynamics.bowen_fact_one_refinement_scales_g17`.

Proof: replace the positive modulus at δ by its minimum with three times the
requested mesh. At a positive radius r, apply the five-scale construction with
initial radius r and take its first successor. Its scale bound is less than
r/9 and less than the mesh, and its image bounds hold for F and its inverse.
Choose such a successor on positive radii and iterate it seven times from γ.
The original modulus bound follows by monotonicity of minimum. Positivity is
built into the successor type. Empty X requires no separate assumption. -/
theorem exists_factOne_refinement_scales
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (F : X ≃ₜ X) (γ mesh : ℝ) (hγ : 0 < γ) (hmesh : 0 < mesh)
    (εmod : ℝ → ℝ) (hmod : ∀ δ, 0 < δ → 0 < εmod δ) :
    ∃ α : Fin 8 → ℝ, α 0 = γ ∧ (∀ i, 0 < α i) ∧
      (∀ i : Fin 7, α i.succ < α i.castSucc) ∧
      (∀ i : Fin 7, α i.succ < mesh) ∧
      (∀ i : Fin 7,
        α i.succ < (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3))) ∧
      (∀ i : Fin 7, ∀ a b : X, dist a b ≤ α i.succ →
        dist (F a) (F b) < α i.castSucc ∧
          dist (F.symm a) (F.symm b) < α i.castSucc) := by
  classical
  let modulus := fun δ ↦ min (εmod δ) (3 * mesh)
  have hpos : ∀ δ, 0 < δ → 0 < modulus δ := fun δ hδ ↦
    lt_min (hmod δ hδ) (by positivity)
  have hstep : ∀ r : {r : ℝ // 0 < r}, ∃ s : {r : ℝ // 0 < r},
      s.val < r.val ∧ s.val < mesh ∧
      s.val < (1 / 3 : ℝ) * min (r.val / 3) (εmod (r.val / 3)) ∧
      ∀ a b : X, dist a b ≤ s.val →
        dist (F a) (F b) < r.val ∧ dist (F.symm a) (F.symm b) < r.val := by
    intro r
    obtain ⟨β, hβ0, hβpos, hβscale, hβmap⟩ :=
      exists_factOne_product_scales F r.val r.property modulus hpos
    have hb := hβscale 0
    have hm := hβmap 0
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, hβ0] at hb hm
    refine ⟨⟨β 1, hβpos 1⟩, ?_, ?_, ?_, hm⟩
    · have hh := hb.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _)
        (by norm_num : (0 : ℝ) ≤ 1 / 3))
      linarith [r.property]
    · have hh := hb.trans_le (mul_le_mul_of_nonneg_left
        ((min_le_right _ _).trans (min_le_right _ _))
        (by norm_num : (0 : ℝ) ≤ 1 / 3))
      linarith
    · exact hb.trans_le (mul_le_mul_of_nonneg_left
        (min_le_min_left _ (min_le_left _ _)) (by norm_num))
  choose step hdesc hmesh' hscale hmap using hstep
  let a : ℕ → {r : ℝ // 0 < r} := fun n ↦ step^[n] ⟨γ, hγ⟩
  have ha : ∀ n, a (n + 1) = step (a n) := fun n ↦ Function.iterate_succ_apply' ..
  refine ⟨fun i ↦ (a i.val).val, rfl, fun i ↦ (a i.val).property, ?_, ?_, ?_, ?_⟩
  · intro i
    change (a (i.val + 1)).val < (a i.val).val
    rw [ha]
    exact hdesc (a i.val)
  · intro i
    change (a (i.val + 1)).val < mesh
    rw [ha]
    exact hmesh' (a i.val)
  · intro i
    change (a (i.val + 1)).val < _
    rw [ha]
    exact hscale (a i.val)
  · intro i x y hxy
    change dist x y ≤ (a (i.val + 1)).val at hxy
    rw [ha] at hxy
    exact hmap (a i.val) x y hxy


end HolomorphicAnosov.BowenBasicSetCoding
