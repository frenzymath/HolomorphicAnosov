import HolomorphicAnosov.Analysis.Complex.MarkedConformalModulusCyclic

/-! # Opposite diagonals forced by the current partition hypotheses

The source rectangle's affine diagonals are transported through the literal
closure homeomorphisms in the marked-modulus witnesses. This audits the current
partition contract; it does not establish the intended Lehto–Virtanen rigidity
result. Source: the explicit model in `HasMarkedConformalModulus`, Ahlfors,
Lectures on Quasiconformal Mappings, Chapter II A, p.21.
-/

open Set HolomorphicAnosov.Analysis.MarkedRectangle
namespace HolomorphicAnosov

/-- The source rectangle's straight diagonal transports to an embedded arc
joining opposite prescribed marks, with every non-endpoint in the piece. -/
theorem qc_partition_diagonal_witness {P : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus P p m) :
    ∃ γ : unitInterval → ℂ, Topology.IsEmbedding γ ∧
      γ 0 = p 0 ∧ γ 1 = p 2 ∧
      (∀ t, γ t ∈ closure P) ∧
      (∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∈ P) := by
  obtain ⟨a, b, ha, hb, hm, F, Fi, hF, hFi, hbij, hmaps, hleft, hright,
    e, he, hc⟩ := hmod
  let d : unitInterval → ClosedRectangle a b := fun t ↦
    ⟨⟨a * (t : ℝ), b * (t : ℝ)⟩,
      ⟨⟨mul_nonneg ha.le t.property.1, mul_le_of_le_one_right ha.le t.property.2⟩,
        ⟨mul_nonneg hb.le t.property.1, mul_le_of_le_one_right hb.le t.property.2⟩⟩⟩
  have hd : Continuous d := by
    apply Continuous.subtype_mk
    exact Complex.equivRealProdCLM.symm.continuous.comp
      (show Continuous (fun t : unitInterval ↦ (a * (t : ℝ), b * (t : ℝ))) by fun_prop)
  have hdi : Function.Injective d := by
    intro s t h
    have hx := congrArg (fun z : ClosedRectangle a b ↦ (z : ℂ).re) h
    apply Subtype.ext
    change a * (s : ℝ) = a * (t : ℝ) at hx
    exact mul_left_cancel₀ ha.ne' hx
  let γ : unitInterval → ℂ := fun t ↦ (e (d t) : ℂ)
  refine ⟨γ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Topology.IsEmbedding.subtypeVal.comp
      (e.isEmbedding.comp (hd.isClosedEmbedding hdi).isEmbedding)
  · exact hc 0 (d 0) (by apply Complex.ext <;> simp [d, RectangleCorner])
  · exact hc 2 (d 1) (by apply Complex.ext <;> simp [d, RectangleCorner])
  · intro t
    exact (e (d t)).property
  · intro t ht₀ ht₁
    have ht : (d t : ℂ) ∈ OpenRectangle a b := by
      exact ⟨⟨mul_pos ha ht₀, mul_lt_of_lt_one_right ha ht₁⟩,
        ⟨mul_pos hb ht₀, mul_lt_of_lt_one_right hb ht₁⟩⟩
    change (e (d t) : ℂ) ∈ P
    rw [he (d t) ht]
    exact hbij.mapsTo ht

/-- The disputed partition hypotheses provide opposite-corner arcs entirely
in the closed ambient rectangle, with disjoint open arc images. This lemma
uses no crossing theorem and does not assert inconsistency. -/
theorem qc_partition_opposite_diagonals {M : ℝ} (hM : 0 < M)
    {P₁ P₂ : Set ℂ} (hopen₁ : IsOpen P₁) (hopen₂ : IsOpen P₂)
    (hdisj : Disjoint P₁ P₂)
    (hinside₁ : closure P₁ ⊆ closure (OpenRectangle M 1))
    (hinside₂ : closure P₂ ⊆ closure (OpenRectangle M 1))
    {m₁ m₂ : ℝ}
    (h₁ : HasMarkedConformalModulus P₁ (RectangleCorner M 1) m₁)
    (h₂ : HasMarkedConformalModulus P₂ (RectangleCorner M 1) m₂) :
    ∃ α β : unitInterval → ℂ,
      Topology.IsEmbedding α ∧ Topology.IsEmbedding β ∧
      α 0 = 0 ∧ α 1 = (M : ℂ) + Complex.I ∧
      β 0 = (M : ℂ) ∧ β 1 = Complex.I ∧
      (∀ t, α t ∈ ClosedRectangle M 1 ∧ β t ∈ ClosedRectangle M 1) ∧
      (∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
        α t ∈ OpenRectangle M 1 ∧ β t ∈ OpenRectangle M 1) ∧
      (∀ s t : unitInterval, 0 < (s : ℝ) → (s : ℝ) < 1 →
        0 < (t : ℝ) → (t : ℝ) < 1 → α s ≠ β t) := by
  obtain ⟨α, hα, hα0, hα1, hαcl, hαin⟩ := qc_partition_diagonal_witness h₁
  obtain ⟨β, hβ, hβ0, hβ1, hβcl, hβin⟩ := qc_partition_diagonal_witness h₂.cyclic
  have hcl := RectangleModelPreparation.closure_openRectangle hM zero_lt_one
  have hsub {P : Set ℂ} (ho : IsOpen P)
      (hi : closure P ⊆ closure (OpenRectangle M 1)) : P ⊆ OpenRectangle M 1 := by
    have hs : P ⊆ interior (ClosedRectangle M 1) :=
      ho.subset_interior_iff.mpr (subset_closure.trans (hcl ▸ hi))
    simpa only [ClosedRectangle, Complex.interior_reProdIm, interior_Icc, OpenRectangle]
      using hs
  refine ⟨α, β, hα, hβ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [RectangleCorner] using hα0
  · simpa [RectangleCorner] using hα1
  · simpa [RectangleCorner] using hβ0
  · simpa [RectangleCorner] using hβ1
  · intro t
    exact ⟨hcl ▸ hinside₁ (hαcl t), hcl ▸ hinside₂ (hβcl t)⟩
  · intro t ht₀ ht₁
    exact ⟨hsub hopen₁ hinside₁ (hαin t ht₀ ht₁),
      hsub hopen₂ hinside₂ (hβin t ht₀ ht₁)⟩
  · intro s t hs₀ hs₁ ht₀ ht₁ heq
    exact Set.disjoint_left.mp hdisj (heq ▸ hαin s hs₀ hs₁) (hβin t ht₀ ht₁)

end HolomorphicAnosov
