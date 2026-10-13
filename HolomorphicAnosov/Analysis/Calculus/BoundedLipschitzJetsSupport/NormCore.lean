import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.SlopeDescent

noncomputable section

namespace HolomorphicAnosov.BoundedLipschitzJets

open Filter Set
open scoped Topology _root_.Topology

variable (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Structural norm obligation, HPS (3.3), p. 27.
Every slope-bound set is nonempty and bounded below by zero. Intersecting
eventual sets gives triangle bounds; scaling gives |a|-homogeneity (handle
a=0 separately and use 1/a for the reverse inequality otherwise). Zero slope
is equivalent to every positive epsilon being an eventual slope bound, hence
to membership in the little-o submodule. Submodule quotient equality then
gives norm zero iff class zero. All operations descend from pointwise maps;
in particular neither a norm nor a completeness structure was assumed. -/
theorem jet_norm_core : NormedSpace.Core ℝ (BoundedJet X Y) := by
  refine { norm_nonneg := ?_, norm_smul := ?_, norm_triangle := ?_, norm_eq_zero_iff := ?_ }
  · intro j
    refine Quotient.inductionOn j ?_
    intro q
    change 0 ≤ representativeSlope X Y q
    obtain ⟨_, C, hC, hq⟩ := q.property
    exact le_csInf ⟨C, hC, hq⟩ (fun _ h => h.1)
  · intro a j
    refine Quotient.inductionOn j ?_
    intro q
    by_cases ha : a = 0
    · subst a
      rw [zero_smul, norm_zero, zero_mul]
      change jetNorm X Y (0 : BoundedJet X Y) = 0
      change representativeSlope X Y (0 : BoundedRepresentative X Y) = 0
      have hz : (0 : ℝ) ∈ slopeBounds X Y (0 : X → Y) :=
        ⟨le_rfl, Filter.Eventually.of_forall (fun x ↦ by simp)⟩
      have hbz : BddBelow (slopeBounds X Y (0 : X → Y)) :=
        ⟨0, fun _ h ↦ h.1⟩
      apply le_antisymm
      · exact csInf_le hbz hz
      · exact le_csInf ⟨0, hz⟩ (fun _ h ↦ h.1)
    · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
      have hmul (D : ℝ) (hD : D ∈ slopeBounds X Y (q : X → Y)) :
          ‖a‖ * D ∈ slopeBounds X Y ((a • q : BoundedRepresentative X Y) : X → Y) := by
        refine ⟨mul_nonneg (norm_nonneg _) hD.1, ?_⟩
        filter_upwards [hD.2] with x hx
        change ‖a • (q : X → Y) x‖ ≤ (‖a‖ * D) * ‖x‖
        rw [norm_smul]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hx (norm_nonneg a)
      have hdiv (C : ℝ) (hC : C ∈ slopeBounds X Y ((a • q : BoundedRepresentative X Y) : X → Y)) :
          C / ‖a‖ ∈ slopeBounds X Y (q : X → Y) := by
        refine ⟨div_nonneg hC.1 (norm_nonneg _), ?_⟩
        filter_upwards [hC.2] with x hx
        change ‖a • (q : X → Y) x‖ ≤ C * ‖x‖ at hx
        rw [norm_smul] at hx
        calc
          ‖(q : X → Y) x‖ ≤ (C * ‖x‖) / ‖a‖ :=
            (le_div_iff₀ ha').2 (by simpa [mul_comm] using hx)
          _ = (C / ‖a‖) * ‖x‖ := by ring
      have hp : BddBelow (slopeBounds X Y ((a • q : BoundedRepresentative X Y) : X → Y)) :=
        ⟨0, fun _ h => h.1⟩
      obtain ⟨_, C, hC, hqC⟩ := q.property
      have hs : (slopeBounds X Y (q : X → Y)).Nonempty := ⟨C, hC, hqC⟩
      have hs' : BddBelow (slopeBounds X Y (q : X → Y)) := ⟨0, fun _ h => h.1⟩
      have hscale : representativeSlope X Y (a • q) =
          ‖a‖ * representativeSlope X Y q := by
        apply le_antisymm
        · apply le_of_forall_pos_le_add
          intro ε hε
          let δ : ℝ := ε / (‖a‖ + 1)
          have hδ : 0 < δ := div_pos hε (by positivity)
          obtain ⟨D, hD, hDlt⟩ := exists_lt_of_csInf_lt hs
            (lt_add_of_pos_right _ hδ)
          have hupper := csInf_le hp (hmul D hD)
          calc
            representativeSlope X Y (a • q) ≤ ‖a‖ * D := hupper
            _ ≤ ‖a‖ * (representativeSlope X Y q + δ) :=
              mul_le_mul_of_nonneg_left (le_of_lt hDlt) (norm_nonneg _)
            _ = ‖a‖ * representativeSlope X Y q + ‖a‖ * δ := by ring
            _ ≤ ‖a‖ * representativeSlope X Y q + ε := by
              apply add_le_add_right
              dsimp [δ]
              have hden : 0 ≤ ‖a‖ + 1 := by positivity
              calc
                ‖a‖ * (ε / (‖a‖ + 1)) ≤ (‖a‖ + 1) * (ε / (‖a‖ + 1)) :=
                  mul_le_mul_of_nonneg_right (by linarith) hδ.le
                _ = ε := by field_simp
        · have hp_nonempty : (slopeBounds X Y ((a • q : BoundedRepresentative X Y) : X → Y)).Nonempty :=
            ⟨‖a‖ * C, hmul C ⟨hC, hqC⟩⟩
          apply le_csInf hp_nonempty
          intro C hC
          have hqC' := hdiv C hC
          have hle : representativeSlope X Y q ≤ C / ‖a‖ := csInf_le hs' hqC'
          have hmul' := (le_div_iff₀ ha').1 hle
          simpa [mul_comm] using hmul'
      exact hscale
  · intro j k
    refine Quotient.inductionOn j ?_
    intro q
    refine Quotient.inductionOn k ?_
    intro r
    change representativeSlope X Y (q + r) ≤
      representativeSlope X Y q + representativeSlope X Y r
    obtain ⟨_, C, hC, hqC⟩ := q.property
    obtain ⟨_, D, hD, hrD⟩ := r.property
    have hs : (slopeBounds X Y (q : X → Y)).Nonempty := ⟨C, hC, hqC⟩
    have hs' : BddBelow (slopeBounds X Y (q : X → Y)) := ⟨0, fun _ h => h.1⟩
    have ht : (slopeBounds X Y (r : X → Y)).Nonempty := ⟨D, hD, hrD⟩
    have ht' : BddBelow (slopeBounds X Y (r : X → Y)) := ⟨0, fun _ h => h.1⟩
    have hp : BddBelow (slopeBounds X Y ((q + r : BoundedRepresentative X Y) : X → Y)) :=
      ⟨0, fun _ h => h.1⟩
    have hsum (A B : ℝ) (hA : A ∈ slopeBounds X Y (q : X → Y))
        (hB : B ∈ slopeBounds X Y (r : X → Y)) :
        A + B ∈ slopeBounds X Y ((q + r : BoundedRepresentative X Y) : X → Y) := by
      refine ⟨add_nonneg hA.1 hB.1, ?_⟩
      filter_upwards [hA.2, hB.2] with x hx hy
      change ‖(q : X → Y) x + (r : X → Y) x‖ ≤ (A + B) * ‖x‖
      calc
        ‖(q : X → Y) x + (r : X → Y) x‖ ≤ ‖(q : X → Y) x‖ + ‖(r : X → Y) x‖ := norm_add_le _ _
        _ ≤ A * ‖x‖ + B * ‖x‖ := add_le_add hx hy
        _ = (A + B) * ‖x‖ := by ring
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨A, hA, hAlt⟩ := exists_lt_of_csInf_lt hs (lt_add_of_pos_right _ hδ)
    obtain ⟨B, hB, hBlt⟩ := exists_lt_of_csInf_lt ht (lt_add_of_pos_right _ hδ)
    have hab := csInf_le hp (hsum A B hA hB)
    calc
      representativeSlope X Y (q + r) ≤ A + B := hab
      _ ≤ representativeSlope X Y q + representativeSlope X Y r + ε := by
        dsimp [representativeSlope] at *
        dsimp [δ] at hAlt hBlt
        linarith
  · intro j
    refine Quotient.inductionOn j ?_
    intro q
    change representativeSlope X Y q = 0 ↔ Submodule.Quotient.mk q = 0
    have hqbound : ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ x in 𝓝[≠] (0 : X), ‖(q : X → Y) x‖ ≤ C * ‖x‖ := by
      obtain ⟨_, C, hC, hqC⟩ := q.property
      exact ⟨C, hC, hqC⟩
    have hnonneg : 0 ≤ representativeSlope X Y q := by
      change 0 ≤ sInf (slopeBounds X Y (q : X → Y))
      obtain ⟨C, hC, hqC⟩ := hqbound
      exact le_csInf ⟨C, hC, hqC⟩ (fun _ h ↦ h.1)
    constructor
    · intro hsl
      apply (jetClass_eq_iff X Y q 0).2
      change IsLittleORepresentative X Y ((q : X → Y) - (0 : X → Y))
      intro ε hε
      obtain ⟨C, hC, hqC⟩ := hqbound
      have hsinf : sInf (slopeBounds X Y (q : X → Y)) < ε := by
        simpa [representativeSlope] using (show representativeSlope X Y q < ε by simpa [hsl] using hε)
      obtain ⟨D, hD, hDlt⟩ := exists_lt_of_csInf_lt
        (s := slopeBounds X Y (q : X → Y)) ⟨C, hC, hqC⟩ hsinf
      filter_upwards [hD.2] with x hx
      change ‖(q : X → Y) x - (0 : X → Y) x‖ ≤ ε * ‖x‖
      simp only [Pi.zero_apply, sub_zero]
      calc
        ‖(q : X → Y) x‖ ≤ D * ‖x‖ := hx
        _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right (le_of_lt hDlt) (norm_nonneg x)
    · intro hz
      have hrel := (jetClass_eq_iff X Y q 0).1 hz
      change IsLittleORepresentative X Y ((q : X → Y) - (0 : X → Y)) at hrel
      apply le_antisymm
      · apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨_, C, hC, hqC⟩ := q.property
        have hmem : ε ∈ slopeBounds X Y (q : X → Y) := by
          refine ⟨hε.le, ?_⟩
          filter_upwards [hrel ε hε] with x hx
          simpa only [sub_zero] using hx
        have hb : BddBelow (slopeBounds X Y (q : X → Y)) :=
          ⟨0, fun _ h ↦ h.1⟩
        have hinf := csInf_le hb hmem
        change sInf (slopeBounds X Y (q : X → Y)) ≤ _ at hinf
        simpa [representativeSlope] using hinf
      · exact hnonneg

/-- The normed additive group built from the actual quotient and slope norm,
using the named structural obligation from HPS p. 27. -/
instance : NormedAddCommGroup (BoundedJet X Y) :=
  NormedAddCommGroup.ofCore (jet_norm_core X Y)

/-- The real normed-space structure induced by the quotient scalar action,
HPS (3.3), p. 27. -/
instance : NormedSpace ℝ (BoundedJet X Y) :=
  NormedSpace.ofCore (jet_norm_core X Y)

/-- HPS J_c requires a representative continuous on a neighborhood of zero.
Continuity only at zero would incorrectly include every bounded jet. -/
def HasContinuousRepresentative (j : BoundedJet X Y) : Prop :=
  ∃ q : BoundedRepresentative X Y, jetClass X Y q = j ∧
    ∃ U : Set X, IsOpen U ∧ (0 : X) ∈ U ∧ ContinuousOn (q : X → Y) U

/-- HPS J_d requires Fréchet differentiability at zero of a representative.
The derivative remainder then identifies its class with a bounded linear map. -/
def HasDifferentiableRepresentative (j : BoundedJet X Y) : Prop :=
  ∃ q : BoundedRepresentative X Y, jetClass X Y q = j ∧
    DifferentiableAt ℝ (q : X → Y) 0


end HolomorphicAnosov.BoundedLipschitzJets

