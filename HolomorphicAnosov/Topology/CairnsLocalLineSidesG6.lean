import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import HolomorphicAnosov.Topology.TwoLocalSidesSeparation

open Set Metric
namespace HolomorphicAnosov

/-- At a straight boundary point, complementary open regions with that common
frontier occupy the two half-balls. Source: Cairns (1951), Theorem 2.1, p.860.
Each half-ball is convex, hence connected, and avoids the boundary. Both labels
occur arbitrarily close to the center. The two connected sides must consequently
have different labels; the complement cover makes these inclusions equalities. -/
theorem cairns_local_line_sides_g6 (C E c : Set ℂ) (L : ℂ →ₗ[ℝ] ℝ)
    (x : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : IsOpen C) (hE : IsOpen E) (hdis : Disjoint C E)
    (hcover : C ∪ E = cᶜ) (hxC : x ∈ closure C) (hxE : x ∈ closure E)
    (hline : ∀ z ∈ ball x ε, z ∈ c ↔ L z = L x) :
    (ball x ε ∩ C = ball x ε ∩ {z | L x < L z} ∧
      ball x ε ∩ E = ball x ε ∩ {z | L z < L x}) ∨
    (ball x ε ∩ C = ball x ε ∩ {z | L z < L x} ∧
      ball x ε ∩ E = ball x ε ∩ {z | L x < L z}) := by
  let P := ball x ε ∩ {z | L x < L z}
  let N := ball x ε ∩ {z | L z < L x}
  have hP : IsPreconnected P :=
    ((convex_ball x ε).inter (convex_halfSpace_gt L.isLinear (L x))).isPreconnected
  have hN : IsPreconnected N :=
    ((convex_ball x ε).inter (convex_halfSpace_lt L.isLinear (L x))).isPreconnected
  have hsides : ball x ε \ c = P ∪ N := by
    ext z
    simp only [P, N, mem_sdiff, mem_inter_iff, mem_ofPred_eq, mem_union]
    by_cases hz : z ∈ ball x ε
    · simp only [hz, true_and, hline z hz, ne_iff_lt_or_gt]
      exact or_comm
    · simp [hz]
  have hs := two_local_sides_separation hC hE hdis hcover hxC hxE
    isOpen_ball (mem_ball_self hε) hP hN hsides
  have heq {S T : Set ℂ} (hS : S ⊆ C) (hT : T ⊆ E)
      (hST : ball x ε \ c = S ∪ T) (hSb : S ⊆ ball x ε) (hTb : T ⊆ ball x ε) :
      ball x ε ∩ C = S ∧ ball x ε ∩ E = T := by
    constructor
    · apply Subset.antisymm
      · rintro z ⟨hzb,hzC⟩
        have hz : z ∈ S ∪ T := hST ▸ ⟨hzb, show z ∈ cᶜ from hcover ▸ Or.inl hzC⟩
        exact hz.elim id (fun h ↦ (disjoint_left.mp hdis hzC (hT h)).elim)
      · exact fun z hz ↦ ⟨hSb hz,hS hz⟩
    · apply Subset.antisymm
      · rintro z ⟨hzb,hzE⟩
        have hz : z ∈ S ∪ T := hST ▸ ⟨hzb, show z ∈ cᶜ from hcover ▸ Or.inr hzE⟩
        exact hz.elim (fun h ↦ (disjoint_left.mp hdis (hS h) hzE).elim) id
      · exact fun z hz ↦ ⟨hTb hz,hT hz⟩
  exact hs.elim (fun h ↦ Or.inl (heq h.1 h.2 hsides inter_subset_left inter_subset_left))
    (fun h ↦ Or.inr (heq h.2 h.1 (hsides.trans (union_comm _ _))
      inter_subset_left inter_subset_left))

/-- Nested cells sharing the same straight local boundary have a neighborhood
covered by the inner cell, the outer exterior, and the seam. In the half-ball
labelings above, containment rules out opposite labels by any nearby inner-cell
point. The remaining matching labeling covers both half-balls, and the supplied
line identity puts the intervening diameter in the seam. -/
theorem cairns_nested_local_seam_g6
    (C₁ E₁ c₁ C₂ E₂ c₂ d : Set ℂ) (L : ℂ →ₗ[ℝ] ℝ)
    (x : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC₁ : IsOpen C₁) (hE₁ : IsOpen E₁)
    (hC₂ : IsOpen C₂) (hE₂ : IsOpen E₂)
    (hd₁ : Disjoint C₁ E₁) (hd₂ : Disjoint C₂ E₂)
    (hc₁ : C₁ ∪ E₁ = c₁ᶜ) (hc₂ : C₂ ∪ E₂ = c₂ᶜ)
    (hxC₁ : x ∈ closure C₁) (hxE₁ : x ∈ closure E₁)
    (hxC₂ : x ∈ closure C₂) (hxE₂ : x ∈ closure E₂)
    (hl₁ : ∀ z ∈ ball x ε, z ∈ c₁ ↔ L z = L x)
    (hl₂ : ∀ z ∈ ball x ε, z ∈ c₂ ↔ L z = L x)
    (hld : ∀ z ∈ ball x ε, L z = L x → z ∈ d)
    (hsub : C₂ ⊆ C₁) : C₂ ∪ E₁ ∪ d ∈ nhds x := by
  obtain ⟨w,hwb,hwC⟩ := mem_closure_iff.mp hxC₂ (ball x ε) isOpen_ball
    (mem_ball_self hε)
  have hlabels₁ := cairns_local_line_sides_g6 C₁ E₁ c₁ L x ε hε
    hC₁ hE₁ hd₁ hc₁ hxC₁ hxE₁ hl₁
  have hlabels₂ := cairns_local_line_sides_g6 C₂ E₂ c₂ L x ε hε
    hC₂ hE₂ hd₂ hc₂ hxC₂ hxE₂ hl₂
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hε)
  intro z hzb
  rcases lt_trichotomy (L z) (L x) with hz | hz | hz
  · rcases hlabels₁ with ⟨ha,he⟩ | ⟨ha,he⟩ <;>
      rcases hlabels₂ with ⟨hb,hf⟩ | ⟨hb,hf⟩
    · exact Or.inl (Or.inr ((he.symm ▸ ⟨hzb,hz⟩ : z ∈ ball x ε ∩ E₁).2))
    · exact Or.inl (Or.inl ((hb.symm ▸ ⟨hzb,hz⟩ : z ∈ ball x ε ∩ C₂).2))
    · have hw₁ : L w < L x := (ha ▸ ⟨hwb,hsub hwC⟩ : w ∈ ball x ε ∩ {z | L z < L x}).2
      have hw₂ : L x < L w := (hb ▸ ⟨hwb,hwC⟩ : w ∈ ball x ε ∩ {z | L x < L z}).2
      exact (lt_asymm hw₁ hw₂).elim
    · exact Or.inl (Or.inl ((hb.symm ▸ ⟨hzb,hz⟩ : z ∈ ball x ε ∩ C₂).2))
  · exact Or.inr (hld z hzb hz)
  · rcases hlabels₁ with ⟨ha,he⟩ | ⟨ha,he⟩ <;>
      rcases hlabels₂ with ⟨hb,hf⟩ | ⟨hb,hf⟩
    · exact Or.inl (Or.inl ((hb.symm ▸ ⟨hzb,hz⟩ : z ∈ ball x ε ∩ C₂).2))
    · have hw₁ : L x < L w := (ha ▸ ⟨hwb,hsub hwC⟩ : w ∈ ball x ε ∩ {z | L x < L z}).2
      have hw₂ : L w < L x := (hb ▸ ⟨hwb,hwC⟩ : w ∈ ball x ε ∩ {z | L z < L x}).2
      exact (lt_asymm hw₁ hw₂).elim
    · exact Or.inl (Or.inr ((he.symm ▸ ⟨hzb,hz⟩ : z ∈ ball x ε ∩ E₁).2))
    · exact Or.inl (Or.inr ((he.symm ▸ ⟨hzb,hz⟩ : z ∈ ball x ε ∩ E₁).2))

/-- Multiplication of a nonzero direction by `I` and normalization gives a unit
normal. The real normal coordinate is signed area divided by the direction's
positive length, so it has precisely the same strict sign. -/
theorem cairns_unit_normal_coordinate_g6 (v : ℂ) (hv : v ≠ 0) :
    ∃ ν : ℂ, ‖ν‖ = 1 ∧ (v/ν).re=0 ∧
      ∀ z : ℂ, (z/ν).re = (star v*z).im / ‖v‖ := by
  let ν : ℂ := (v*Complex.I)/(‖v‖:ℂ)
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hν : ‖ν‖=1 := by
    simp [ν,hn.ne']
  have hre : ν.re = -v.im/‖v‖ := by simp [ν,Complex.div_ofReal,Complex.mul_re]
  have him : ν.im = v.re/‖v‖ := by simp [ν,Complex.div_ofReal,Complex.mul_im]
  have hcoord (z : ℂ) : (z/ν).re = (star v*z).im / ‖v‖ := by
    rw [Complex.div_re,Complex.normSq_eq_norm_sq,hν]
    simp only [one_pow,div_one,hre,him,Complex.mul_im,Complex.star_def,
      Complex.conj_re,Complex.conj_im]
    ring
  refine ⟨ν,hν,?_,hcoord⟩
  rw [hcoord]
  simp only [Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

end HolomorphicAnosov
