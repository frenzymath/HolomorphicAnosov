import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LittleORepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.BoundedRepresentativeStructure
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularRadii
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.AnnularIndex
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.EventuallySlopeBound
import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.NormCore
import Mathlib.Tactic.Linarith

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- HPS (3.3), p.28: choose a representative on each shrinking annulus.
At annular index n compare to q_m using the finite radius conditions for m≤n.
Cauchyness and the vanishing error 2^(-n) give the asserted eventual slope estimate. -/
theorem annular_approximation
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (q : ℕ → BoundedRepresentative X Y)
    (hc : CauchySeq (fun n ↦ jetClass X Y (q n))) :
    ∃ g : X → Y, g 0 = 0 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N,
      ∀ᶠ x in 𝓝 (0 : X), ‖g x - (q m : X → Y) x‖ ≤ ε * ‖x‖ := by
  classical
  have he (n : ℕ) : ∀ᶠ x in 𝓝 (0 : X), ∀ m : Fin (n+1),
      ‖(q n : X → Y) x - (q m : X → Y) x‖ ≤
        (‖jetClass X Y (q n) - jetClass X Y (q m)‖ + (1/2:ℝ)^n) * ‖x‖ := by
    apply Filter.eventually_all.mpr
    intro m
    have hb := eventually_slope_le X Y (q n - q m)
      (C := ‖jetClass X Y (q n) - jetClass X Y (q m)‖ + (1/2:ℝ)^n) (by
        change ‖jetClass X Y (q n - q m)‖ < _
        simp only [jetClass]
        exact lt_add_of_pos_right _ (pow_pos (by norm_num : (0:ℝ)<1/2) n))
    filter_upwards [eventually_nhdsWithin_iff.mp hb] with x hx
    by_cases hx0 : x = 0
    · subst x; simp [(q n).property.1, (q m).property.1]
    · exact hx (by simpa using hx0)
  choose δ hδ hb using fun n ↦ Metric.nhds_basis_closedBall.eventually_iff.mp (he n)
  obtain ⟨r, hrpos, hra, hrd, hrt⟩ := annular_radii δ hδ
  have hi (x : X) (hx : 0 < ‖x‖ ∧ ‖x‖ ≤ r 0) :
      ∃ n, r (n+1) < ‖x‖ ∧ ‖x‖ ≤ r n := annular_index hrt hx.1 hx.2
  let k (x : X) : ℕ := if hx : 0 < ‖x‖ ∧ ‖x‖ ≤ r 0 then (hi x hx).choose else 0
  have hk (x : X) (hx : 0 < ‖x‖ ∧ ‖x‖ ≤ r 0) :
      r (k x+1) < ‖x‖ ∧ ‖x‖ ≤ r (k x) := by
    dsimp [k]; rw [dite_eq_left hx]; exact (hi x hx).choose_spec
  let g : X → Y := fun x ↦ (q (k x) : X → Y) x
  refine ⟨g, (q (k 0)).property.1, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε/2) (half_pos hε)
  have ht : Tendsto (fun n : ℕ ↦ (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 (ε/2) (half_pos hε))
  refine ⟨max N K, fun m hm ↦ ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : X) (hrpos m)] with x hx
  have hxm : ‖x‖ ≤ r m := by simpa [Metric.mem_closedBall, dist_zero_right] using hx
  by_cases hx0 : x = 0
  · subst x; simp [g, (q (k 0)).property.1, (q m).property.1]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hxx := hk x ⟨hxpos, hxm.trans (hra.antitone (Nat.zero_le m))⟩
  have hmk : m ≤ k x := by
    by_contra hh
    have hkm : k x + 1 ≤ m := by omega
    have hh := hra.antitone hkm
    linarith [hxx.1]
  have hxd : x ∈ Metric.closedBall 0 (δ (k x)) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hxx.2.trans (hrd _)
  have hbound := hb (k x) hxd ⟨m, by omega⟩
  have hd : ‖jetClass X Y (q (k x)) - jetClass X Y (q m)‖ < ε/2 := by
    simpa [dist_eq_norm] using hN (k x) (by omega) m (by omega)
  have hg := hK (k x) (by omega)
  exact hbound.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x))

end HolomorphicAnosov.BoundedLipschitzJets

