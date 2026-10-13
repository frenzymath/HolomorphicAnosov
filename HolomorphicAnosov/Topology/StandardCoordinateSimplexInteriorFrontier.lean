import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace HolomorphicAnosov

open Set Topology _root_.Topology Metric Bornology

/-- The strict normalized barycentric coordinates are exactly the interior of
the standard coordinate simplex, and its frontier is the weak simplex minus
that strict interior.

Source: Hatcher, *Algebraic Topology*, §2.1 pp.103–104 and Proposition A.2
p.521. The finite-product maximum-norm perturbation argument is expanded here
because no single Mathlib theorem packages this coordinate description. The
zero-dimensional singleton is included.

Natural-language proof: for V = Fin d → Real, Delta consists of nonnegative
coordinates with sum at most one and I consists of positive coordinates with
sum strictly below one. For u∈I, choose a positive minimum of its finitely many
coordinates and a positive sum margin; a sufficiently small maximum-norm ball
stays in Delta. Conversely, an interior point with a zero coordinate is moved
negative in that coordinate, and an interior point with sum one is moved above
one in one coordinate. Thus interior Delta=I. Since Delta is closed, frontier
Delta=Delta\I. At d=0, V is a singleton, Delta=I=univ and the frontier is
empty. The barycentric first coefficient is 1−Σu and the remaining
coefficients are u i, so frontier points are exactly normalized nonnegative
families with a zero coefficient, i.e. proper barycentric faces.
-/
theorem standard_coordinate_simplex_interior (d : ℕ) :
    let V := Fin d → ℝ
    let Delta : Set V := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}
    let I : Set V := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
    I.Nonempty ∧
      interior Delta = I := by
  dsimp
  let U : Set (Fin d → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}
  let J : Set (Fin d → ℝ) := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
  have hnonempty : J.Nonempty := by
    classical
    refine ⟨fun _ => (1 : ℝ) / (d + 1), ?_, ?_⟩
    · intro i
      positivity
    · simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      norm_num
      field_simp
      nlinarith [show (0 : ℝ) < d + 1 by positivity]
  have hinter : J ⊆ interior U := by
    classical
    intro u hu
    by_cases hd0 : d = 0
    · subst d
      simp [U]
    have hdn : 0 < d := Nat.pos_of_ne_zero hd0
    let : Nonempty (Fin d) := ⟨⟨0, hdn⟩⟩
    obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin d)) (fun i => u i)
      Finset.univ_nonempty
    let s : ℝ := ∑ i, u i
    let a : ℝ := u j
    let r : ℝ := min (a / 2) ((1 - s) / (2 * d))
    have ha : 0 < a := by
      dsimp [a]
      exact hu.1 j
    have hale : ∀ i, a ≤ u i := by
      intro i
      exact hmin i (Finset.mem_univ i)
    have hs : 0 < 1 - s := sub_pos.mpr hu.2
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (by positivity) (by positivity)
    have hr_a : r < a := by
      dsimp [r]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdr : (d : ℝ) * r < 1 - s := by
      have hrd : r ≤ (1 - s) / (2 * d) := min_le_right _ _
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hdn
      calc
        (d : ℝ) * r ≤ (d : ℝ) * ((1 - s) / (2 * d)) :=
          mul_le_mul_of_nonneg_left hrd (le_of_lt hdpos)
        _ = (1 - s) / 2 := by field_simp
        _ < 1 - s := by linarith
    apply (mem_interior_iff_mem_nhds).2
    rw [Metric.mem_nhds_iff]
    refine ⟨r, hr, ?_⟩
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm] at hv
    have hcoord : ∀ i, ‖v i - u i‖ < r := by
      intro i
      have := (pi_norm_lt_iff hr).1 (by simpa [Pi.sub_apply] using hv)
      simpa [Real.norm_eq_abs] using this i
    constructor
    · intro i
      have hi : a ≤ u i := hale i
      have habs : |v i - u i| < r := by simpa [Real.norm_eq_abs] using hcoord i
      have hlow : -(r : ℝ) < v i - u i := (abs_lt.mp habs).1
      have : 0 < v i := by linarith
      exact le_of_lt this
    · have hsumabs : ∑ i, |v i - u i| < (d : ℝ) * r := by
        have hlt : ∀ i ∈ (Finset.univ : Finset (Fin d)), |v i - u i| < r := by
          intro i hi
          simpa [Real.norm_eq_abs] using hcoord i
        simpa [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using
          (Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) hlt)
      have hsum : ∑ i, v i ≤ ∑ i, u i + ∑ i, |v i - u i| := by
        calc
          ∑ i, v i = ∑ i, (u i + (v i - u i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ ≤ ∑ i, u i + ∑ i, |v i - u i| := by
            calc
              ∑ i, (u i + (v i - u i)) ≤ ∑ i, (u i + |v i - u i|) := by
                apply Finset.sum_le_sum
                intro i hi
                linarith [le_abs_self (v i - u i)]
              _ = ∑ i, u i + ∑ i, |v i - u i| := by rw [Finset.sum_add_distrib]
      linarith
  have hsubset : interior U ⊆ J := by
    classical
    intro u hu
    have hdzero : d = 0 → u ∈ J := by
      intro hd
      subst d
      change (∀ i : Fin 0, 0 < u i) ∧ (∑ i : Fin 0, u i) < 1
      simp
    by_cases hd0 : d = 0
    · exact hdzero hd0
    have hdn : 0 < d := Nat.pos_of_ne_zero hd0
    have hU : U ∈ 𝓝 u := (mem_interior_iff_mem_nhds.mp hu)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    have huU : u ∈ U := interior_subset hu
    have hcoord : ∀ i, 0 < u i := by
      intro i
      by_contra hnot
      have hi : u i = 0 := le_antisymm (not_lt.mp hnot) (huU.1 i)
      let v : Fin d → ℝ := Function.update u i (u i - ε / 2)
      have hvball : v ∈ Metric.ball u ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        apply (pi_norm_lt_iff hε).2
        intro j
        by_cases hji : j = i
        · subst j
          simp [v, hi, Real.norm_eq_abs]
          rw [abs_of_pos hε]
          linarith
        · simp [v, hji]
          exact hε
      have hvD := hball hvball
      have := hvD.1 i
      simp [v, hi] at this
      linarith
    have hsum : ∑ i, u i < 1 := by
      by_contra hnot
      have hle : ∑ i, u i ≤ 1 := huU.2
      have hi0 : Fin d := ⟨0, hdn⟩
      let v : Fin d → ℝ := Function.update u hi0 (u hi0 + ε / 2)
      have hvball : v ∈ Metric.ball u ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        apply (pi_norm_lt_iff hε).2
        intro j
        by_cases hji : j = hi0
        · subst j
          simp [v, Real.norm_eq_abs]
          rw [abs_of_pos hε]
          linarith
        · simp [v, hji]
          exact hε
      have hvD := hball hvball
      have hsumv : ∑ j, v j ≤ 1 := hvD.2
      have herase : (∑ j ∈ (Finset.univ.erase hi0), u j) + u hi0 = ∑ j, u j :=
        Finset.sum_erase_add (Finset.univ : Finset (Fin d)) u (Finset.mem_univ hi0)
      have hsumv_eq : ∑ j, v j = (∑ j, u j) + ε / 2 := by
        calc
          ∑ j, v j = (u hi0 + ε / 2) + ∑ j ∈ (Finset.univ.erase hi0), u j := by
            dsimp [v]
            rw [Finset.sum_update_of_mem (Finset.mem_univ hi0) u (u hi0 + ε / 2)]
            simp only [Finset.erase_eq]
          _ = ((∑ j ∈ (Finset.univ.erase hi0), u j) + u hi0) + ε / 2 := by
            ring
          _ = (∑ j, u j) + ε / 2 := by rw [herase]
      rw [hsumv_eq] at hsumv
      linarith
    change (∀ i : Fin d, 0 < u i) ∧ (∑ i, u i) < 1
    exact ⟨hcoord, hsum⟩
  exact ⟨hnonempty, Set.Subset.antisymm hsubset hinter⟩


end HolomorphicAnosov
