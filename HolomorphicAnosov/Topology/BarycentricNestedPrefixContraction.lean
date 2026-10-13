import HolomorphicAnosov.Topology.BarycentricIteratedMeshDefs
import HolomorphicAnosov.Topology.CentroidDistanceBound

noncomputable section
namespace HolomorphicAnosov.BarycentricMesh

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- The prefix barycenters contract pairwise distances by `n/(n+1)`.
This is the finite nested-prefix centroid estimate used in Hatcher's Proposition 2.21,
p.120. The finite nested-prefix argument expands the centroid estimate as follows.
For indices i ≤ j, every vertex of the i-prefix belongs to the j-prefix. In its
average distance to that vertex, the j-prefix has a zero self-distance term and
at most card(j-prefix)−1 terms bounded by D. Average this estimate over the
nonempty i-prefix and use card(j-prefix) ≤ n+1 and D ≥ 0. Symmetry handles j ≤ i.
This calculation includes n=0 and repeated vertices without extra assumptions. -/
theorem child_vertices_dist_le_ratio {n : ℕ}
    (w : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))) (D : ℝ)
    (hD : ∀ i j : Fin (n + 1), dist (w i) (w j) ≤ D) :
    ∀ i j, dist (childVertices w σ i) (childVertices w σ j) ≤
      ((n : ℝ) / ((n : ℝ) + 1)) * D := by
  have hforward : ∀ i j : Fin (n+1), i ≤ j →
      dist (childVertices w σ i) (childVertices w σ j) ≤
        ((n : ℝ) / ((n : ℝ) + 1)) * D := by
    intro i j hij
    let si : Finset (Fin (n+1)) := Finset.univ.filter (fun k ↦ k ≤ i)
    let sj : Finset (Fin (n+1)) := Finset.univ.filter (fun k ↦ k ≤ j)
    have hsi : si.Nonempty := by
      exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩⟩
    have hsj : sj.Nonempty := by
      exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.zero_le _⟩⟩
    have hsub : si ⊆ sj := by
      intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        le_trans (Finset.mem_filter.mp hk).2 hij⟩
    have houter := centroid_dist_le_average si hsi (w ∘ σ)
      (sj.centroid ℝ (w ∘ σ))
    have hinner : ∀ k ∈ si,
        dist (sj.centroid ℝ (w ∘ σ)) (w (σ k)) ≤
          ((sj.card : ℝ) - 1) / sj.card * D := by
      intro k hk
      have hkj : k ∈ sj := hsub hk
      have hsum : ∑ l ∈ sj, dist (w (σ l)) (w (σ k)) ≤
          ((sj.card : ℝ) - 1) * D := by
        rw [← Finset.sum_erase_add sj
          (fun l ↦ dist (w (σ l)) (w (σ k))) hkj]
        have hsum' := (sj.erase k).sum_le_card_nsmul
          (fun l ↦ dist (w (σ l)) (w (σ k))) D (by
            intro l hl
            exact hD _ _)
        rw [Finset.card_erase_of_mem hkj] at hsum'
        norm_num [Nat.cast_smul_eq_nsmul,
          Nat.cast_sub (Finset.card_pos.mpr hsj).le] at hsum'
        have hcast : ((sj.card - 1 : ℕ) : ℝ) = (sj.card : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.succ_le_iff.2 (Finset.card_pos.mpr hsj))]
          norm_num
        rw [hcast] at hsum'
        simpa only [dist_self, add_zero] using hsum'
      have hh := centroid_dist_le_average sj hsj (w ∘ σ) (w (σ k))
      dsimp only [Function.comp_apply] at hh
      calc
        dist (sj.centroid ℝ (w ∘ σ)) (w (σ k)) ≤
            (sj.card : ℝ)⁻¹ * ∑ l ∈ sj,
              dist (w (σ l)) (w (σ k)) := hh
        _ ≤ (sj.card : ℝ)⁻¹ * (((sj.card : ℝ) - 1) * D) := by gcongr
        _ = ((sj.card : ℝ) - 1) / sj.card * D := by
          rw [div_eq_mul_inv]
          ring
    have hsumouter := si.sum_le_card_nsmul
      (fun k ↦ dist ((w ∘ σ) k) (sj.centroid ℝ (w ∘ σ)))
      (((sj.card : ℝ) - 1) / sj.card * D) (by
        intro k hk
        simpa [dist_comm] using hinner k hk)
    have houter' : dist (si.centroid ℝ (w ∘ σ))
        (sj.centroid ℝ (w ∘ σ)) ≤
          ((sj.card : ℝ) - 1) / sj.card * D := by
      apply le_trans houter
      have hsumouter' : ∑ k ∈ si,
          dist ((w ∘ σ) k) (sj.centroid ℝ (w ∘ σ)) ≤
            (si.card : ℝ) * (((sj.card : ℝ) - 1) / sj.card * D) := by
        simpa [Nat.cast_smul_eq_nsmul] using hsumouter
      calc
        (si.card : ℝ)⁻¹ * ∑ k ∈ si,
            dist ((w ∘ σ) k) (sj.centroid ℝ (w ∘ σ)) ≤
            (si.card : ℝ)⁻¹ * ((si.card : ℝ) *
              (((sj.card : ℝ) - 1) / sj.card * D)) :=
          mul_le_mul_of_nonneg_left hsumouter'
            (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = ((sj.card : ℝ) - 1) / sj.card * D := by
          field_simp [ne_of_gt
            (by exact_mod_cast (Finset.card_pos.mpr hsi))]
    have hD0 : 0 ≤ D := le_trans dist_nonneg (hD 0 0)
    have hsj_le : sj.card ≤ n + 1 := by
      exact (Finset.card_filter_le Finset.univ _).trans_eq (by simp)
    have hratio : ((sj.card : ℝ) - 1) / sj.card ≤
        (n : ℝ) / ((n : ℝ) + 1) := by
      have hr : (0 : ℝ) < sj.card := by
        exact_mod_cast (Finset.card_pos.mpr hsj)
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      apply (div_le_div_iff₀ hr hn).2
      have hsj_le' : (sj.card : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast hsj_le
      nlinarith
    exact houter'.trans (mul_le_mul_of_nonneg_right hratio hD0)
  intro i j
  rcases le_total i j with hij | hji
  · exact hforward i j hij
  · simpa [dist_comm] using hforward j i hji

end HolomorphicAnosov.BarycentricMesh
