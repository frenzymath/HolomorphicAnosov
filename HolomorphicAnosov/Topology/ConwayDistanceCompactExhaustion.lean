import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-!
# Conway's distance-and-radius compact sets

Source: Conway, Functions of One Complex Variable I, second edition,
Chapter VII Proposition 1.2, printed p.143, first two paragraphs of the proof.
-/

open Set Metric

namespace HolomorphicAnosov

/-- The literal distance-and-radius sets in Conway VII.1.2 form an interior-nested,
compact-cofinal exhaustion when the open domain has nonempty complement.

Source: Conway, VII.1.2, p.143. Distance is continuous, so each set is closed and
bounded, hence compact. Positive distance excludes the complement. The strict
inequalities at index `n+1` define an open neighborhood of the preceding set.
For any point of the domain, distance to the closed complement is positive;
choose an integer larger than both its norm and the reciprocal distance.
Thus the interiors cover. A finite directed subcover covers each compact subset.
The empty open domain is allowed; all its exhaustion sets are empty. -/
theorem conway_distance_compact_exhaustion
    (U : Set ℂ) (hU : IsOpen U) (hUc : Uᶜ.Nonempty) :
    let K : ℕ+ → Set ℂ := fun n ↦
      {z | ‖z‖ ≤ (n : ℝ) ∧ 1 / (n : ℝ) ≤ infDist z Uᶜ}
    (∀ n, IsCompact (K n) ∧ K n ⊆ U) ∧
      (⋃ n, K n) = U ∧
      (∀ n, K n ⊆ interior (K (n + 1))) ∧
      (∀ C : Set ℂ, IsCompact C → C ⊆ U → ∃ n, C ⊆ K n) := by
  classical
  dsimp only
  let K : ℕ+ → Set ℂ := fun n ↦
    {z | ‖z‖ ≤ (n : ℝ) ∧ 1 / (n : ℝ) ≤ infDist z Uᶜ}
  have hnpos (n : ℕ+) : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hKU (n : ℕ+) : K n ⊆ U := by
    intro z hz
    by_contra hzU
    have hzdist : infDist z Uᶜ = 0 := infDist_zero_of_mem hzU
    have := hz.2
    rw [hzdist] at this
    exact (one_div_pos.mpr (hnpos n)).not_ge this
  have hcompact (n : ℕ+) : IsCompact (K n) := by
    apply (isCompact_closedBall (0 : ℂ) (n : ℝ)).of_isClosed_subset
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const (continuous_infDist_pt _))
    · intro z hz
      simpa only [mem_closedBall, dist_zero_right] using hz.1
  have hstrict (n : ℕ+) : {z : ℂ | ‖z‖ < (n : ℝ) ∧ 1 / (n : ℝ) < infDist z Uᶜ}
      ⊆ interior (K n) := by
    have hopen : IsOpen {z : ℂ | ‖z‖ < (n : ℝ) ∧
        1 / (n : ℝ) < infDist z Uᶜ} :=
      (isOpen_lt continuous_norm continuous_const).inter
        (isOpen_lt continuous_const (continuous_infDist_pt _))
    exact hopen.subset_interior_iff.mpr (fun _ h ↦ ⟨h.1.le, h.2.le⟩)
  have hnest (n : ℕ+) : K n ⊆ interior (K (n + 1)) := by
    intro z hz
    apply hstrict
    have hnext : (n : ℝ) < ((n + 1 : ℕ+) : ℝ) := by exact_mod_cast Nat.lt_succ_self (n : ℕ)
    exact ⟨hz.1.trans_lt hnext,
      (one_div_lt_one_div_of_lt (hnpos n) hnext).trans_le hz.2⟩
  have hmono : Monotone K := by
    intro n m hnm z hz
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact ⟨hz.1.trans hnm', (one_div_le_one_div_of_le (hnpos n) hnm').trans hz.2⟩
  have hcover : U ⊆ ⋃ n, interior (K n) := by
    intro z hz
    have hd : 0 < infDist z Uᶜ :=
      (hU.isClosed_compl.notMem_iff_infDist_pos hUc).mp (by simpa)
    obtain ⟨N, hN⟩ := exists_nat_gt (max ‖z‖ (1 / infDist z Uᶜ))
    let n : ℕ+ := ⟨N + 1, Nat.succ_pos _⟩
    have hNn : (N : ℝ) < (n : ℝ) := by dsimp [n]; norm_cast; exact Nat.lt_succ_self N
    have hnorm : ‖z‖ < (n : ℝ) := (le_max_left _ _).trans_lt (hN.trans hNn)
    have hinv : 1 / infDist z Uᶜ < (n : ℝ) :=
      (le_max_right _ _).trans_lt (hN.trans hNn)
    have hdist : 1 / (n : ℝ) < infDist z Uᶜ := by
      apply (div_lt_iff₀ (hnpos n)).mpr
      have := (div_lt_iff₀ hd).mp hinv
      simpa only [mul_comm] using this
    exact mem_iUnion.mpr ⟨n, hstrict n ⟨hnorm, hdist⟩⟩
  refine ⟨fun n ↦ ⟨hcompact n, hKU n⟩, ?_, hnest, ?_⟩
  · exact subset_antisymm (iUnion_subset hKU)
      (hcover.trans (iUnion_mono fun _ ↦ interior_subset))
  · intro C hC hCU
    obtain ⟨n, hn⟩ := hC.elim_directed_cover (fun n ↦ interior (K n))
      (fun _ ↦ isOpen_interior) (hCU.trans hcover)
      (fun n m ↦ ⟨max n m, interior_mono (hmono (le_max_left _ _)),
        interior_mono (hmono (le_max_right _ _))⟩)
    exact ⟨n, hn.trans interior_subset⟩

end HolomorphicAnosov
