import HolomorphicAnosov.Topology.Cubical.ClosedCoordinateCell
import Mathlib.Tactic

namespace HolomorphicAnosov.Cubical

/-- Every positive-dimensional coordinate cell has a boundary patch equal to a coordinate plane.
Source: Hatcher, Algebraic Topology, Appendix A.2 p.521, coordinate-face construction;
Dold, Fixed point index and fixed point theorem for Euclidean neighborhood retracts,
§5 Step 3, p.7. Choose an active coordinate at its lower endpoint and take midpoints
in all other coordinates. The open conditions that the other active coordinates remain
strictly between their endpoints, and that the chosen coordinate is below its upper
endpoint, hold at this point. A sufficiently small metric ball satisfies them all.
A boundary point in this ball must therefore have the chosen coordinate at its lower
endpoint; all degenerate coordinates are fixed by membership in the cell. Conversely,
these fixed-coordinate equations imply membership in that face. Removing the chosen
coordinate from the active set leaves exactly q free coordinates. -/
theorem cell_boundary_local_flat_patch {N q : ℕ} (c : ClosedCoordinateCell N)
    (hd : c.dimension = q + 1) :
    ∃ J : Finset (Fin N), J.card = q ∧
      ∃ p ∈ {x : Fin N → ℝ | x ∈ c.carrier ∧ ∃ i : Fin N,
        c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)},
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin N → ℝ, dist x p < δ →
        ((x ∈ c.carrier ∧ ∃ i : Fin N,
          c.lower i < c.upper i ∧ (x i = c.lower i ∨ x i = c.upper i)) ↔
          ∀ i : Fin N, i ∉ J → x i = p i) := by
  classical
  let A : Finset (Fin N) := {i | c.lower i < c.upper i}.toFinset
  have hA : A.card = q + 1 := by
    simpa only [ClosedCoordinateCell.dimension, Set.ncard_eq_toFinset_card'] using hd
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have hi : c.lower i₀ < c.upper i₀ := by simpa [A] using hi₀
  let J := A.erase i₀
  let p : Fin N → ℝ := Function.update (fun i ↦ (c.lower i + c.upper i) / 2) i₀ (c.lower i₀)
  have hp0 : p i₀ = c.lower i₀ := by simp [p]
  have hpj : ∀ i, i ≠ i₀ → p i = (c.lower i + c.upper i) / 2 := by
    intro i hi'; simp [p, hi']
  have hp : p ∈ c.carrier := by
    constructor <;> intro i <;> by_cases hii : i = i₀
    · subst i; simp [hp0]
    · rw [hpj i hii]; linarith [c.lower_le_upper i]
    · subst i; rw [hp0]; exact hi.le
    · rw [hpj i hii]; linarith [c.lower_le_upper i]
  let U : Set (Fin N → ℝ) :=
    {x | x i₀ < c.upper i₀} ∩ ⋂ i ∈ J, {x | c.lower i < x i ∧ x i < c.upper i}
  have hU : IsOpen U := by
    apply IsOpen.inter (isOpen_lt (continuous_apply i₀) continuous_const)
    apply isOpen_biInter_finset
    intro i hi'
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)
  have hpU : p ∈ U := by
    refine ⟨by simpa [hp0] using hi, ?_⟩
    simp only [Set.mem_iInter]
    intro i hij
    have hiA : c.lower i < c.upper i := by simpa [A] using (Finset.mem_erase.mp hij).2
    change c.lower i < p i ∧ p i < c.upper i
    rw [hpj i (Finset.mem_erase.mp hij).1]
    constructor <;> linarith
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU p hpU
  refine ⟨J, ?_, p, ⟨hp, i₀, hi, Or.inl hp0⟩, δ, hδ, ?_⟩
  · dsimp [J]
    rw [Finset.card_erase_of_mem hi₀, hA]
    omega
  · intro x hx
    have hxU := hδU hx
    have hxj : ∀ i ∈ J, c.lower i < x i ∧ x i < c.upper i := by
      intro i hi
      have hi' := Set.mem_iInter.mp hxU.2 i
      exact Set.mem_iInter.mp hi' hi
    constructor
    · rintro ⟨hxc, k, hk, hxk⟩ i hij
      by_cases hii : i = i₀
      · subst i
        have hki : k = i₀ := by
          by_contra hki
          have hkJ : k ∈ J := Finset.mem_erase.mpr ⟨hki, by simpa [A] using hk⟩
          obtain ⟨hkl, hku⟩ := hxj k hkJ
          rcases hxk with hxk | hxk <;> linarith
        subst k
        rw [hp0]
        rcases hxk with hxk | hxk
        · exact hxk
        · exact (ne_of_lt hxU.1 hxk).elim
      · have hiA : i ∉ A := by
          intro hiA; exact hij (Finset.mem_erase.mpr ⟨hii, hiA⟩)
        have hn : ¬ c.lower i < c.upper i := by simpa [A] using hiA
        have he : c.lower i = c.upper i := le_antisymm (c.lower_le_upper i) (le_of_not_gt hn)
        have hxi : x i = c.lower i := le_antisymm (he ▸ hxc.2 i) (hxc.1 i)
        calc
          x i = c.lower i := hxi
          _ = (c.lower i + c.upper i) / 2 := by rw [he]; ring
          _ = p i := (hpj i hii).symm
    · intro hxplane
      have hx0 : x i₀ = c.lower i₀ := by
        rw [← hp0]; apply hxplane; simp [J]
      refine ⟨?_, i₀, hi, Or.inl hx0⟩
      constructor <;> intro i <;> by_cases hij : i ∈ J
      · exact (hxj i hij).1.le
      · rw [hxplane i hij]; exact hp.1 i
      · exact (hxj i hij).2.le
      · rw [hxplane i hij]; exact hp.2 i

end HolomorphicAnosov.Cubical

