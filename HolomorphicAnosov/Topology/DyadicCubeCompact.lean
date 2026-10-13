import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

namespace HolomorphicAnosov

open Set Topology _root_.Topology

/-- Every finite-dimensional closed dyadic coordinate cube is compact.

Source: Hatcher, Algebraic Topology, proof of Theorem A.7, pp. 525–526,
where selected dyadic cubes are treated as compact coordinate boxes. The
statement is an explicit Mathlib specialization: transport the finite product
of compact real intervals along the canonical `EuclideanSpace.equiv` and use
its coordinate identities. Degenerate intervals and `Fin 0` are included.
-/
theorem dyadic_cube_compact {N : ℕ} (k : ℕ) (m : Fin N → ℤ) :
    IsCompact {x : EuclideanSpace ℝ (Fin N) | ∀ j,
      (m j : ℝ) / (2 : ℝ) ^ k ≤ x j ∧
        x j ≤ ((m j : ℝ) + 1) / (2 : ℝ) ^ k} := by
  let e := EuclideanSpace.equiv (Fin N) ℝ
  let B : Set (Fin N → ℝ) := Set.Icc (fun j => (m j : ℝ) / (2 : ℝ) ^ k)
    (fun j => ((m j : ℝ) + 1) / (2 : ℝ) ^ k)
  have hB : IsCompact B := by
    dsimp [B]
    rw [← pi_univ_Icc]
    exact isCompact_univ_pi fun j ↦
      ConditionallyCompleteLinearOrder.isCompact_Icc _ _
  have hmap : IsCompact (e.symm '' B) := hB.image e.symm.continuous
  have heq : (e.symm : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) '' B =
      {x : EuclideanSpace ℝ (Fin N) | ∀ j,
      (m j : ℝ) / (2 : ℝ) ^ k ≤ x j ∧
        x j ≤ ((m j : ℝ) + 1) / (2 : ℝ) ^ k} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      dsimp [B] at hy
      rw [← pi_univ_Icc] at hy
      change ∀ j, (m j : ℝ) / (2 : ℝ) ^ k ≤ y j ∧
        y j ≤ ((m j : ℝ) + 1) / (2 : ℝ) ^ k
      simpa only [Set.mem_univ_pi, Set.mem_Icc] using hy
    · intro hx
      have hx' : e x ∈ B := by
        dsimp [B]
        rw [← pi_univ_Icc]
        apply Set.mem_univ_pi.mpr
        intro j
        apply Set.mem_Icc.mpr
        exact hx j
      exact ⟨e x, hx', e.symm_apply_apply x⟩
  rw [← heq]
  exact hmap


end HolomorphicAnosov
