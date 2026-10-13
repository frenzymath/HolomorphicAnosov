import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Continuous endpoints from compatible skeletal stages

Source: Hatcher, *Algebraic Topology*, Theorem 4.8, pp. 349–351,
especially the eventual stationarity and characteristic-prism continuity
argument, together with Appendix A.17, pp. 532–533.
-/

namespace HolomorphicAnosov.Topology.CWComplex

universe u v

open Set

/-- Successive maps which fix each completed skeleton have a unique continuous
cellular endpoint. Source: Hatcher Theorem 4.8, pp.349–350, the endpoint of the
skeletal homotopies.

For a point in the n-skeleton, induction gives equality of every stage from n
onward with stage n. Choose a skeleton for each point; comparing two choices at
their maximum proves independence and agreement on every skeleton. On a closed
characteristic n-cell the endpoint equals the continuous stage n, so the
characteristic continuity criterion applies. Cellularity follows on each
skeleton, and exhaustion proves uniqueness. This includes an empty source and
arbitrarily many cells and dimensions. -/
theorem stationary_skeletal_cellular_endpoint
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set K)] [Topology.CWComplex (Set.univ : Set Y)]
    (F : ℕ → C(K, Y))
    (hstep : ∀ (n : ℕ) (x : K),
      x ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) →
      F (n + 1) x = F n x)
    (hcell : ∀ n : ℕ, MapsTo (F n)
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) :
    ∃! c : C(K, Y),
      (∀ (n : ℕ) (x : K),
        x ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) →
        c x = F n x) ∧
      (∀ n : ℕ, MapsTo c
        (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
        (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) := by
  classical
  let S : ℕ → Set K := fun n ↦
    (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
  have hcover : ∀ x : K, ∃ n : ℕ, x ∈ S n := by
    intro x
    have hx : x ∈ ⋃ n : ℕ, S n := by
      rw [show (⋃ n : ℕ, S n) = Set.univ from
        Topology.CWComplex.iUnion_skeleton_eq_complex]
      exact Set.mem_univ _
    exact Set.mem_iUnion.mp hx
  have hcompat (m n : ℕ) (hmn : m ≤ n) (x : K) (hx : x ∈ S m) : F n x = F m x := by
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      exact (hstep n x (Topology.CWComplex.skeleton_mono
        (by exact_mod_cast hmn) hx)).trans ih
  let index : K → ℕ := fun x ↦ (hcover x).choose
  have hindex : ∀ x, x ∈ S (index x) := fun x ↦ (hcover x).choose_spec
  let c : K → Y := fun x ↦ F (index x) x
  have hagree : ∀ n x, x ∈ S n → c x = F n x := by
    intro n x hx
    exact (hcompat (index x) (max (index x) n) (le_max_left _ _) x (hindex x)).symm.trans
      (hcompat n (max (index x) n) (le_max_right _ _) x hx)
  have hc : Continuous c := by
    apply HolomorphicAnosov.cw_continuous_of_characteristic
    intro n i
    have hc' := (F n).continuous.comp (Topology.RelCWComplex.continuousOn n i).domRestrict
    convert hc' using 1
    funext z
    exact hagree n _ (Topology.CWComplex.closedCell_subset_skeleton n i
      ⟨z.val, z.property, rfl⟩)
  refine ⟨⟨c, hc⟩, ⟨hagree, ?_⟩, ?_⟩
  · intro n x hx
    change c x ∈ _
    rw [hagree n x hx]
    exact hcell n hx
  · intro c' hc'
    apply ContinuousMap.ext
    intro x
    obtain ⟨n, hx⟩ := hcover x
    exact (hc'.1 n x hx).trans (hagree n x hx).symm


end HolomorphicAnosov.Topology.CWComplex
