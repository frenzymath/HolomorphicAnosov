import HolomorphicAnosov.Topology.CWComplex.SkeletalEndpoint
import HolomorphicAnosov.Topology.CWComplex.RelativeHomotopyCompatibleSkeleta

namespace HolomorphicAnosov.Topology.CWComplex

universe u v

/-- The assembly step of Hatcher's cellular approximation, Theorem 4.8,
pp.349–351: compatible finite-stage relative homotopies have a continuous
cellular endpoint and a single relative homotopy with exactly the same
tracks on each completed skeleton.

Proof: evaluation at time one makes the stage maps stationary on completed
skeleta, so the stationary endpoint theorem constructs the continuous
cellular map. Restrict each stage homotopy to its completed skeleton.
Induction on later stages proves equality of these entire restricted
homotopies, since skeletal inclusion makes each intervening stationarity
hypothesis applicable. Their initial, terminal and relative-set identities
then descend by relative compatible-skeleton gluing. No uniform bound on
cell dimensions or local finiteness is needed; the empty source and either
extreme choice of the fixed set are allowed. -/
theorem stationary_skeletal_cellular_homotopy
    {K : Type u} {Y : Type v} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set K)] [Topology.CWComplex (Set.univ : Set Y)]
    (A : Set K) (f : C(K, Y)) (F : ℕ → C(K, Y))
    (H : ∀ n, ContinuousMap.HomotopyRel f (F n) A)
    (hstep : ∀ (n : ℕ) (t : unitInterval) (x : K),
      x ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) →
      H (n + 1) (t, x) = H n (t, x))
    (hcell : ∀ n : ℕ, Set.MapsTo (F n)
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) :
    ∃ c : C(K, Y),
      (∀ n : ℕ, Set.MapsTo c
        (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K)
        (Topology.CWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) ∧
      ∃ G : ContinuousMap.HomotopyRel f c A, ∀ (n : ℕ) t x,
        x ∈ (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K) →
        G (t, x) = H n (t, x) := by
  obtain ⟨c, ⟨hc, hccell⟩, _⟩ := stationary_skeletal_cellular_endpoint F
    (fun n x hx ↦ by simpa using hstep n 1 x hx) hcell
  let R : ∀ n : ℕ, C(unitInterval ×
      (Topology.CWComplex.skeleton (Set.univ : Set K) (n : ℕ∞) : Set K), Y) :=
    fun n ↦ ⟨fun q ↦ H n (q.1, q.2.val),
      (H n).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  obtain ⟨G, hG⟩ := HolomorphicAnosov.cw_relative_homotopy_of_compatible_skeleta
    A f c R (fun n x ↦ (H n).map_zero_left x.val)
    (fun n x ↦ ((H n).map_one_left x.val).trans (hc n x.val x.property).symm)
    (fun n t x hx ↦ (H n).prop t x.val hx) (by
      intro m n hmn t x
      change H m (t, x.val) = H n (t, x.val)
      induction n, hmn using Nat.le_induction with
      | base => rfl
      | succ n hmn ih =>
        exact ih.trans (hstep n t x.val (Topology.CWComplex.skeleton_mono
          (by exact_mod_cast hmn) x.property)).symm)
  exact ⟨c, hccell, G, fun n t x hx ↦ hG n t ⟨x, hx⟩⟩

end HolomorphicAnosov.Topology.CWComplex
