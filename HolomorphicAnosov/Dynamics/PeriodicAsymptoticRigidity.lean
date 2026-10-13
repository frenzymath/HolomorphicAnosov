import HolomorphicAnosov.Dynamics.AsymptoticLeaf

/-!
Periodic-label consequences of the asymptotic-set partition in
`zhang.stable_foliations`, proof step 25. The direct metric arguments are
agent-written. Shub, Global Stability of Dynamical Systems (1987),
Definition 2.1, pp.8–9 supplies the asymptotic-set definition; no separately
printed periodic-rigidity result is claimed.
-/

noncomputable section
open Filter Set _root_.Topology
namespace HolomorphicAnosov.StableFoliationsSupport

/-- Two periodic point labels cannot be asymptotic unless they coincide.
Restrict to multiples of the product of their positive periods. Both orbits
then remain at their original points, so their constant distance tends to zero.
No dynamical regularity or compactness hypothesis is used. -/
theorem periodic_eq_of_forwardAsymptotic {M : Type*} [MetricSpace M]
    {f : M → M} {x y : M} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hx : (f^[m]) x = x) (hy : (f^[n]) y = y)
    (h : ForwardAsymptotic f x y) : x = y := by
  have hmult : Tendsto (fun k : ℕ ↦ (m * n) * k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_mul_of_pos_left k (Nat.mul_pos hm hn)) tendsto_id
  have hxk (k : ℕ) : (f^[m * n * k]) x = x := by
    rw [Nat.mul_assoc, Function.iterate_mul]
    exact Function.iterate_fixed hx (n * k)
  have hyk (k : ℕ) : (f^[m * n * k]) y = y := by
    rw [Nat.mul_comm m n, Nat.mul_assoc, Function.iterate_mul]
    exact Function.iterate_fixed hy (m * k)
  have hzero : Tendsto (fun _ : ℕ ↦ dist y x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hxk, hyk] using h.comp hmult
  exact (dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero)).symm

end HolomorphicAnosov.StableFoliationsSupport
