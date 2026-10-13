import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.Real.Lemmas

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

/-- A point cannot belong to the original stable point sets of two distinct
periodic labels. The distance triangle first makes those labels asymptotic;
the constant common-period subsequence then identifies them. -/
theorem periodic_label_unique {M : Type*} [MetricSpace M]
    {f : M → M} {x y z : M} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hx : (f^[m]) x = x) (hy : (f^[n]) y = y)
    (hxz : ForwardAsymptotic f x z) (hyz : ForwardAsymptotic f y z) : x = y := by
  have hmult : Tendsto (fun k : ℕ ↦ (m * n) * k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ Nat.le_mul_of_pos_left k (Nat.mul_pos hm hn)) tendsto_id
  have hxk (k : ℕ) : (f^[m * n * k]) x = x := by
    rw [Nat.mul_assoc, Function.iterate_mul]
    exact Function.iterate_fixed hx (n * k)
  have hyk (k : ℕ) : (f^[m * n * k]) y = y := by
    rw [Nat.mul_comm m n, Nat.mul_assoc, Function.iterate_mul]
    exact Function.iterate_fixed hy (m * k)
  have hzy : Tendsto (fun k : ℕ ↦ dist ((f^[k]) y) ((f^[k]) z)) atTop (𝓝 0) := by
    simpa only [ForwardAsymptotic, dist_comm] using hyz
  have hdist : Tendsto (fun k : ℕ ↦ dist ((f^[k]) y) ((f^[k]) x)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ dist_nonneg)
      (fun k ↦ dist_triangle ((f^[k]) y) ((f^[k]) z) ((f^[k]) x))
    simpa only [add_zero] using hzy.add hxz
  have hzero : Tendsto (fun _ : ℕ ↦ dist y x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hxk, hyk] using hdist.comp hmult
  exact (dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero)).symm

end HolomorphicAnosov.StableFoliationsSupport
