import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.Linarith

/-! Local maximality from internal shadowing and ambient expansivity (Shub, Props. 8.21(b) and
8.22). -/

namespace HolomorphicAnosov

open Set

/-- An invariant set with internal shadowing is locally maximal for an expansive uniformly
continuous bijection (Shub, Props. 8.21(b) and 8.22(1)). -/
theorem smale_locallyMaximal_of_shadowing_of_expansive
    {X : Type*} [MetricSpace X] (e : X ≃ X) (A : Set X)
    (he : UniformContinuous (e : X → X)) (hA : e '' A = A)
    (c : ℝ) (hc : 0 < c)
    (hexp : ∀ x y : X, (∀ k : ℤ, dist ((e ^ k) x) ((e ^ k) y) < c) → x = y)
    (hshadow : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℤ → X, (∀ k, q k ∈ A) →
        (∀ k, dist (e (q k)) (q (k + 1)) < δ) →
        ∃ a ∈ A, ∀ k : ℤ, dist ((e ^ k) a) (q k) < ε) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧
      A = ⋂ k : ℤ, (fun x ↦ (e ^ k) x) '' U := by
  classical
  obtain ⟨δ, hδ, hshadowδ⟩ := hshadow (c / 3) (by linarith)
  obtain ⟨η, hη, hcont⟩ := Metric.uniformContinuous_iff.mp he (δ / 2) (by linarith)
  let r := min (c / 3) (min η (δ / 2))
  have hr : 0 < r := lt_min (by linarith) (lt_min hη (by linarith))
  have hrc : r ≤ c / 3 := min_le_left _ _
  have hrη : r ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Metric.thickening r A, Metric.isOpen_thickening,
    Metric.self_subset_thickening hr A, ?_⟩
  have hf : ∀ {x}, x ∈ A → e x ∈ A := by
    intro x hx
    rw [← hA]
    exact mem_image_of_mem e hx
  have hi : ∀ {x}, x ∈ A → e.symm x ∈ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hA.symm ▸ hx
    simpa using hy
  have hinv : ∀ (k : ℤ) {x}, x ∈ A → (e ^ k) x ∈ A := by
    intro k x hx
    exact zpow_induction_left (P := fun g : Equiv.Perm X ↦ g x ∈ A)
      hx (fun g hg ↦ hf hg) (fun g hg ↦ hi hg) k
  apply Subset.antisymm
  · intro x hx
    apply mem_iInter.mpr
    intro k
    refine ⟨(e ^ (-k)) x, Metric.self_subset_thickening hr A (hinv (-k) hx), ?_⟩
    change (e ^ k) ((e ^ (-k)) x) = x
    rw [← Equiv.Perm.mul_apply, ← zpow_add]
    simp
  · intro x hx
    have hU : ∀ k : ℤ, (e ^ k) x ∈ Metric.thickening r A := by
      intro k
      obtain ⟨y, hy, hxy⟩ := mem_iInter.mp hx (-k)
      have : (e ^ k) x = y := by
        rw [← hxy]
        rw [← Equiv.Perm.mul_apply, ← zpow_add]
        simp
      rwa [this]
    choose q hqA hqclose using fun k ↦ Metric.mem_thickening_iff.mp (hU k)
    have hjump : ∀ k, dist (e (q k)) (q (k + 1)) < δ := by
      intro k
      have heclose : dist (e (q k)) (e ((e ^ k) x)) < δ / 2 :=
        hcont (by rw [dist_comm]; exact (hqclose k).trans_le hrη)
      have hnext : e ((e ^ k) x) = (e ^ (k + 1)) x := by
        rw [show k + 1 = 1 + k by omega, zpow_add, zpow_one]
        rfl
      rw [hnext] at heclose
      exact (dist_triangle _ ((e ^ (k + 1)) x) _).trans_lt
        (by have := (hqclose (k + 1)).trans_le hrδ; linarith)
    obtain ⟨a, ha, has⟩ := hshadowδ q hqA hjump
    have hxa : x = a := hexp x a (fun k ↦ by
      have hqa : dist (q k) ((e ^ k) a) < c / 3 := by
        simpa only [dist_comm] using has k
      exact (dist_triangle _ (q k) _).trans_lt
        (by have := (hqclose k).trans_le hrc; linarith))
    rwa [hxa]

end HolomorphicAnosov

