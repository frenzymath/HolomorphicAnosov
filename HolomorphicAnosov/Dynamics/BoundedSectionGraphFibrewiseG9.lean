import HolomorphicAnosov.Dynamics.HirschPughRestrictedSplitting
import Mathlib.Tactic

/-!
# Fibre dependence of a bounded-section stable graph

Source: Shub, Global Stability of Dynamical Systems (1987), Lemma 6.5,
pp.75–77. The proof pastes two actual retained graph orbits at the moving
basepoint and uses the original graph's bounded-orbit characterization.
-/

namespace HolomorphicAnosov
open HirschRestrictedCoordinates

/-- A stable graph for a pointwise section operator depends only on the input
in the evaluated fibre. Paste two retained graph orbits at σ^n(p), using one
orbit at that point and the other elsewhere. Pasting never increases the norm
beyond the maximum of the two norms. Pointwise dependence of the operator and
bijectivity of σ make the pasted sequence an actual orbit. Its initial stable
section is the first input when both inputs agree at p. Graph capture then
identifies its unstable section with the first graph value; evaluation at p
is the second graph value by the definition of pasting. -/
theorem bounded_section_graph_fibrewise
    {A : Type*} {V : A → Type*}
    [∀ p, NormedAddCommGroup (V p)] [∀ p, NormedSpace ℝ (V p)]
    (U S : ∀ p, Submodule ℝ (V p)) (σ : A ≃ A)
    (g : boundedSectionSubmodule U × boundedSectionSubmodule S →
      boundedSectionSubmodule U × boundedSectionSubmodule S)
    (v : boundedSectionSubmodule S → boundedSectionSubmodule U)
    (r : ℝ)
    (hretained : ∀ s : boundedSectionSubmodule S, ‖s‖ < r →
      ∀ n : ℕ, ‖g^[n] (v s, s)‖ < r)
    (hcapture : ∀ w : ℕ → boundedSectionSubmodule U × boundedSectionSubmodule S,
      (∀ n, ‖w n‖ < r) → (∀ n, g (w n) = w (n + 1)) → (w 0).1 = v (w 0).2)
    (hlocal : ∀ w, ‖w‖ < r → ∀ z, ‖z‖ < r → ∀ p : A,
      w.1.val p = z.1.val p → w.2.val p = z.2.val p →
      (g w).1.val (σ p) = (g z).1.val (σ p) ∧
      (g w).2.val (σ p) = (g z).2.val (σ p))
    (s t : boundedSectionSubmodule S) (hs : ‖s‖ < r) (ht : ‖t‖ < r)
    (p : A) (hp : s.val p = t.val p) : (v s).val p = (v t).val p := by
  classical
  let paste (W : ∀ p, Submodule ℝ (V p)) (p : A)
      (a b : boundedSectionSubmodule W) : boundedSectionSubmodule W :=
    ⟨lp.single ⊤ p (b.val p - a.val p) + a.val, by
      intro q
      by_cases hq : q = p
      · subst q
        simpa using b.property p
      · simpa [Pi.single_eq_of_ne hq] using a.property q⟩
  have hpaste_same (W : ∀ p, Submodule ℝ (V p)) (q : A)
      (a b : boundedSectionSubmodule W) : (paste W q a b).val q = b.val q := by
    simp [paste]
  have hpaste_ne (W : ∀ p, Submodule ℝ (V p)) (q k : A)
      (a b : boundedSectionSubmodule W) (hk : k ≠ q) :
      (paste W q a b).val k = a.val k := by
    simp [paste, Pi.single_eq_of_ne hk]
  have hpaste_norm (W : ∀ p, Submodule ℝ (V p)) (q : A)
      (a b : boundedSectionSubmodule W) : ‖paste W q a b‖ ≤ max ‖a‖ ‖b‖ := by
    apply lp.norm_le_of_forall_le (le_max_of_le_left (norm_nonneg _))
    intro k
    change ‖(paste W q a b).val k‖ ≤ max ‖a‖ ‖b‖
    by_cases hk : k = q
    · subst k
      rw [hpaste_same]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero b.val q).trans (le_max_right _ _)
    · rw [hpaste_ne W q k a b hk]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero a.val k).trans (le_max_left _ _)
  let P := boundedSectionSubmodule U × boundedSectionSubmodule S
  let a : ℕ → P := fun n ↦ g^[n] (v s, s)
  let b : ℕ → P := fun n ↦ g^[n] (v t, t)
  let q : ℕ → A := fun n ↦ (σ : A → A)^[n] p
  let w : ℕ → P := fun n ↦
    (paste U (q n) (a n).1 (b n).1, paste S (q n) (a n).2 (b n).2)
  have hwm (n : ℕ) : ‖w n‖ < r := by
    rw [Prod.norm_def]
    apply max_lt
    · exact (hpaste_norm U (q n) (a n).1 (b n).1).trans_lt (max_lt
        ((norm_fst_le (a n)).trans_lt (hretained s hs n))
        ((norm_fst_le (b n)).trans_lt (hretained t ht n)))
    · exact (hpaste_norm S (q n) (a n).2 (b n).2).trans_lt (max_lt
        ((norm_snd_le (a n)).trans_lt (hretained s hs n))
        ((norm_snd_le (b n)).trans_lt (hretained t ht n)))
  have hrec (n : ℕ) : g (w n) = w (n + 1) := by
    have hq : q (n + 1) = σ (q n) := Function.iterate_succ_apply' _ _ _
    have ha : g (a n) = a (n + 1) := (Function.iterate_succ_apply' _ _ _).symm
    have hb : g (b n) = b (n + 1) := (Function.iterate_succ_apply' _ _ _).symm
    have heq (k : A) :
        (g (w n)).1.val k = (w (n + 1)).1.val k ∧
        (g (w n)).2.val k = (w (n + 1)).2.val k := by
      obtain ⟨j, rfl⟩ := σ.surjective k
      by_cases hj : j = q n
      · subst j
        have hh := hlocal (w n) (hwm n) (b n) (hretained t ht n) (q n)
          (hpaste_same U (q n) (a n).1 (b n).1)
          (hpaste_same S (q n) (a n).2 (b n).2)
        rw [hb] at hh
        simpa only [w, hq, hpaste_same] using hh
      · have hk : σ j ≠ q (n + 1) := by rw [hq]; exact σ.injective.ne hj
        have hh := hlocal (w n) (hwm n) (a n) (hretained s hs n) j
          (hpaste_ne U (q n) j (a n).1 (b n).1 hj)
          (hpaste_ne S (q n) j (a n).2 (b n).2 hj)
        rw [ha] at hh
        simpa only [w, hpaste_ne U (q (n + 1)) (σ j) _ _ hk,
          hpaste_ne S (q (n + 1)) (σ j) _ _ hk] using hh
    apply Prod.ext
    · apply Subtype.ext
      apply lp.ext
      funext k
      exact (heq k).1
    · apply Subtype.ext
      apply lp.ext
      funext k
      exact (heq k).2
  have hwzero : (w 0).2 = s := by
    apply Subtype.ext
    apply lp.ext
    funext k
    by_cases hk : k = p
    · subst k
      exact (hpaste_same S p s t).trans hp.symm
    · exact hpaste_ne S p k s t hk
  have hcapt := hcapture w hwm hrec
  rw [hwzero] at hcapt
  have heval := congrArg (fun z : boundedSectionSubmodule U ↦ z.val p) hcapt
  exact heval.symm.trans (hpaste_same U p (v s) (v t))

end HolomorphicAnosov

