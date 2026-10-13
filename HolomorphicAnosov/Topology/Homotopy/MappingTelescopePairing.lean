import HolomorphicAnosov.Topology.Homotopy.MappingTelescopeSequence
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Data.Nat.EvenOddRec

/-! # Pairing consecutive mapping-telescope bonds
Source: Hatcher, *Algebraic Topology*, Proposition A.11(3), p.528.
-/

universe u

namespace HolomorphicAnosov.MappingTelescope.Sequence

open ContinuousMap

/-- Pairing successive bonds preserves the homotopy type of the ordinary
mapping telescope, without restrictions on its spaces or bonding maps.

Source: Hatcher, Proposition A.11(3), p.528, and Proposition 0.18, p.16.
The following explicit coordinate verification of the source's cylinder slide
is agent-written. Write H_n(t,x) for the path that traverses cylinder 2n on
the first half and cylinder 2n+1, after applying f_(2n), on the second half.
It defines the comparison i from the paired telescope to the original one.
In the other direction r maps an even cylinder to its paired cylinder with
the same time, and collapses an odd cylinder to its target. The endpoint seam
identities show that both maps descend continuously through the quotient.

On original even cylinder (x,t), the inverse homotopy at parameter v is
H_n(t(1+v)/2,x); on an odd cylinder it is [x,max(t,v)]. At an even top these
formulas both equal [f_(2n)(x),v] in the odd cylinder. At an odd top they both
equal the next even level. At v=0 this is the identity, and at v=1 it is i r.
On a paired cylinder, r i sends time t to min(2t,1). Interpolating the time
by min(t(1+v),1) gives the other inverse homotopy, fixing both endpoints.

Curry each formula into continuous maps from the compact interval before
quotient descent; continuous evaluation then gives joint continuity without
any local compactness or separation assumption on the spaces. Arithmetic
transport identifies 2n+2 with 2(n+1). Empty spaces require no separate case.
-/
theorem mapping_telescope_pairing
    (X : ℕ → Type u) [∀ n, TopologicalSpace (X n)]
    (f : ∀ n, C(X n, X (n + 1))) :
    Nonempty (telescope f ≃ₕ telescope (X := fun n ↦ X (2 * n))
      (fun n ↦ Eq.mp (congrArg (fun m ↦ C(X (2 * n), X m)) (Nat.mul_succ 2 n).symm)
        ((f (2 * n + 1)).comp (f (2 * n))))) := by
  classical
  let g : ∀ n, C(X (2 * n), X (2 * (n + 1))) := fun n ↦
    Eq.mp (congrArg (fun m ↦ C(X (2 * n), X m)) (Nat.mul_succ 2 n).symm)
      ((f (2 * n + 1)).comp (f (2 * n)))
  let H : ∀ n, (level f (2 * n)).Homotopy
      (((level f (2 * n + 2)).comp (f (2 * n + 1))).comp (f (2 * n))) :=
    fun n ↦ (cylinderHomotopy f (2 * n)).trans
      ((cylinderHomotopy f (2 * n + 1)).compContinuousMap (f (2 * n)))
  let iraw : C(Cylinder (fun n ↦ X (2 * n)), telescope f) :=
    ⟨fun z ↦ H z.1 (z.2.2, z.2.1),
      continuous_sigma fun n ↦ (H n).continuous.comp continuous_swap⟩
  have hi : ∀ a b, setoid g a b → iraw a = iraw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · change H n (1, x) = H (n + 1) (0, g n x)
        simp [g, Nat.mul_succ]
      · change H (n + 1) (0, g n x) = H n (1, x)
        simp [g, Nat.mul_succ]
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let i : C(telescope g, telescope f) :=
    ⟨Quotient.lift iraw hi, iraw.continuous.quotient_lift hi⟩
  let oddLevel (n : ℕ) : C(X (2 * n + 2), telescope g) := by
    simpa only [Nat.mul_succ] using level g (n + 1)
  have oddLevel_apply (n : ℕ) (x : X (2 * n)) :
      oddLevel n (f (2 * n + 1) (f (2 * n) x)) = level g (n + 1) (g n x) := by
    simp only [g, oddLevel, Nat.mul_succ]
    rfl
  let R : ∀ n, C(X n × unitInterval, telescope g) :=
    Nat.evenOddRec (cylinder g 0) (fun n _ ↦ cylinder g n)
      (fun n _ ↦ ((oddLevel n).comp (f (2 * n + 1))).comp ⟨Prod.fst, continuous_fst⟩)
  have Re (n : ℕ) : R (2 * n) = cylinder g n := by
    simp [R, Nat.evenOddRec_even]
  have Ro (n : ℕ) : R (2 * n + 1) =
      ((oddLevel n).comp (f (2 * n + 1))).comp ⟨Prod.fst, continuous_fst⟩ := by
    simp [R, Nat.evenOddRec_odd]
  have Rseam (n : ℕ) (x : X n) : R n (x, 1) = R (n + 1) (f n x, 0) := by
    obtain ⟨k, hk | hk⟩ := n.even_or_odd'
    · subst n
      rw [Re, Ro]
      exact (levelTop_eq g k x).trans (oddLevel_apply k x).symm
    · subst n
      rw [Ro]
      have hn : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      have hh : ∀ (m : ℕ) (h : m = 2 * (k + 1)) (y : X m),
          R m (y, 0) = level g (k + 1) (h ▸ y) := by
        intro m h y
        subst m
        rw [Re]
        rfl
      rw [hh _ hn]
      simp only [ContinuousMap.comp_apply]
      simp only [oddLevel, Nat.mul_succ]
      rfl
  let rraw : C(Cylinder X, telescope g) :=
    ⟨fun z ↦ R z.1 z.2, continuous_sigma fun n ↦ (R n).continuous⟩
  have hr : ∀ a b, setoid f a b → rraw a = rraw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Rseam n x
      · exact (Rseam n x).symm
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let r : C(telescope f, telescope g) :=
    ⟨Quotient.lift rraw hr, rraw.continuous.quotient_lift hr⟩
  let time : C(unitInterval × unitInterval, unitInterval) :=
    ⟨fun p ↦ ⟨(p.1 : ℝ) * (1 + p.2) / 2, by
      constructor
      · exact div_nonneg (mul_nonneg p.1.prop.1 (by linarith [p.2.prop.1])) (by norm_num)
      · have h₁ := p.1.prop.2
        have h₂ := p.2.prop.2
        have h₃ := p.1.prop.1
        nlinarith⟩, by fun_prop⟩
  have time_one (t : unitInterval) : time (t, 1) = t := by
    apply Subtype.ext
    dsimp [time]
    ring
  have Hhalf (n : ℕ) (t : unitInterval) (x : X (2 * n)) :
      H n (time (t, 0), x) = cylinder f (2 * n) (x, t) := by
    dsimp only [H]
    rw [Homotopy.trans_apply]
    have hh : ((time (t, 0) : unitInterval) : ℝ) ≤ 1 / 2 := by
      dsimp [time]
      have ht := t.prop.2
      linarith
    rw [dite_eq_left hh]
    change cylinder f (2 * n) (x, _) = _
    congr 1
    congr 1
    apply Subtype.ext
    dsimp [time]
    ring
  have Hupper (n : ℕ) (v : unitInterval) (x : X (2 * n)) :
      H n (time (1, v), x) = cylinder f (2 * n + 1) (f (2 * n) x, v) := by
    dsimp only [H]
    rw [Homotopy.trans_apply]
    split_ifs with hh
    · have hv : v = 0 := by
        apply Subtype.ext
        dsimp [time] at hh
        have hv := v.prop.1
        change (v : ℝ) = 0
        linarith
      subst v
      have ht : (⟨2 * (time (1, 0) : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨(time (1, 0)).prop.1, hh⟩⟩ :
          unitInterval) = 1 := by
        apply Subtype.ext
        norm_num [time]
      simp only [ht, Homotopy.apply_one]
      rfl
    · change cylinder f (2 * n + 1) (f (2 * n) x, _) = _
      congr 1
      congr 1
      apply Subtype.ext
      dsimp [time]
      ring
  let Ke (n : ℕ) : C(X (2 * n) × unitInterval, C(unitInterval, telescope f)) :=
    ⟨fun z ↦ ⟨fun v ↦ H n (time (z.2, v), z.1), by fun_prop⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (H n).continuous.comp
        ((time.continuous.comp (continuous_fst.snd.prodMk continuous_snd)).prodMk
          continuous_fst.fst)⟩
  let Ko (n : ℕ) : C(X (2 * n + 1) × unitInterval, C(unitInterval, telescope f)) :=
    ⟨fun z ↦ ⟨fun v ↦ cylinder f (2 * n + 1) (z.1, max z.2 v), by fun_prop⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (cylinder f (2 * n + 1)).continuous.comp
        (continuous_fst.fst.prodMk (continuous_fst.snd.max continuous_snd))⟩
  let K : ∀ n, C(X n × unitInterval, C(unitInterval, telescope f)) :=
    Nat.evenOddRec (Ke 0) (fun n _ ↦ Ke n) (fun n _ ↦ Ko n)
  have K_even (n : ℕ) : K (2 * n) = Ke n := by simp [K]
  have K_odd (n : ℕ) : K (2 * n + 1) = Ko n := by simp [K]
  have Kseam (n : ℕ) (x : X n) : K n (x, 1) = K (n + 1) (f n x, 0) := by
    obtain ⟨m, hm | hm⟩ := n.even_or_odd'
    · subst n
      rw [K_even, K_odd]
      ext v
      change H m (time (1, v), x) = cylinder f (2 * m + 1) (f (2 * m) x, max 0 v)
      rw [max_eq_right (show (0 : unitInterval) ≤ v from v.prop.1)]
      exact Hupper m v x
    · subst n
      rw [K_odd]
      have hn : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
      have hh : ∀ (j : ℕ) (h : j = 2 * (m + 1)) (y : X j),
          K j (y, 0) = ContinuousMap.const _ (level f j y) := by
        intro j h y
        subst j
        rw [K_even]
        ext v
        change H (m + 1) (time (0, v), y) = _
        have ht : time (0, v) = 0 := by ext; simp [time]
        rw [ht, Homotopy.apply_zero]
        rfl
      rw [hh _ hn]
      ext v
      change cylinder f (2 * m + 1) (x, max 1 v) = _
      rw [max_eq_left (show v ≤ (1 : unitInterval) from v.prop.2)]
      exact levelTop_eq f (2 * m + 1) x
  let kraw : C(Cylinder X, C(unitInterval, telescope f)) :=
    ⟨fun z ↦ K z.1 z.2, continuous_sigma fun n ↦ (K n).continuous⟩
  have hk : ∀ a b, setoid f a b → kraw a = kraw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Kseam n x
      · exact (Kseam n x).symm
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let k : C(telescope f, C(unitInterval, telescope f)) :=
    ⟨Quotient.lift kraw hk, kraw.continuous.quotient_lift hk⟩
  have hK : (ContinuousMap.id (telescope f)).Homotopic (i.comp r) := by
    refine ⟨{ toFun := fun p ↦ k p.2 p.1
              continuous_toFun := k.uncurry.continuous.comp continuous_swap
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro q
      induction q using Quotient.inductionOn with
      | h z =>
        rcases z with ⟨n, x, t⟩
        change K n (x, t) 0 = cylinder f n (x, t)
        obtain ⟨m, hm | hm⟩ := n.even_or_odd'
        · subst n
          rw [K_even]
          exact Hhalf m t x
        · subst n
          rw [K_odd]
          change cylinder f (2 * m + 1) (x, max t 0) = _
          rw [max_eq_left (show (0 : unitInterval) ≤ t from t.prop.1)]
    · intro q
      induction q using Quotient.inductionOn with
      | h z =>
        rcases z with ⟨n, x, t⟩
        change K n (x, t) 1 = i (R n (x, t))
        obtain ⟨m, hm | hm⟩ := n.even_or_odd'
        · subst n
          rw [K_even, Re]
          change H m (time (t, 1), x) = H m (t, x)
          rw [time_one]
        · subst n
          rw [K_odd, Ro]
          change cylinder f (2 * m + 1) (x, max t 1) =
            i (oddLevel m (f (2 * m + 1) x))
          rw [max_eq_right (show t ≤ (1 : unitInterval) from t.prop.2)]
          have hiLevel (y : X (2 * (m + 1))) :
              i (level g (m + 1) y) = level f (2 * (m + 1)) y := by
            change H (m + 1) (0, y) = _
            exact Homotopy.apply_zero _ _
          have hiOdd (y : X (2 * m + 2)) :
              i (oddLevel m y) = level f (2 * m + 2) y := by
            simpa only [oddLevel, Nat.mul_succ] using hiLevel y
          rw [hiOdd]
          exact levelTop_eq f (2 * m + 1) x
  let speed : C(unitInterval × unitInterval, unitInterval) :=
    ⟨fun p ↦ ⟨min ((p.1 : ℝ) * (1 + p.2)) 1, by
      constructor
      · exact le_min (mul_nonneg p.1.prop.1 (by linarith [p.2.prop.1])) (by norm_num)
      · exact min_le_right _ _⟩, by fun_prop⟩
  have speed_zero (t : unitInterval) : speed (t, 0) = t := by
    apply Subtype.ext
    dsimp [speed]
    simp only [add_zero, mul_one, min_eq_left t.prop.2]
  have speed_bottom (v : unitInterval) : speed (0, v) = 0 := by
    ext
    norm_num [speed]
  have speed_top (v : unitInterval) : speed (1, v) = 1 := by
    apply Subtype.ext
    dsimp [speed]
    rw [min_eq_right (by linarith [v.prop.1])]
  have rH (n : ℕ) (t : unitInterval) (x : X (2 * n)) :
      r (H n (t, x)) = cylinder g n (x, speed (t, 1)) := by
    dsimp only [H]
    rw [Homotopy.trans_apply]
    split_ifs with ht
    · change R (2 * n) (x, _) = _
      rw [Re]
      congr 1
      congr 1
      apply Subtype.ext
      dsimp [speed]
      rw [min_eq_left (by linarith)]
      ring
    · change R (2 * n + 1) (f (2 * n) x, _) = _
      rw [Ro]
      change oddLevel n (f (2 * n + 1) (f (2 * n) x)) = _
      rw [oddLevel_apply, ← levelTop_eq]
      have hs : speed (t, 1) = 1 := by
        apply Subtype.ext
        dsimp [speed]
        rw [min_eq_right (by have ht' := lt_of_not_ge ht; linarith)]
      rw [hs]
      rfl
  let lraw : C(Cylinder (fun n ↦ X (2 * n)), C(unitInterval, telescope g)) :=
    ⟨fun z ↦ ⟨fun v ↦ cylinder g z.1 (z.2.1, speed (z.2.2, v)), by fun_prop⟩, by
      apply continuous_sigma
      intro n
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (cylinder g n).continuous.comp
        (continuous_fst.fst.prodMk
          (speed.continuous.comp (continuous_fst.snd.prodMk continuous_snd)))⟩
  have hl : ∀ a b, setoid g a b → lraw a = lraw b := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      rcases hab with ⟨n, x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · ext v
        change cylinder g n (x, speed (1, v)) =
          cylinder g (n + 1) (g n x, speed (0, v))
        rw [speed_top, speed_bottom]
        exact levelTop_eq g n x
      · ext v
        change cylinder g (n + 1) (g n x, speed (0, v)) =
          cylinder g n (x, speed (1, v))
        rw [speed_top, speed_bottom]
        exact (levelTop_eq g n x).symm
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k
  let l : C(telescope g, C(unitInterval, telescope g)) :=
    ⟨Quotient.lift lraw hl, lraw.continuous.quotient_lift hl⟩
  have hL : (ContinuousMap.id (telescope g)).Homotopic (r.comp i) := by
    refine ⟨{ toFun := fun p ↦ l p.2 p.1
              continuous_toFun := l.uncurry.continuous.comp continuous_swap
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro q
      induction q using Quotient.inductionOn with
      | h z =>
        rcases z with ⟨n, x, t⟩
        change cylinder g n (x, speed (t, 0)) = cylinder g n (x, t)
        rw [speed_zero]
    · intro q
      induction q using Quotient.inductionOn with
      | h z =>
        rcases z with ⟨n, x, t⟩
        exact (rH n t x).symm
  exact ⟨{ toFun := r, invFun := i, left_inv := hK.symm, right_inv := hL.symm }⟩



end HolomorphicAnosov.MappingTelescope.Sequence

