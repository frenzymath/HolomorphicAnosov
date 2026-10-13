import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic
import HolomorphicAnosov.Dynamics.SmaleCyclicShadowing
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

/-! Finite metric pseudo-orbit chains and the spectral decomposition of expansive homeomorphisms
with cyclic shadowing. -/

namespace HolomorphicAnosov
open Set Fin.NatCast

/-- A finite pseudo-orbit from `x` to `y`, allowing length zero (Shub, Chapter 8, pp. 102–107). -/
def SmaleChain {X : Type*} [MetricSpace X] (f : X → X) (δ : ℝ) (x y : X) : Prop :=
  ∃ (n : ℕ) (q : ℕ → X), q 0 = x ∧ q n = y ∧
    ∀ i < n, dist (f (q i)) (q (i + 1)) < δ

namespace SmaleChain
variable {X : Type*} [MetricSpace X] {f : X → X} {δ : ℝ} {x y z : X}

protected theorem refl (x : X) : SmaleChain f δ x x :=
  ⟨0, fun _ ↦ x, rfl, rfl, fun i hi ↦ (Nat.not_lt_zero i hi).elim⟩

protected theorem single (h : dist (f x) y < δ) : SmaleChain f δ x y := by
  refine ⟨1, fun i ↦ if i = 0 then x else y, by simp, by simp, ?_⟩
  intro i hi
  have : i = 0 := by omega
  simpa [this] using h

protected theorem trans (hxy : SmaleChain f δ x y) (hyz : SmaleChain f δ y z) :
    SmaleChain f δ x z := by
  obtain ⟨n, a, ha0, han, ha⟩ := hxy
  obtain ⟨m, b, hb0, hbm, hb⟩ := hyz
  refine ⟨n + m, fun i ↦ if i < n then a i else b (i - n), ?_, ?_, ?_⟩
  · by_cases hn : n = 0
    · simp only [hn, Nat.sub_zero, Nat.lt_irrefl, ite_false]
      rw [hb0, ← han, hn, ha0]
    · simpa [Nat.pos_of_ne_zero hn] using ha0
  · simpa using hbm
  · intro i hi
    by_cases hin : i < n
    · by_cases hsucc : i + 1 < n
      · simpa [hin, hsucc] using ha i hin
      · have heq : i + 1 = n := by omega
        simpa [hin, hsucc, heq, hb0, han] using ha i hin
    · have hsub : i - n < m := by omega
      have hsucc : ¬i + 1 < n := by omega
      have heq : i + 1 - n = i - n + 1 := by omega
      simpa [hin, hsucc, heq] using hb (i - n) hsub

theorem mono {ε : ℝ} (h : SmaleChain f δ x y) (hle : δ ≤ ε) : SmaleChain f ε x y := by
  obtain ⟨n, q, hq0, hqn, hq⟩ := h
  exact ⟨n, q, hq0, hqn, fun i hi ↦ (hq i hi).trans_le hle⟩

theorem orbit (hδ : 0 < δ) (n : ℕ) (x : X) : SmaleChain f δ x (f^[n] x) := by
  refine ⟨n, fun i ↦ f^[i] x, rfl, rfl, ?_⟩
  intro i _
  simpa only [Function.iterate_succ_apply', dist_self] using hδ

/-- A periodic point within distance `δ` of another point admits a `δ`-chain to that point. -/
theorem of_periodic_close (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hx : Function.IsPeriodicPt f n x) (hxy : dist x y < δ) : SmaleChain f δ x y := by
  have hn1 : n - 1 + 1 = n := by omega
  apply (orbit hδ (n - 1) x).trans
  apply SmaleChain.single
  rw [← Function.iterate_succ_apply' f (n - 1) x, Nat.succ_eq_add_one, hn1, hx.eq]
  exact hxy

theorem same_periodic_orbit (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hp : Function.IsPeriodicPt f n x) (i j : ℕ) :
    SmaleChain f δ (f^[i] x) (f^[j] x) := by
  have hirem : i % n ≤ n := (Nat.mod_lt i hn).le
  have hback : f^[n - i % n] (f^[i] x) = x := by
    rw [← hp.iterate_mod_apply i, ← Function.iterate_add_apply,
      Nat.sub_add_cancel hirem, hp.eq]
  have h := orbit (f := f) hδ (n - i % n) (f^[i] x)
  rw [hback] at h
  exact h.trans (orbit hδ j x)

end SmaleChain

/-- Concatenation of two sequences at index `n`. -/
def smaleAppend {X : Type*} (a : ℕ → X) (n : ℕ) (b : ℕ → X) : ℕ → X :=
  fun i ↦ if i < n then a i else b (i - n)

 theorem smaleAppend_left {X : Type*} (a b : ℕ → X) (n : ℕ) (hab : a n = b 0)
    (i : ℕ) (hi : i ≤ n) : smaleAppend a n b i = a i := by
  by_cases h : i < n
  · simp [smaleAppend, h]
  · have : i = n := by omega
    simp [smaleAppend, this, hab]

 theorem smaleAppend_right {X : Type*} (a b : ℕ → X) (n i : ℕ) :
    smaleAppend a n b (n + i) = b i := by simp [smaleAppend]

 theorem smaleAppend_jumps {X : Type*} [MetricSpace X] (f : X → X) (δ : ℝ)
    (a b : ℕ → X) (n m : ℕ) (hab : a n = b 0)
    (ha : ∀ i < n, dist (f (a i)) (a (i + 1)) < δ)
    (hb : ∀ i < m, dist (f (b i)) (b (i + 1)) < δ) :
    ∀ i < n + m, dist (f (smaleAppend a n b i)) (smaleAppend a n b (i + 1)) < δ := by
  intro i hi
  by_cases hin : i < n
  · rw [smaleAppend_left a b n hab i hin.le,
      smaleAppend_left a b n hab (i + 1) (by omega)]
    exact ha i hin
  · have heq : i = n + (i - n) := by omega
    rw [heq, smaleAppend_right, show n + (i - n) + 1 = n + (i - n + 1) by omega,
      smaleAppend_right]
    exact hb _ (by omega)



/-- A cyclic shadowing semiconjugacy gives a periodic orbit shadowing every point of a closed finite
chain, including its endpoint. -/
theorem smale_shadow_closed_chain
    {X : Type*} [MetricSpace X] (f : X → X) (ε δ : ℝ)
    (hcyclic : ∀ (n : ℕ), 0 < n → ∀ q : Fin n → X,
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
      ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
        ∀ i, dist (j i) (q i) < ε)
    (n : ℕ) (hn : 0 < n) (q : ℕ → X) (hqn : q n = q 0)
    (hjump : ∀ i < n, dist (f (q i)) (q (i + 1)) < δ) :
    ∃ p : X, Function.IsPeriodicPt f n p ∧
      ∀ i ≤ n, dist (f^[i] p) (q i) < ε := by
  let : NeZero n := ⟨by omega⟩
  have hrot (i : Fin n) : (finRotate n i).val = (i.val + 1) % n := by
    rw [finRotate_apply]
    simp [Fin.val_add]
  have hqjump (i : Fin n) : dist (f (q i.val)) (q (finRotate n i).val) < δ := by
    rw [hrot]
    by_cases hi : i.val + 1 < n
    · rw [Nat.mod_eq_of_lt hi]
      exact hjump i.val i.isLt
    · have heq : i.val + 1 = n := by omega
      simpa only [heq, Nat.mod_self, hqn] using hjump i.val i.isLt
  obtain ⟨j, hj, hclose⟩ := hcyclic n hn (fun i ↦ q i.val) hqjump
  have hiter (i : ℕ) : f^[i] (j 0) = j (i : Fin n) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, ← hj]
      congr 1
      simp [finRotate_apply, Nat.cast_add, Nat.cast_one]
  have hp : Function.IsPeriodicPt f n (j 0) := by
    exact show f^[n] (j 0) = j 0 from by simpa only [Fin.natCast_self] using hiter n
  refine ⟨j 0, hp, ?_⟩
  intro i hi
  rcases lt_or_eq_of_le hi with hi | rfl
  · rw [hiter]
    have hval : (i : Fin n).val = i := by simp [Fin.val_natCast, Nat.mod_eq_of_lt hi]
    simpa only [hval] using hclose (i : Fin n)
  · rw [hp.eq, hqn]
    exact hclose 0

/-- For an expansive homeomorphism of a compact metric space, closeness on a sufficiently long
centered orbit segment forces any prescribed closeness of the initial points. -/
theorem smale_centered_expansive_window {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ : ℝ)
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((f ^ j) x) ((f ^ j) y) ≤ γ) → x = y)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ n : ℕ, ∀ x y : X,
      (∀ i ≤ 2 * n, dist ((f : X → X)^[i] x) ((f : X → X)^[i] y) ≤ γ) →
      dist ((f : X → X)^[n] x) ((f : X → X)^[n] y) < ζ := by
  obtain ⟨n, hn⟩ := BowenBasicSetCoding.exists_finite_expansive_window f γ hexp ζ hζ
  refine ⟨n, fun x y hxy ↦ hn _ _ ?_⟩
  intro j hj
  let i := (j + n).toNat
  have hjlo : -(n : ℤ) ≤ j := (abs_le.mp hj).1
  have hjhi : j ≤ (n : ℤ) := (abs_le.mp hj).2
  have hieq : (i : ℤ) = j + n := Int.toNat_of_nonneg (by omega)
  have hile : i ≤ 2 * n := by omega
  have hpow (l : ℕ) (z : X) : (f ^ l) z = (f : X → X)^[l] z := by
    induction l with
    | zero => rfl
    | succ l ih => simp [pow_succ', Homeomorph.mul_apply,
        Function.iterate_succ_apply', ih]
  have heq (z : X) : (f ^ j) ((f : X → X)^[n] z) = (f : X → X)^[i] z := by
    rw [← hpow n, ← hpow i]
    rw [← zpow_natCast f n, ← Homeomorph.mul_apply, ← zpow_add,
      ← hieq, zpow_natCast]
  simpa only [heq] using hxy i hile

/-- Under expansivity and cyclic shadowing, two periodic points joined by chains in both directions
at a fixed scale can be approximated arbitrarily closely by one periodic orbit. -/
theorem smale_periodic_orbit_approximates_mutual_chains
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ δ : ℝ) (hδ : 0 < δ)
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((f ^ j) x) ((f ^ j) y) ≤ γ) → x = y)
    (hcyclic : ∀ (n : ℕ), 0 < n → ∀ q : Fin n → X,
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
      ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
        ∀ i, dist (j i) (q i) < γ)
    (x y : X) (hx : x ∈ Function.periodicPts (f : X → X))
    (hy : y ∈ Function.periodicPts (f : X → X))
    (hxy : SmaleChain (f : X → X) δ x y)
    (hyx : SmaleChain (f : X → X) δ y x) :
    ∀ ε : ℝ, 0 < ε → ∃ p ∈ Function.periodicPts (f : X → X),
      ∃ i j : ℕ, dist ((f : X → X)^[i] p) x < ε ∧
        dist ((f : X → X)^[j] p) y < ε := by
  intro ε hε
  obtain ⟨w, hw⟩ := smale_centered_expansive_window f γ hexp ε hε
  obtain ⟨px, hpx, hxper⟩ := Function.mem_periodicPts.mp hx
  obtain ⟨py, hpy, hyper⟩ := Function.mem_periodicPts.mp hy
  obtain ⟨n, a, ha0, han, ha⟩ := hxy
  obtain ⟨m, b, hb0, hbm, hb⟩ := hyx
  let A := px * (w + 1)
  let B := py * (w + 1)
  have hAw : w ≤ A := by dsimp [A]; nlinarith
  have hBw : w ≤ B := by dsimp [B]; nlinarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hxA : (f : X → X)^[A] x = x := (hxper.mul_const (w + 1)).eq
  have hyB : (f : X → X)^[B] y = y := (hyper.mul_const (w + 1)).eq
  have hx2A : (f : X → X)^[2 * A] x = x :=
    (hxper.mul_const (w + 1) |>.const_mul 2).eq
  have hy2B : (f : X → X)^[2 * B] y = y :=
    (hyper.mul_const (w + 1) |>.const_mul 2).eq
  let ox : ℕ → X := fun i ↦ (f : X → X)^[i] x
  let oy : ℕ → X := fun i ↦ (f : X → X)^[i] y
  let R := smaleAppend oy (2 * B) b
  let S := smaleAppend a n R
  let Q := smaleAppend ox (2 * A) S
  have hyb : oy (2 * B) = b 0 := hy2B.trans hb0.symm
  have hR0 : R 0 = y := by
    rw [show R 0 = oy 0 from smaleAppend_left oy b (2 * B) hyb 0 (Nat.zero_le _)]
    rfl
  have har : a n = R 0 := han.trans hR0.symm
  have hS0 : S 0 = x := by
    rw [show S 0 = a 0 from smaleAppend_left a R n har 0 (Nat.zero_le _)]
    exact ha0
  have hxs : ox (2 * A) = S 0 := hx2A.trans hS0.symm
  have hQ0 : Q 0 = x := by
    rw [show Q 0 = ox 0 from smaleAppend_left ox S (2 * A) hxs 0 (Nat.zero_le _)]
    rfl
  let T := 2 * A + (n + (2 * B + m))
  have hT : 0 < T := by dsimp [T]; omega
  have hQT : Q T = Q 0 := by
    dsimp only [T, Q, S, R]
    rw [smaleAppend_right, smaleAppend_right, smaleAppend_right, hbm]
    exact hQ0.symm
  have hox : ∀ i < 2 * A, dist (f (ox i)) (ox (i + 1)) < δ := by
    intro i _
    simpa [ox, Function.iterate_succ_apply'] using hδ
  have hoy : ∀ i < 2 * B, dist (f (oy i)) (oy (i + 1)) < δ := by
    intro i _
    simpa [oy, Function.iterate_succ_apply'] using hδ
  have hQ : ∀ i < T, dist (f (Q i)) (Q (i + 1)) < δ :=
    smaleAppend_jumps f δ ox S (2 * A) (n + (2 * B + m)) hxs hox
      (smaleAppend_jumps f δ a R n (2 * B + m) har ha
        (smaleAppend_jumps f δ oy b (2 * B) m hyb hoy hb))
  obtain ⟨p, hp, hclose⟩ := smale_shadow_closed_chain f γ δ hcyclic T hT Q hQT hQ
  have hxwindow : dist ((f : X → X)^[A] p) x < ε := by
    have h := hw ((f : X → X)^[A - w] p) (ox (A - w)) (by
      intro i hi
      have hidx : A - w + i ≤ 2 * A := by omega
      have hidxT : A - w + i ≤ T := by dsimp [T]; omega
      have hqidx : Q (A - w + i) = ox (A - w + i) :=
        smaleAppend_left ox S (2 * A) hxs _ hidx
      have hci := (hclose (A - w + i) hidxT).le
      rw [hqidx] at hci
      simpa only [ox, ← Function.iterate_add_apply, Nat.add_comm i] using hci)
    have heq : A - w + w = A := Nat.sub_add_cancel hAw
    simpa only [ox, ← Function.iterate_add_apply, Nat.add_comm w, heq, hxA] using h
  have hywindow : dist ((f : X → X)^[2 * A + n + B] p) y < ε := by
    have h := hw ((f : X → X)^[2 * A + n + (B - w)] p) (oy (B - w)) (by
      intro i hi
      have hidx : B - w + i ≤ 2 * B := by omega
      have hidxT : 2 * A + (n + (B - w + i)) ≤ T := by dsimp [T]; omega
      have hqidx : Q (2 * A + (n + (B - w + i))) = oy (B - w + i) := by
        dsimp only [Q, S]
        rw [smaleAppend_right, smaleAppend_right]
        exact smaleAppend_left oy b (2 * B) hyb _ hidx
      have hci := (hclose _ hidxT).le
      rw [hqidx] at hci
      simpa only [oy, ← Function.iterate_add_apply, Nat.add_assoc, Nat.add_comm i,
        Nat.add_left_comm i] using hci)
    have heq : B - w + w = B := Nat.sub_add_cancel hBw
    simpa only [oy, ← Function.iterate_add_apply, Nat.add_assoc, Nat.add_comm w,
      Nat.add_left_comm w, heq, hyB] using h
  exact ⟨p, Function.mem_periodicPts.mpr ⟨T, hT, hp⟩, A, 2 * A + n + B,
    hxwindow, hywindow⟩

/-- Mutual pseudo-orbit reachability at every positive accuracy. -/
def SmaleRelated {X : Type*} [MetricSpace X] (f : X → X) (x y : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → SmaleChain f ε x y ∧ SmaleChain f ε y x

namespace SmaleRelated
variable {X : Type*} [MetricSpace X] {f : X → X} {x y z : X}

protected theorem refl (x : X) : SmaleRelated f x x :=
  fun _ _ ↦ ⟨SmaleChain.refl x, SmaleChain.refl x⟩

protected theorem symm (h : SmaleRelated f x y) : SmaleRelated f y x :=
  fun ε hε ↦ (h ε hε).symm

protected theorem trans (h : SmaleRelated f x y) (h' : SmaleRelated f y z) :
    SmaleRelated f x z := fun ε hε ↦
  ⟨(h ε hε).1.trans (h' ε hε).1, (h' ε hε).2.trans (h ε hε).2⟩

 theorem of_periodic_approximation (hf : Continuous f)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ p ∈ Function.periodicPts f,
      ∃ i j : ℕ, dist (f^[i] p) x < ε ∧ dist (f^[j] p) y < ε) :
    SmaleRelated f x y := by
  intro ε hε
  obtain ⟨ηx, hηx, hfx⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := x)) ε hε
  obtain ⟨ηy, hηy, hfy⟩ := Metric.continuousAt_iff.mp (hf.continuousAt (x := y)) ε hε
  obtain ⟨p, hp, i, j, hix, hjy⟩ := happrox (min ε (min ηx ηy))
    (lt_min hε (lt_min hηx hηy))
  obtain ⟨n, hn, hpn⟩ := Function.mem_periodicPts.mp hp
  have hixε := hix.trans_le (min_le_left ε (min ηx ηy))
  have hjyε := hjy.trans_le (min_le_left ε (min ηx ηy))
  have hixη := hix.trans_le ((min_le_right ε (min ηx ηy)).trans (min_le_left ηx ηy))
  have hjyη := hjy.trans_le ((min_le_right ε (min ηx ηy)).trans (min_le_right ηx ηy))
  have hstartx : SmaleChain f ε x (f^[i + 1] p) := SmaleChain.single (by
    rw [Function.iterate_succ_apply']
    simpa only [dist_comm] using hfx hixη)
  have hstarty : SmaleChain f ε y (f^[j + 1] p) := SmaleChain.single (by
    rw [Function.iterate_succ_apply']
    simpa only [dist_comm] using hfy hjyη)
  refine ⟨hstartx.trans ((SmaleChain.same_periodic_orbit hε hn hpn (i + 1) j).trans ?_),
    hstarty.trans ((SmaleChain.same_periodic_orbit hε hn hpn (j + 1) i).trans ?_)⟩
  · exact SmaleChain.of_periodic_close hε hn (hpn.apply_iterate j) hjyε
  · exact SmaleChain.of_periodic_close hε hn (hpn.apply_iterate i) hixε

end SmaleRelated

/-- Under expansivity and cyclic shadowing, mutual chains at a single fixed scale characterize
mutual reachability at every positive scale for periodic points. -/
theorem smale_related_iff_coarse_chains
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ δ : ℝ) (hδ : 0 < δ)
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((f ^ j) x) ((f ^ j) y) ≤ γ) → x = y)
    (hcyclic : ∀ (n : ℕ), 0 < n → ∀ q : Fin n → X,
      (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
      ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
        ∀ i, dist (j i) (q i) < γ)
    (x y : X) (hx : x ∈ Function.periodicPts (f : X → X))
    (hy : y ∈ Function.periodicPts (f : X → X)) :
    SmaleRelated (f : X → X) x y ↔
      SmaleChain (f : X → X) δ x y ∧ SmaleChain (f : X → X) δ y x := by
  constructor
  · exact fun h ↦ h δ hδ
  · rintro ⟨hxy, hyx⟩
    exact SmaleRelated.of_periodic_approximation f.continuous
      (smale_periodic_orbit_approximates_mutual_chains f γ δ hδ hexp hcyclic x y hx hy hxy hyx)

/-- The periodic points related to `x` by chains at every positive accuracy. -/
def smalePeriodicClass {X : Type*} [MetricSpace X] (f : X → X) (x : X) : Set X :=
  {y | y ∈ Function.periodicPts f ∧ SmaleRelated f x y}

 theorem smale_periodic_iterate_reachable {X : Type*} (f : X → X) {p : X}
    {n : ℕ} (hn : 0 < n) (hp : Function.IsPeriodicPt f n p) (i j : ℕ) :
    ∃ k : ℕ, f^[k] (f^[i] p) = f^[j] p := by
  refine ⟨j + (n - i % n), ?_⟩
  rw [Function.iterate_add_apply]
  have hback : f^[n - i % n] (f^[i] p) = p := by
    rw [← hp.iterate_mod_apply i, ← Function.iterate_add_apply,
      Nat.sub_add_cancel (Nat.mod_lt i hn).le, hp.eq]
  rw [hback]

 theorem smale_related_periodic_iterates {X : Type*} [MetricSpace X] (f : X → X)
    {p : X} (hp : p ∈ Function.periodicPts f) (i j : ℕ) :
    SmaleRelated f (f^[i] p) (f^[j] p) := by
  obtain ⟨n, hn, hpn⟩ := Function.mem_periodicPts.mp hp
  exact fun ε hε ↦ ⟨SmaleChain.same_periodic_orbit hε hn hpn i j,
    SmaleChain.same_periodic_orbit hε hn hpn j i⟩

 theorem smale_periodicClass_eq {X : Type*} [MetricSpace X] (f : X → X)
    {x y : X} (hxy : SmaleRelated f x y) : smalePeriodicClass f x = smalePeriodicClass f y := by
  ext z
  exact ⟨fun h ↦ ⟨h.1, hxy.symm.trans h.2⟩, fun h ↦ ⟨h.1, hxy.trans h.2⟩⟩

 theorem smale_periodicClass_image {X : Type*} [MetricSpace X] (f : X ≃ₜ X) (x : X) :
    f '' smalePeriodicClass (f : X → X) x = smalePeriodicClass (f : X → X) x := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨n, hn, hyn⟩ := Function.mem_periodicPts.mp hy.1
    refine ⟨Function.mem_periodicPts.mpr ⟨n, hn, hyn.apply⟩, ?_⟩
    exact hy.2.trans (smale_related_periodic_iterates f hy.1 0 1)
  · intro y hy
    obtain ⟨n, hn, hyn⟩ := Function.mem_periodicPts.mp hy.1
    refine ⟨(f : X → X)^[n - 1] y, ⟨Function.mem_periodicPts.mpr
      ⟨n, hn, hyn.apply_iterate (n - 1)⟩, ?_⟩, ?_⟩
    · exact hy.2.trans (smale_related_periodic_iterates f hy.1 0 (n - 1))
    · rw [← Function.iterate_succ_apply' f (n - 1) y,
        show (n - 1).succ = n by omega, hyn.eq]

/-- For an expansive homeomorphism with cyclic shadowing, the closure of the periodic points is a
finite disjoint union of nonempty compact invariant transitive components, uniformly isolated
among periodic points (Shub, Thm. 8.13). -/
theorem smale_finite_components_of_expansive_cyclic
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ : ℝ) (hγ : 0 < γ)
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((f ^ j) x) ((f ^ j) y) ≤ γ) → x = y)
    (hcyclic : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → X,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
          ∃ j : Fin n → X, Function.Semiconj j (finRotate n) f ∧
            ∀ i, dist (j i) (q i) < ε) :
    ∃ (b : ℕ) (L : Fin b → Set X),
      (∀ i, (L i).Nonempty ∧ IsCompact (L i) ∧ f '' L i = L i) ∧
      Pairwise (fun i j ↦ Disjoint (L i) (L j)) ∧
      closure (Function.periodicPts (f : X → X)) = ⋃ i, L i ∧
      (∀ i, ∀ U V : Set X, IsOpen U → (U ∩ L i).Nonempty →
        IsOpen V → (V ∩ L i).Nonempty →
        ∃ k : ℕ, ((f : X → X)^[k] '' (U ∩ L i) ∩ V).Nonempty) ∧
      (∀ i, ∃ η : ℝ, 0 < η ∧ ∀ a ∈ L i,
        ∀ p ∈ Function.periodicPts (f : X → X), dist p a < η → p ∈ L i) := by
  classical
  obtain ⟨δ, hδ, hδcyclic⟩ := hcyclic γ hγ
  let P := Function.periodicPts (f : X → X)
  let C := smalePeriodicClass (f : X → X)
  have hclose_related : ∀ x ∈ P, ∀ y ∈ P, dist x y < δ → SmaleRelated (f : X → X) x y := by
    intro x hx y hy hxy
    obtain ⟨nx, hnx, hpx⟩ := Function.mem_periodicPts.mp hx
    obtain ⟨ny, hny, hpy⟩ := Function.mem_periodicPts.mp hy
    apply (smale_related_iff_coarse_chains f γ δ hδ hexp hδcyclic x y hx hy).mpr
    exact ⟨SmaleChain.of_periodic_close hδ hnx hpx hxy,
      SmaleChain.of_periodic_close hδ hny hpy (by simpa only [dist_comm] using hxy)⟩
  have hmem (x : X) (hx : x ∈ P) : x ∈ C x := ⟨hx, SmaleRelated.refl x⟩
  have hCeq {x y : X} (hxy : SmaleRelated (f : X → X) x y) : C x = C y :=
    smale_periodicClass_eq f hxy
  have hsep : ∀ x y : X, C x ≠ C y → ∀ a ∈ C x, ∀ b ∈ C y, δ ≤ dist a b := by
    intro x y hne a ha b hb
    by_contra! hab
    exact hne (hCeq (ha.2.trans ((hclose_related a ha.1 b hb.1 hab).trans hb.2.symm)))
  have hsepClosure : ∀ x y : X, C x ≠ C y →
      ∀ a ∈ closure (C x), ∀ b ∈ closure (C y), δ ≤ dist a b := by
    intro x y hne a ha b hb
    have hCa : closure (C x) ⊆ {a | ∀ b ∈ C y, δ ≤ dist a b} := by
      have hclosed : IsClosed {a : X | ∀ b ∈ C y, δ ≤ dist a b} := by
        simp only [ofPred_forall]
        exact isClosed_iInter fun b ↦ isClosed_iInter fun _ ↦
          isClosed_le continuous_const (continuous_id.dist continuous_const)
      exact closure_minimal (fun a ha b hb ↦ hsep x y hne a ha b hb) hclosed
    have hCb : closure (C y) ⊆ {b | δ ≤ dist a b} :=
      closure_minimal (hCa ha)
        (isClosed_le continuous_const (continuous_const.dist continuous_id))
    exact hCb hb
  have hdisj : ∀ x y : X, closure (C x) ≠ closure (C y) →
      Disjoint (closure (C x)) (closure (C y)) := by
    intro x y hne
    apply Set.disjoint_left.mpr
    intro a ha hb
    have hCne : C x ≠ C y := fun h ↦ hne (congrArg closure h)
    have := hsepClosure x y hCne a ha a hb
    exact hδ.not_ge (by simpa using this)
  have hsepp : ∀ x, ∀ a ∈ closure (C x), ∀ p ∈ P,
      dist p a < δ → p ∈ C x := by
    intro x a ha p hp hpa
    by_contra hpnot
    have hne : C p ≠ C x := fun h ↦ hpnot (h ▸ hmem p hp)
    exact (not_lt_of_ge (hsepClosure p x hne p (subset_closure (hmem p hp)) a ha)) hpa
  obtain ⟨t, htP, htfin, htcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure
      (isClosed_closure.isCompact : IsCompact (closure P)) hδ
  let S : Finset (Set X) := htfin.toFinset.image (fun x ↦ closure (C x))
  have hS : ∀ A ∈ S, ∃ x ∈ P, A = closure (C x) := by
    intro A hA
    obtain ⟨x, hxt, rfl⟩ := Finset.mem_image.mp hA
    exact ⟨x, htP (by simpa using hxt), rfl⟩
  have hcoverP : P ⊆ ⋃ A ∈ S, A := by
    intro p hp
    obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.mp (htcover hp)
    have hrel := hclose_related x (htP hxt) p hp (by
      simpa only [dist_comm] using (Metric.mem_ball.mp hpx))
    exact Set.mem_iUnion₂.mpr ⟨closure (C x), Finset.mem_image.mpr
      ⟨x, by simpa using hxt, rfl⟩, subset_closure ⟨hp, hrel⟩⟩
  have hcover : closure P = ⋃ A ∈ S, A := by
    apply Set.Subset.antisymm
    · apply closure_minimal hcoverP
      apply Set.Finite.isClosed_biUnion S.finite_toSet
      intro A hA
      obtain ⟨x, _, rfl⟩ := hS A hA
      exact isClosed_closure
    · intro p hp
      obtain ⟨A, hA, hpA⟩ := Set.mem_iUnion₂.mp hp
      obtain ⟨x, _, rfl⟩ := hS A hA
      exact closure_mono (fun _ h ↦ h.1) hpA
  let e : Fin S.card ≃ {A // A ∈ S} := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let L : Fin S.card → Set X := fun i ↦ (e i).val
  have hL (i : Fin S.card) : ∃ x ∈ P, L i = closure (C x) := hS _ (e i).property
  have hLinj : Function.Injective L := fun i j hij ↦ e.injective (Subtype.ext hij)
  refine ⟨S.card, L, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨x, hx, heq⟩ := hL i
    rw [heq]
    exact ⟨⟨x, subset_closure (hmem x hx)⟩, isClosed_closure.isCompact, by
      rw [f.image_closure, smale_periodicClass_image]⟩
  · intro i j hij
    obtain ⟨x, hx, hi⟩ := hL i
    obtain ⟨y, hy, hj⟩ := hL j
    rw [hi, hj]
    exact hdisj x y (fun heq ↦ hij (hLinj (hi.trans (heq.trans hj.symm))))
  · rw [hcover]
    ext p
    constructor
    · intro hp
      obtain ⟨A, hA, hpA⟩ := Set.mem_iUnion₂.mp hp
      exact Set.mem_iUnion.mpr ⟨e.symm ⟨A, hA⟩, by simpa [L] using hpA⟩
    · intro hp
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
      exact Set.mem_iUnion₂.mpr ⟨L i, (e i).property, hpi⟩
  · intro i U V hU hUn hV hVn
    obtain ⟨x, hx, hLi⟩ := hL i
    obtain ⟨u, huU, huL⟩ := hUn
    obtain ⟨v, hvV, hvL⟩ := hVn
    rw [hLi] at huL hvL
    obtain ⟨a, haU, haC⟩ := (mem_closure_iff.mp huL) U hU huU
    obtain ⟨b, hbV, hbC⟩ := (mem_closure_iff.mp hvL) V hV hvV
    obtain ⟨εu, hεu, hballU⟩ := Metric.isOpen_iff.mp hU a haU
    obtain ⟨εv, hεv, hballV⟩ := Metric.isOpen_iff.mp hV b hbV
    let ε := min δ (min εu εv)
    have hε : 0 < ε := lt_min hδ (lt_min hεu hεv)
    have hab := haC.2.symm.trans hbC.2
    obtain ⟨p, hp, s, t, hps, hpt⟩ :=
      smale_periodic_orbit_approximates_mutual_chains f γ δ hδ hexp hδcyclic
        a b haC.1 hbC.1 (hab δ hδ).1 (hab δ hδ).2 ε hε
    obtain ⟨n, hn, hpn⟩ := Function.mem_periodicPts.mp hp
    have hsp : (f : X → X)^[s] p ∈ P :=
      Function.mem_periodicPts.mpr ⟨n, hn, hpn.apply_iterate s⟩
    have hsC : (f : X → X)^[s] p ∈ C x :=
      ⟨hsp, haC.2.trans (hclose_related a haC.1 _ hsp (by
        simpa only [dist_comm] using hps.trans_le (min_le_left δ _)))⟩
    obtain ⟨k, hk⟩ := smale_periodic_iterate_reachable f hn hpn s t
    refine ⟨k, (f : X → X)^[t] p, ⟨(f : X → X)^[s] p, ⟨?_, ?_⟩, hk⟩, ?_⟩
    · exact hballU (hps.trans_le ((min_le_right δ _).trans (min_le_left εu εv)))
    · rw [hLi]
      exact subset_closure hsC
    · exact hballV (hpt.trans_le ((min_le_right δ _).trans (min_le_right εu εv)))
  · intro i
    obtain ⟨x, hx, hLi⟩ := hL i
    refine ⟨δ, hδ, ?_⟩
    intro a ha p hp hpa
    rw [hLi] at ha ⊢
    exact subset_closure (hsepp x a ha p hp hpa)

end HolomorphicAnosov

