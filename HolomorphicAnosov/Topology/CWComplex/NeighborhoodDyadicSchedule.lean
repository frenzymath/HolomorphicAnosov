import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Dyadic contraction of a quotient union of nested deformation retracts
Source: Hatcher, Algebraic Topology, Appendix A.4, pp.522–523. Finite successive
strong deformation retractions are placed in dyadic time intervals accumulating
at zero. Compatibility fixes earlier stages; the stage-coproduct quotient and
its product with the locally compact interval give continuity on the union.
-/

namespace HolomorphicAnosov.CWNeighborhoodSchedule

open Set _root_.Topology

noncomputable section
variable {X : Type*} [TopologicalSpace X]

def into {A U : Set X} (h : A ⊆ U) : C(A, U) := ContinuousMap.inclusion h

def extendSchedule {A B U : Set X} (hAB : A ⊆ B) (hBU : B ⊆ U)
    (r : C(B, A))
    (R : (ContinuousMap.id B).HomotopyRel ((ContinuousMap.inclusion hAB).comp r)
      {y : B | y.val ∈ A})
    (a b : ℝ) (hab : a < b) (H : C(ℝ × A, U))
    (hstationary : ∀ t ≤ b, ∀ y, H (t, y) = into (hAB.trans hBU) y) : C(ℝ × B, U) where
  toFun p := if p.1 ≤ b then into hBU (R.toHomotopy.extend ((p.1 - a) / (b - a)) p.2)
    else H (p.1, r p.2)
  continuous_toFun := by
    apply continuous_if_le continuous_fst continuous_const
    · exact ((into hBU).continuous.comp (R.continuous.comp (by fun_prop))).continuousOn
    · exact (H.continuous.comp (continuous_fst.prodMk (r.continuous.comp continuous_snd))).continuousOn
    · intro p hp
      have he : R.toHomotopy.extend ((p.1 - a) / (b - a)) p.2 =
          ((ContinuousMap.inclusion hAB).comp r) p.2 := by
        apply R.toHomotopy.extend_apply_of_one_le
        rw [hp, div_self (sub_pos.mpr hab).ne']
      rw [he, hstationary p.1 hp.le]
      rfl

theorem extendSchedule_stationary {A B U : Set X} (hAB : A ⊆ B) (hBU : B ⊆ U)
    (r : C(B, A))
    (R : (ContinuousMap.id B).HomotopyRel ((ContinuousMap.inclusion hAB).comp r)
      {y : B | y.val ∈ A})
    (a b : ℝ) (hab : a < b) (H : C(ℝ × A, U))
    (hs : ∀ t ≤ b, ∀ y, H (t, y) = into (hAB.trans hBU) y)
    (t : ℝ) (ht : t ≤ a) (y : B) :
    extendSchedule hAB hBU r R a b hab H hs (t, y) = into hBU y := by
  change (if t ≤ b then _ else _) = _
  rw [ite_eq_left (ht.trans hab.le)]
  rw [R.toHomotopy.extend_apply_of_le_zero
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hab.le))]
  rfl

theorem extendSchedule_compatible {A B U : Set X} (hAB : A ⊆ B) (hBU : B ⊆ U)
    (r : C(B, A))
    (R : (ContinuousMap.id B).HomotopyRel ((ContinuousMap.inclusion hAB).comp r)
      {y : B | y.val ∈ A})
    (a b : ℝ) (hab : a < b) (H : C(ℝ × A, U))
    (hs : ∀ t ≤ b, ∀ y, H (t, y) = into (hAB.trans hBU) y)
    (t : ℝ) (y : A) :
    extendSchedule hAB hBU r R a b hab H hs
      (t, ContinuousMap.inclusion hAB y) = H (t, y) := by
  change (if t ≤ b then _ else _) = _
  split_ifs with ht
  · rw [R.extendProp _ (ContinuousMap.inclusion hAB y) y.property, hs t ht]
    rfl
  · have hr : r (ContinuousMap.inclusion hAB y) = y := by
      apply Subtype.ext
      exact congrArg (fun z : B ↦ z.val)
        (R.fst_eq_snd (x := ContinuousMap.inclusion hAB y) y.property).symm
    rw [hr]

def breakpoint (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

theorem breakpoint_step (n : ℕ) : breakpoint (n + 1) < breakpoint n := by
  unfold breakpoint
  rw [pow_succ]
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  linarith

structure Schedule (A U : Set X) (hAU : A ⊆ U) (n : ℕ) where
  H : C(ℝ × A, U)
  stationary : ∀ t ≤ breakpoint n, ∀ y, H (t, y) = into hAU y

def scheduleStep (V : ℕ → Set X) (U : Set X)
    (hVU : ∀ n, V n ⊆ U) (hVV : ∀ n, V n ⊆ V (n + 1))
    (r : ∀ n, C(V (n + 1), V n))
    (R : ∀ n, (ContinuousMap.id (V (n + 1))).HomotopyRel
      ((ContinuousMap.inclusion (hVV n)).comp (r n)) {y : V (n + 1) | y.val ∈ V n})
    (n : ℕ) (S : Schedule (V n) U (hVU n) n) :
    Schedule (V (n + 1)) U (hVU (n + 1)) (n + 1) where
  H := extendSchedule (hVV n) (hVU (n + 1)) (r n) (R n)
    (breakpoint (n + 1)) (breakpoint n) (breakpoint_step n) S.H S.stationary
  stationary := extendSchedule_stationary (hVV n) (hVU (n + 1)) (r n) (R n)
    (breakpoint (n + 1)) (breakpoint n) (breakpoint_step n) S.H S.stationary

def schedules (V : ℕ → Set X) (U : Set X)
    (hVU : ∀ n, V n ⊆ U) (hVV : ∀ n, V n ⊆ V (n + 1))
    (r : ∀ n, C(V (n + 1), V n))
    (R : ∀ n, (ContinuousMap.id (V (n + 1))).HomotopyRel
      ((ContinuousMap.inclusion (hVV n)).comp (r n)) {y : V (n + 1) | y.val ∈ V n})
    (S₀ : Schedule (V 0) U (hVU 0) 0) : ∀ n, Schedule (V n) U (hVU n) n
  | 0 => S₀
  | n + 1 => scheduleStep V U hVU hVV r R n (schedules V U hVU hVV r R S₀ n)

theorem schedules_compatible (V : ℕ → Set X) (U : Set X)
    (hVU : ∀ n, V n ⊆ U) (hVV : ∀ n, V n ⊆ V (n + 1))
    (r : ∀ n, C(V (n + 1), V n))
    (R : ∀ n, (ContinuousMap.id (V (n + 1))).HomotopyRel
      ((ContinuousMap.inclusion (hVV n)).comp (r n)) {y : V (n + 1) | y.val ∈ V n})
    (S₀ : Schedule (V 0) U (hVU 0) 0) (n : ℕ) (t : ℝ) (y : V n) :
    (schedules V U hVU hVV r R S₀ (n + 1)).H (t, ContinuousMap.inclusion (hVV n) y) =
      (schedules V U hVU hVV r R S₀ n).H (t, y) :=
  extendSchedule_compatible (hVV n) (hVU (n + 1)) (r n) (R n)
    (breakpoint (n + 1)) (breakpoint n) (breakpoint_step n)
    (schedules V U hVU hVV r R S₀ n).H (schedules V U hVU hVV r R S₀ n).stationary t y

section Consequences
variable (V : ℕ → Set X) (U : Set X)
    (hVU : ∀ n, V n ⊆ U) (hVV : ∀ n, V n ⊆ V (n + 1))
    (r : ∀ n, C(V (n + 1), V n))
    (R : ∀ n, (ContinuousMap.id (V (n + 1))).HomotopyRel
      ((ContinuousMap.inclusion (hVV n)).comp (r n)) {y : V (n + 1) | y.val ∈ V n})
    (S₀ : Schedule (V 0) U (hVU 0) 0)

theorem schedules_compatible_le (hmono : Monotone V) {n m : ℕ} (hnm : n ≤ m)
    (t : ℝ) (y : V n) :
    (schedules V U hVU hVV r R S₀ m).H (t, ⟨y.val, hmono hnm y.property⟩) =
      (schedules V U hVU hVV r R S₀ n).H (t, y) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have he := schedules_compatible V U hVU hVV r R S₀ m t
      ⟨y.val, hmono hnm y.property⟩
    exact he.trans ih

theorem schedules_zero (n : ℕ) (y : V n) :
    (schedules V U hVU hVV r R S₀ n).H (0, y) = into (hVU n) y := by
  exact (schedules V U hVU hVV r R S₀ n).stationary 0
    (le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1))) y

theorem schedules_one (p₀ : U) (hbase : ∀ y, S₀.H (1, y) = p₀)
    (n : ℕ) (y : V n) : (schedules V U hVU hVV r R S₀ n).H (1, y) = p₀ := by
  induction n with
  | zero => exact hbase y
  | succ n ih =>
    have hb : breakpoint n < 1 := by
      unfold breakpoint
      exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
    change (if (1 : ℝ) ≤ breakpoint n then _ else _) = _
    rw [ite_eq_right (not_le.mpr hb)]
    exact ih (r n y)

end Consequences

/-- The initial contraction occupies the final fixed interval [1/2,1]. -/
def baseSchedule {A U : Set X} (hAU : A ⊆ U) (p₀ : U)
    (F : (into hAU).Homotopy (ContinuousMap.const A p₀)) : Schedule A U hAU 0 where
  H :=
    { toFun := fun p ↦ F.extend (2 * p.1 - 1) p.2
      continuous_toFun := F.continuous.comp (by fun_prop) }
  stationary := by
    intro t ht y
    apply F.extend_apply_of_le_zero
    norm_num [breakpoint] at ht
    linarith

theorem baseSchedule_one {A U : Set X} (hAU : A ⊆ U) (p₀ : U)
    (F : (into hAU).Homotopy (ContinuousMap.const A p₀)) (y : A) :
    (baseSchedule hAU p₀ F).H (1, y) = p₀ := by
  exact F.extend_apply_of_one_le (by norm_num : (1 : ℝ) ≤ 2 * 1 - 1) y

/-- The accumulating dyadic schedule on the literal union, with its actual
ordinary product topology. The quotient premise is the remaining topology input;
all time joins, the accumulation point zero, and the constant endpoint are handled. -/
theorem union_dyadic_homotopy
    (V : ℕ → Set X) (hmono : Monotone V)
    (hq : IsQuotientMap (fun p : Σ n, V n ↦
      (⟨p.2.val, mem_iUnion.mpr ⟨p.1, p.2.property⟩⟩ : ↥(⋃ n, V n))))
    (r : ∀ n, C(V (n + 1), V n))
    (R : ∀ n, (ContinuousMap.id (V (n + 1))).HomotopyRel
      ((ContinuousMap.inclusion (hmono (Nat.le_succ n))).comp (r n))
      {y : V (n + 1) | y.val ∈ V n})
    (p₀ : ↥(⋃ n, V n))
    (F : (into (show V 0 ⊆ ⋃ n, V n from subset_iUnion V 0)).Homotopy
      (ContinuousMap.const (V 0) p₀)) :
    ∃ G : (ContinuousMap.id ↥(⋃ n, V n)).Homotopy
        (ContinuousMap.const ↥(⋃ n, V n) p₀),
      ∀ n (t : unitInterval) (y : V n),
        G (t, ⟨y.val, mem_iUnion.mpr ⟨n, y.property⟩⟩) =
          (schedules V (⋃ n, V n) (fun n ↦ subset_iUnion V n)
            (fun n ↦ hmono (Nat.le_succ n)) r R
            (baseSchedule (subset_iUnion V 0) p₀ F) n).H ((t : ℝ), y) := by
  classical
  let U := ⋃ n, V n
  let inc : ∀ n, V n ⊆ U := fun n ↦ subset_iUnion V n
  let q : (Σ n, V n) → U := fun p ↦ ⟨p.2.val, inc p.1 p.2.property⟩
  let S := schedules V U inc (fun n ↦ hmono (Nat.le_succ n)) r R
    (baseSchedule (inc 0) p₀ F)
  have hc (n m : ℕ) (hnm : n ≤ m) (t : ℝ) (y : V n) :
      (S m).H (t, ⟨y.val, hmono hnm y.property⟩) = (S n).H (t, y) :=
    schedules_compatible_le V U inc _ r R _ hmono hnm t y
  let rep : U → Σ n, V n := fun y ↦ (hq.surjective y).choose
  have hrep : ∀ y, q (rep y) = y := fun y ↦ (hq.surjective y).choose_spec
  have heq (t : ℝ) (a b : Σ n, V n) (hab : q a = q b) :
      (S a.1).H (t, a.2) = (S b.1).H (t, b.2) := by
    have hv : a.2.val = b.2.val := congrArg Subtype.val hab
    rw [← hc a.1 (max a.1 b.1) (le_max_left _ _) t a.2,
      ← hc b.1 (max a.1 b.1) (le_max_right _ _) t b.2]
    congr 1
    exact Prod.ext rfl (Subtype.ext hv)
  let g : unitInterval × U → U := fun p ↦
    (S (rep p.2).1).H ((p.1 : ℝ), (rep p.2).2)
  have hagree (n : ℕ) (t : unitInterval) (y : V n) :
      g (t, q ⟨n, y⟩) = (S n).H ((t : ℝ), y) :=
    heq (t : ℝ) _ ⟨n, y⟩ (hrep _)
  have hcont : Continuous g := by
    apply hq.continuous_lift_prod_right
    have hs : Continuous (fun p : Σ n, V n × unitInterval ↦
        (S p.1).H ((p.2.2 : ℝ), p.2.1)) := by
      apply continuous_sigma
      intro n
      exact (S n).H.continuous.comp
        ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
    have hh := (hs.comp
      (Homeomorph.sigmaProdDistrib (X := fun n ↦ V n) (Y := unitInterval)).continuous).comp
        continuous_swap
    convert hh using 1
    funext p
    exact hagree p.2.1 p.1 p.2.2
  let G : (ContinuousMap.id U).Homotopy (ContinuousMap.const U p₀) :=
    { toFun := g
      continuous_toFun := hcont
      map_zero_left := fun y ↦
        (schedules_zero V U inc _ r R _ (rep y).1 (rep y).2).trans (hrep y)
      map_one_left := fun y ↦
        schedules_one V U inc _ r R _ p₀
          (baseSchedule_one (inc 0) p₀ F) (rep y).1 (rep y).2 }
  exact ⟨G, hagree⟩

/-- A quotient union of successive strong deformation retracts is contractible
when its initial stage is contractible. Source: the dyadic schedule in Hatcher,
Appendix Proposition A.4, p.522, with ordinary-product continuity on p.523.
The general quotient-union formulation is agent-written.

Choose a contraction on the initial stage. Prepend each succeeding relative
deformation in the next dyadic interval towards zero. Fixedness makes the
stage schedules agree on overlaps, and closed pasting gives their continuity.
Descend the compatible schedules along the coproduct quotient, using local
compactness of the interval for product continuity. Their zero and one
endpoint equations give a nullhomotopy of the identity on the union. -/
theorem union_contractible
    (V : ℕ → Set X) (hmono : Monotone V) [ContractibleSpace (V 0)]
    (hq : IsQuotientMap (fun p : Σ n, V n ↦
      (⟨p.2.val, mem_iUnion.mpr ⟨p.1, p.2.property⟩⟩ : ↥(⋃ n, V n))))
    (r : ∀ n, C(V (n + 1), V n))
    (R : ∀ n, (ContinuousMap.id (V (n + 1))).HomotopyRel
      ((ContinuousMap.inclusion (hmono (Nat.le_succ n))).comp (r n))
      {y : V (n + 1) | y.val ∈ V n}) : ContractibleSpace ↥(⋃ n, V n) := by
  obtain ⟨p, ⟨F⟩⟩ := id_nullhomotopic (V 0)
  let inc := into (show V 0 ⊆ ⋃ n, V n from subset_iUnion V 0)
  have G : inc.Homotopy (ContinuousMap.const (V 0) (inc p)) :=
    (ContinuousMap.Homotopy.refl inc).comp F
  obtain ⟨H, _⟩ := union_dyadic_homotopy V hmono hq r R (inc p) G
  exact (contractible_iff_id_nullhomotopic _).mpr ⟨inc p, ⟨H⟩⟩

end
end HolomorphicAnosov.CWNeighborhoodSchedule

