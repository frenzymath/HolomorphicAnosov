import HolomorphicAnosov.Topology.Cubical.ClosedCoordinateCell
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Ambient normalization of a coordinate cell

Agent-written affine coordinate normalization preceding the use of Bredon's
radial convex-body comparison, *Topology and Geometry*, I.16.2–16.4, pp.56–57,
for the coordinate-cell characteristic maps in Hatcher Appendix A.2, p.521.
Neither source prints this active/inactive coordinate formula.
-/

namespace HolomorphicAnosov.Cubical
open Set

/-- An ambient homeomorphism normalizes every active interval to `[-1,1]` and
every inactive coordinate to zero, with an exact characterization of boundary
faces. Degenerate cells, including vertices and zero ambient dimension, are allowed.

Translate each coordinate by its interval midpoint. In an active coordinate,
divide by the positive half-length; in an inactive coordinate use scale one.
The inverse adds the midpoint after multiplying by the scale. These finite
coordinate maps are continuous and inverse. Split the index set into active and
inactive coordinates. The interval inequalities become `-1 ≤ y ≤ 1` in active
coordinates, while equality of the original endpoints forces an inactive value
to be zero. The original lower and upper faces become respectively `-1` and `1`.
This supplies the affine normalization used before the cited radial construction;
the subsequent annular restriction is not asserted here. The coordinate formula
and verification are agent-written. -/
theorem coordinate_cell_normalization {N : ℕ} (c : ClosedCoordinateCell N) :
    ∃ e : (Fin N → ℝ) ≃ₜ
        (({i : Fin N // c.lower i < c.upper i} → ℝ) ×
          ({i : Fin N // ¬ c.lower i < c.upper i} → ℝ)),
      (∀ x, x ∈ c.carrier ↔
        (∀ i, -1 ≤ (e x).1 i ∧ (e x).1 i ≤ 1) ∧ (e x).2 = 0) ∧
      (∀ x, (∃ i : Fin N, c.lower i < c.upper i ∧
          (x i = c.lower i ∨ x i = c.upper i)) ↔
        ∃ i, (e x).1 i = -1 ∨ (e x).1 i = 1) := by
  classical
  let m : Fin N → ℝ := fun i ↦ (c.lower i + c.upper i) / 2
  let s : Fin N → ℝ := fun i ↦
    if c.lower i < c.upper i then (c.upper i - c.lower i) / 2 else 1
  have hs (i : Fin N) : 0 < s i := by
    dsimp [s]
    split_ifs with h
    · exact div_pos (sub_pos.mpr h) (by norm_num)
    · norm_num
  let h : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := fun x i ↦ (x i - m i) / s i
      invFun := fun y i ↦ m i + s i * y i
      left_inv := by
        intro x
        funext i
        dsimp
        field_simp [(hs i).ne']
        ring
      right_inv := by
        intro y
        funext i
        dsimp
        rw [add_sub_cancel_left, mul_div_cancel_left₀ _ (hs i).ne']
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_pi fun i ↦
        continuous_const.add (continuous_const.mul (continuous_apply i)) }
  let e := h.trans (Homeomorph.piEquivPiSubtypeProd
    (fun i : Fin N ↦ c.lower i < c.upper i) (fun _ ↦ ℝ))
  have hactive (x : Fin N → ℝ) (i : {i : Fin N // c.lower i < c.upper i}) :
      (e x).1 i = (x i - m i) / ((c.upper i - c.lower i) / 2) := by
    change (x i - m i) / s i = _
    simp [s, i.property]
  have hinactive (x : Fin N → ℝ) (i : {i : Fin N // ¬ c.lower i < c.upper i}) :
      (e x).2 i = x i - c.lower i := by
    have hi : c.lower i = c.upper i := le_antisymm (c.lower_le_upper i)
      (le_of_not_gt i.property)
    change (x i - m i) / s i = _
    simp [s, m, ← hi]
  have hinterval (x : Fin N → ℝ) (i : {i : Fin N // c.lower i < c.upper i}) :
      c.lower i ≤ x i ∧ x i ≤ c.upper i ↔
        -1 ≤ (e x).1 i ∧ (e x).1 i ≤ 1 := by
    rw [hactive, le_div_iff₀ (div_pos (sub_pos.mpr i.property) (by norm_num)),
      div_le_iff₀ (div_pos (sub_pos.mpr i.property) (by norm_num))]
    dsimp [m]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  refine ⟨e, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      refine ⟨fun i ↦ (hinterval x i).mp ⟨hx.1 i, hx.2 i⟩, ?_⟩
      funext i
      rw [hinactive]
      have hi := le_of_not_gt i.property
      have h₁ := hx.1 i
      have h₂ := hx.2 i
      change x i - c.lower i = 0
      linarith
    · rintro ⟨ha, hb⟩
      constructor <;> intro i
      · by_cases hi : c.lower i < c.upper i
        · exact ((hinterval x ⟨i, hi⟩).mpr (ha ⟨i, hi⟩)).1
        · have hz := congrFun hb ⟨i, hi⟩
          rw [hinactive] at hz
          change x i - c.lower i = 0 at hz
          linarith
      · by_cases hi : c.lower i < c.upper i
        · exact ((hinterval x ⟨i, hi⟩).mpr (ha ⟨i, hi⟩)).2
        · have hz := congrFun hb ⟨i, hi⟩
          rw [hinactive] at hz
          change x i - c.lower i = 0 at hz
          linarith [c.lower_le_upper i]
  · intro x
    have hfaces (i : {i : Fin N // c.lower i < c.upper i}) :
        x i = c.lower i ∨ x i = c.upper i ↔
          (e x).1 i = -1 ∨ (e x).1 i = 1 := by
      rw [hactive, div_eq_iff (ne_of_gt (div_pos (sub_pos.mpr i.property) (by norm_num))),
        div_eq_iff (ne_of_gt (div_pos (sub_pos.mpr i.property) (by norm_num)))]
      dsimp [m]
      constructor <;> intro hx <;> rcases hx with hx | hx
      · left; linarith
      · right; linarith
      · left; linarith
      · right; linarith
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨⟨i, hi⟩, (hfaces ⟨i, hi⟩).mp hx⟩
    · rintro ⟨i, hi⟩
      exact ⟨i.val, i.property, (hfaces i).mpr hi⟩

end HolomorphicAnosov.Cubical
