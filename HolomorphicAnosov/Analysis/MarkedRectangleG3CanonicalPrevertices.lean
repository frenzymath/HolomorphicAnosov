import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov.Analysis.MarkedRectangle

/-- The four real prevertices in the symmetric Schwarz--Christoffel normalization.
Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010), pp. 184--186. -/
def canonicalPrevertex (k : ℝ) (i : Fin 4) : ℝ :=
  match i.val with
  | 0 => -1 / k
  | 1 => -1
  | 2 => 1
  | _ => 1 / k

/-- For a parameter in `(0,1)`, the symmetric Schwarz--Christoffel prevertices are distinct.
Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010), pp. 184--186. -/
theorem canonicalPrevertex_injective {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    Function.Injective (canonicalPrevertex k) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    exfalso
    simp only [canonicalPrevertex] at hij
    have hkne : k ≠ 0 := ne_of_gt hk0
    field_simp [hkne] at hij
    nlinarith

/-- The four-point polynomial factors through the canonical prevertices.
Source: the reciprocal-square-root polynomial in Bak--Newman, *Complex Analysis*
(3rd ed., 2010), pp. 184--186. -/
theorem canonicalPrevertex_product (k : ℝ) (z : ℂ) :
    ∏ i : Fin 4, (z - (canonicalPrevertex k i : ℂ)) =
      (z + (1 / k : ℂ)) * (z + 1) * (z - 1) * (z - (1 / k : ℂ)) := by
  rw [Fin.prod_univ_four]
  by_cases hk : k = 0
  · subst k
    norm_num [canonicalPrevertex]
  · simp only [canonicalPrevertex]
    dsimp [canonicalPrevertex]
    push_cast
    field_simp [hk]
    ring

/-- The canonical polynomial is positive on the interval between the middle
prevertices. Source: Bak--Newman, *Complex Analysis* (3rd ed., 2010),
pp. 184--186, where this sign determines the positive real branch. -/
theorem canonicalPrevertex_product_pos_on_unit_interval
    {k x : ℝ} (hk0 : 0 < k) (hk1 : k < 1)
    (hx0 : -1 < x) (hx1 : x < 1) :
    0 < (x + 1 / k) * (x + 1) * (x - 1) * (x - 1 / k) := by
  have hkinv : 1 < 1 / k := (one_lt_div₀ hk0).mpr hk1
  have h1 : 0 < x + 1 / k := by linarith
  have h2 : 0 < x + 1 := by linarith
  have h3 : 0 < 1 - x := by linarith
  have h4 : 0 < 1 / k - x := by linarith
  calc
    0 < (x + 1 / k) * (x + 1) * ((1 - x) * (1 / k - x)) := by positivity
    _ = (x + 1 / k) * (x + 1) * (x - 1) * (x - 1 / k) := by ring

end HolomorphicAnosov.Analysis.MarkedRectangle

