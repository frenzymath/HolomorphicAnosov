import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrier

/-!
# The normalized carrier norm and weighted graph distance

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977),
Sublemma 5.2, pp.54–55, with parameter insertion on p.62.
Normalized dependent `lp` coordinates recover graph differences by multiplying
by the input norm. This identifies the inherited norm bound with the pointwise
weighted bound, including zero fibres and an empty parameter space.
-/

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- For nonnegative `d`, the norm of a normalized graph difference is at most `d` exactly when every
recovered graph difference is bounded by `d * ‖x‖` (Hirsch–Pugh–Shub, pp. 54–55). -/
theorem parameter_graph_carrier_norm_le_iff
    {A : Type*} (E F : A → Type*)
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    (q q' : ParameterGraphCarrier E F) (d : ℝ) (hd : 0 ≤ d) :
    ‖q - q'‖ ≤ d ↔ ∀ p (x : E p),
      ‖parameterGraphValue E F q p x - parameterGraphValue E F q' p x‖ ≤ d * ‖x‖ := by
  classical
  constructor
  · intro h p x
    by_cases hx : x = 0
    · simp [parameterGraphValue, hx]
    · simp only [parameterGraphValue, dite_eq_right hx, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      calc
        ‖x‖ * ‖q ⟨p, ⟨x, hx⟩⟩ - q' ⟨p, ⟨x, hx⟩⟩‖ ≤ ‖x‖ * ‖q - q'‖ :=
          mul_le_mul_of_nonneg_left
            (lp.norm_apply_le_norm (by simp) (q - q') ⟨p, ⟨x, hx⟩⟩) (norm_nonneg x)
        _ ≤ ‖x‖ * d := mul_le_mul_of_nonneg_left h (norm_nonneg x)
        _ = _ := mul_comm _ _
  · intro h
    apply lp.norm_le_of_forall_le hd
    intro i
    have hi := h i.1 i.2.1
    simp only [parameterGraphValue, dite_eq_right i.2.2, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg i.2.1)] at hi
    rw [mul_comm d] at hi
    exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr i.2.2)).mp hi

end HolomorphicAnosov
