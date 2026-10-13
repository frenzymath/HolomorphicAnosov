import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Normalized parameter graph carrier

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977),
Sublemma 5.2, pp. 54–55, and parameter insertion on p. 62.
The dependent `lp` space at exponent infinity stores normalized graph values at
nonzero inputs. Multiplication by the input norm recovers the graph, with value
zero at zero. The unit-slope subset imposes the original fibrewise Lipschitz bound;
no topology on the parameter type or continuity in the parameter is imposed.
-/

noncomputable section
open scoped Classical
namespace HolomorphicAnosov

variable {A : Type*} (E F : A → Type*)
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]

/-- The raw normalized graph family of HPS Sublemma 5.2, pp.54–55, with the
parameter insertion of p.62. A coordinate records `s p x / ‖x‖` for `x ≠ 0`.
The dependent bounded-function norm retains every original receiving fibre norm. -/
abbrev ParameterGraphCarrier :=
  lp (fun i : Sigma (fun p ↦ {x : E p // x ≠ 0}) ↦ F i.1) ⊤

/-- Recover a centered graph from its normalized coordinates, HPS pp.54–55.
The zero value is explicitly zero; only nonzero inputs access an lp coordinate. -/
def parameterGraphValue (q : ParameterGraphCarrier E F) (p : A) (x : E p) : F p :=
  if hx : x = 0 then 0 else ‖x‖ • q ⟨p, ⟨x, hx⟩⟩

/-- The unit-slope graph carrier in HPS Sublemma 5.2, using the actual recovered
maps and their original fibre norms, without any parameter continuity condition. -/
def parameterGraphUnitSet : Set (ParameterGraphCarrier E F) :=
  {q | ∀ p, LipschitzWith 1 (parameterGraphValue E F q p)}

end HolomorphicAnosov

