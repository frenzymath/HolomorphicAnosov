import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace HolomorphicAnosov

/-! This file identifies a complex vector space of dimension one with `ℂ` by a complex-linear
equivalence. (Ghys, Lemma 2.1, p. 589; Lemma 3.3, p. 592) -/

/-- A complex vector space of dimension one admits a complex-linear equivalence with `ℂ`. -/
theorem exists_complex_line_equiv_of_finrank_one
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (hV : Module.finrank ℂ V = 1) :
    Nonempty (V ≃ₗ[ℂ] ℂ) := by
  exact ⟨(Module.nonempty_linearEquiv_of_finrank_eq_one hV).some.symm⟩

end HolomorphicAnosov

