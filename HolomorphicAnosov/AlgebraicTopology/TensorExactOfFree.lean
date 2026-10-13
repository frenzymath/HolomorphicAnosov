import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# Tensoring exact linear maps with a free module

A free module is flat, so tensoring an exact sequence of R-linear maps with it
preserves exactness.  This is the algebraic step used in Hatcher's finite-CW
Künneth induction, p.218.
-/

noncomputable section

universe u

namespace HolomorphicAnosov.AlgebraicTopology

variable (R : Type u) [CommRing R]

/-- Tensor an exact pair of R-linear maps with a free module on the right. -/
theorem tensor_exact_of_free (M A B C : Type u)
    [AddCommGroup M] [Module R M] [Module.Free R M]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) :=
  Module.Flat.rTensor_exact M h


end HolomorphicAnosov.AlgebraicTopology
