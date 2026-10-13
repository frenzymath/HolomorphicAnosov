import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.RingTheory.Complex

namespace HolomorphicAnosov

universe u

variable {d : ℕ}

open scoped ComplexOrder in
/-- Positive Hermitian Gram determinants. (Demailly, VI §4.) -/
theorem hermitian_core_det_pos {V : Type*} [AddCommGroup V] [Module ℂ V]
    (k : InnerProductSpace.Core ℂ V) (v : Fin d → V) (hv : LinearIndependent ℂ v) :
    0 < (Matrix.det fun i j ↦ k.inner (v j) (v i)).re := by
  let : InnerProductSpace.Core ℂ V := k
  let : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ V := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  have hpos := (Matrix.posDef_gram_of_linearIndependent (𝕜 := ℂ) hv).det_pos
  change 0 < (Matrix.gram ℂ v).transpose.det.re
  rw [Matrix.det_transpose]
  exact (Complex.lt_def.mp hpos).1


end HolomorphicAnosov
