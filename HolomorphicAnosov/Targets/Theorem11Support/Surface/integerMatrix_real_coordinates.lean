import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import HolomorphicAnosov.Targets.Theorem11Support.Surface.integerMatrix_apply
import HolomorphicAnosov.Targets.Theorem11Support.Surface.latticeEquiv_apply

/-!
Real coordinates in an integral lattice basis intertwine the complex-linear map with its integer matrix. (Zhang, §2, p.4)
-/

noncomputable section

namespace HolomorphicAnosov.Theorem11SupportW10

universe u

/-- A real coordinate equivalence agreeing with the integral basis coordinates intertwines
`B.linear` with `integerMatrix L B b` on every ambient vector. -/
theorem integerMatrix_real_coordinates (L : FullComplexLattice 2)
    (B : LatticeLinearEquiv L) (b : Module.Basis (Fin 4) ℤ L.lattice)
    (P : ComplexModel 2 ≃L[ℝ] (Fin 4 → ℝ))
    (hP : ∀ (x : L.lattice) (i : Fin 4), P x i = (b.repr x i : ℝ)) :
    ∀ (v : ComplexModel 2) (i : Fin 4), P (B.linear v) i =
      ∑ j : Fin 4, (integerMatrix L B b i j : ℝ) * P v j := by
  let := L.discrete
  let := L.full
  let c := b.ofZLatticeBasis ℝ L.lattice
  let F := P.toLinearMap.comp (B.linear.restrictScalars ℝ).toLinearMap
  let G := (Matrix.mulVecLin (fun i j : Fin 4 ↦
    (integerMatrix L B b i j : ℝ))).comp P.toLinearMap
  have hFG : F = G := by
    apply c.ext
    intro j
    ext i
    change P (B.linear (c j)) i =
      ∑ k : Fin 4, (integerMatrix L B b i k : ℝ) * P (c j) k
    simp only [c, Module.Basis.ofZLatticeBasis_apply]
    rw [← latticeEquiv_apply L B (b j), hP]
    simp [hP, integerMatrix_apply, Module.Basis.repr_self, Finsupp.single_apply]
  intro v i
  exact congrFun (LinearMap.congr_fun hFG v) i

end HolomorphicAnosov.Theorem11SupportW10

