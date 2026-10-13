import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Logic.Function.Iterate

/-!
Natural-number iterates of a smooth real diffeomorphism are smooth diffeomorphisms with inverse
given by the corresponding iterate of its inverse.
-/

namespace HolomorphicAnosov

universe u v

open scoped ContDiff
noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H]
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]

def realIterate (I : ModelWithCorners ℝ E H)
    (g : Diffeomorph I I X X ∞) (n : ℕ) : Diffeomorph I I X X ∞ :=
  { toEquiv :=
      { toFun := (g : X → X)^[n]
        invFun := (g.symm : X → X)^[n]
        left_inv := g.left_inv.iterate n
        right_inv := g.right_inv.iterate n }
    contMDiff_toFun := g.contMDiff_toFun.iterate n
    contMDiff_invFun := g.symm.contMDiff_toFun.iterate n }

end
end HolomorphicAnosov
