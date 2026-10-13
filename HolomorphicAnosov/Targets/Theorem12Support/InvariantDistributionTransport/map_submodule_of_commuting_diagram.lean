import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Basic.Real.Basic

namespace HolomorphicAnosov.Theorem12SupportW4

section LinearDiagram
variable {A B C D : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
  [Module ℝ A] [Module ℝ B] [Module ℝ C] [Module ℝ D]

/-- In a commuting square of linear maps, if `f` maps `s` onto `t`, then `g` maps the image of `s`
under `i` onto the image of `t` under `j`. -/
theorem map_submodule_of_commuting_diagram
    (s : Submodule ℝ A) (t : Submodule ℝ B)
    (f : A →ₗ[ℝ] B) (i : A →ₗ[ℝ] C) (j : B →ₗ[ℝ] D) (g : C →ₗ[ℝ] D)
    (hinv : s.map f = t) (hcomm : g.comp i = j.comp f) :
    (s.map i).map g = t.map j := by
  rw [← Submodule.map_comp, hcomm, Submodule.map_comp, hinv]

end LinearDiagram
end HolomorphicAnosov.Theorem12SupportW4
