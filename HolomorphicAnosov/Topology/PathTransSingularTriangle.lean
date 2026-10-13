import HolomorphicAnosov.Topology.PathSingularSimplex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Convexity
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- Concatenation is the middle face of a singular triangle whose remaining faces
are the second and first paths, in that order.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 proof p.166. For the concatenated
path p, evaluate p at t1/2+t2 on the ordered triangle. Its edge parameters are
(t+1)/2, t, and t/2, so the edge restrictions are the second path, p, and first path.
The extended path supplies continuity without a separate range proof. -/
theorem pathTrans_singular_triangle {X : Type u} [TopologicalSpace X]
    {x y z : X} (α : Path x y) (β : Path y z) :
    ∃ s : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌,
      (TopCat.toSSet.obj (TopCat.of X)).δ 0 s = pathSingularSimplex β ∧
      (TopCat.toSSet.obj (TopCat.of X)).δ 1 s = pathSingularSimplex (α.trans β) ∧
      (TopCat.toSSet.obj (TopCat.of X)).δ 2 s = pathSingularSimplex α := by
  let f : Fin 3 → Fin 2 := ![0, 0, 1]
  let g : Fin 3 → Fin 2 := ![0, 1, 1]
  let A : C(StdSimplex ℝ (Fin 3), X) :=
    ⟨fun p ↦ (α.trans β).extend
      (((StdSimplex.homeomorphI (p.map f) : unitInterval) : ℝ) / 2 +
       ((StdSimplex.homeomorphI (p.map g) : unitInterval) : ℝ) / 2), by
        apply (α.trans β).continuous_extend.comp
        fun_prop⟩
  refine ⟨(TopCat.toSSetObjEquiv _ _).symm A, ?_, ?_, ?_⟩
  all_goals
    apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
    apply ContinuousMap.ext
    intro p
  · change A (p.map (0 : Fin 3).succAbove) = β (StdSimplex.homeomorphI p)
    dsimp [A]
    simp only [← StdSimplex.map_comp]
    have hf : f ∘ (Fin.succ : Fin 2 → Fin 3) = id := by ext i; fin_cases i <;> rfl
    have hg : g ∘ (Fin.succ : Fin 2 → Fin 3) = fun _ ↦ 1 := by ext i; fin_cases i <;> rfl
    rw [hf, hg]
    simp only [StdSimplex.map_id, StdSimplex.map_const, StdSimplex.homeomorphI_single_one]
    change (α.trans β).extend (_ / 2 + (1 : ℝ) / 2) = _
    rw [Path.extend_trans_of_half_le α β (by
      have := (StdSimplex.homeomorphI p).property.1
      change 0 ≤ ((StdSimplex.homeomorphI p : unitInterval) : ℝ) at this
      change (1 : ℝ) / 2 ≤ _
      linarith)]
    convert β.extend_apply (StdSimplex.homeomorphI p).property using 1; congr 1; ring
  · change A (p.map (1 : Fin 3).succAbove) = (α.trans β) (StdSimplex.homeomorphI p)
    dsimp [A]
    simp only [← StdSimplex.map_comp]
    have hf : f ∘ (1 : Fin 3).succAbove = id := by ext i; fin_cases i <;> rfl
    have hg : g ∘ (1 : Fin 3).succAbove = id := by ext i; fin_cases i <;> rfl
    rw [hf, hg]
    simp only [StdSimplex.map_id]
    rw [add_halves, Path.extend_apply]
  · change A (p.map (2 : Fin 3).succAbove) = α (StdSimplex.homeomorphI p)
    dsimp [A]
    simp only [← StdSimplex.map_comp]
    have hf : f ∘ (2 : Fin 3).succAbove = fun _ ↦ 0 := by ext i; fin_cases i <;> rfl
    have hg : g ∘ (2 : Fin 3).succAbove = id := by ext i; fin_cases i <;> rfl
    rw [hf, hg]
    simp only [StdSimplex.map_id, StdSimplex.map_const, StdSimplex.homeomorphI_single_zero]
    change (α.trans β).extend ((0 : ℝ) / 2 + _ / 2) = _
    rw [Path.extend_trans_of_le_half α β (by
      have := (StdSimplex.homeomorphI p).property.2
      change ((StdSimplex.homeomorphI p : unitInterval) : ℝ) ≤ 1 at this
      change _ ≤ (1 : ℝ) / 2
      linarith)]
    convert α.extend_apply (StdSimplex.homeomorphI p).property using 1; congr 1; ring

end HolomorphicAnosov.Topology
