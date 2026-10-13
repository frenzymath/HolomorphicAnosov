import HolomorphicAnosov.Topology.PathSingularSimplex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Tactic.FinCases

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory Convexity
open scoped Simplicial
universe u
namespace HolomorphicAnosov.Topology

/-- The two ordered triangles of a based-loop homotopy square have a common
diagonal, equal side edges, and the original loops as the remaining faces.
Source: Hatcher, Algebraic Topology, Theorem 2A.1, p.166.
Proof: on barycentric coordinates use the triangle maps
`(t₂,t₁+t₂)` and `(t₁+t₂,t₂)` into the homotopy square. Restriction to
the three ordered edges gives respectively the side, diagonal, and initial
loop, and the final loop, diagonal, and side. Endpoint-fixedness identifies
the side edges. -/
theorem pathHomotopy_singular_triangles {X : Type u} [TopologicalSpace X]
    {x : X} {α β : Path x x} (H : α.Homotopy β) :
    ∃ s t : (TopCat.toSSet.obj (TopCat.of X)) _⦋2⦌,
      (TopCat.toSSet.obj (TopCat.of X)).δ 0 s =
        (TopCat.toSSet.obj (TopCat.of X)).δ 2 t ∧
      (TopCat.toSSet.obj (TopCat.of X)).δ 1 s =
        (TopCat.toSSet.obj (TopCat.of X)).δ 1 t ∧
      (TopCat.toSSet.obj (TopCat.of X)).δ 2 s = pathSingularSimplex α ∧
      (TopCat.toSSet.obj (TopCat.of X)).δ 0 t = pathSingularSimplex β := by
  let f : Fin 3 → Fin 2 := ![0, 0, 1]
  let g : Fin 3 → Fin 2 := ![0, 1, 1]
  let A : C(StdSimplex ℝ (Fin 3), X) :=
    ⟨fun p ↦ H (StdSimplex.homeomorphI (p.map f), StdSimplex.homeomorphI (p.map g)),
      H.continuous.comp ((StdSimplex.homeomorphI.continuous.comp
        (StdSimplex.continuous_map ℝ f)).prodMk
          (StdSimplex.homeomorphI.continuous.comp (StdSimplex.continuous_map ℝ g)))⟩
  let B : C(StdSimplex ℝ (Fin 3), X) :=
    ⟨fun p ↦ H (StdSimplex.homeomorphI (p.map g), StdSimplex.homeomorphI (p.map f)),
      H.continuous.comp ((StdSimplex.homeomorphI.continuous.comp
        (StdSimplex.continuous_map ℝ g)).prodMk
          (StdSimplex.homeomorphI.continuous.comp (StdSimplex.continuous_map ℝ f)))⟩
  refine ⟨(TopCat.toSSetObjEquiv _ _).symm A,
    (TopCat.toSSetObjEquiv _ _).symm B, ?_, ?_, ?_, ?_⟩
  all_goals
    apply (TopCat.toSSetObjEquiv (TopCat.of X) _).injective
    apply ContinuousMap.ext
    intro p
  · change A (p.map (0 : Fin 3).succAbove) = B (p.map (2 : Fin 3).succAbove)
    dsimp [A, B]
    simp only [← StdSimplex.map_comp]
    have hf : f ∘ (Fin.succ : Fin 2 → Fin 3) = id := by ext i; fin_cases i <;> rfl
    have hg : g ∘ (Fin.succ : Fin 2 → Fin 3) = fun _ ↦ 1 := by ext i; fin_cases i <;> rfl
    have hf' : f ∘ (2 : Fin 3).succAbove = fun _ ↦ 0 := by ext i; fin_cases i <;> rfl
    have hg' : g ∘ (2 : Fin 3).succAbove = id := by ext i; fin_cases i <;> rfl
    rw [hf, hg, hf', hg']
    simp
  · change A (p.map (1 : Fin 3).succAbove) = B (p.map (1 : Fin 3).succAbove)
    dsimp [A, B]
    simp only [← StdSimplex.map_comp]
    have hf : f ∘ (1 : Fin 3).succAbove = id := by ext i; fin_cases i <;> rfl
    have hg : g ∘ (1 : Fin 3).succAbove = id := by ext i; fin_cases i <;> rfl
    rw [hf, hg]
  · change A (p.map (2 : Fin 3).succAbove) = α (StdSimplex.homeomorphI p)
    dsimp [A]
    simp only [← StdSimplex.map_comp]
    have hf : f ∘ (2 : Fin 3).succAbove = fun _ ↦ 0 := by ext i; fin_cases i <;> rfl
    have hg : g ∘ (2 : Fin 3).succAbove = id := by ext i; fin_cases i <;> rfl
    rw [hf, hg]
    simp
  · change B (p.map (0 : Fin 3).succAbove) = β (StdSimplex.homeomorphI p)
    dsimp [B]
    simp only [← StdSimplex.map_comp]
    have hf : f ∘ (Fin.succ : Fin 2 → Fin 3) = id := by ext i; fin_cases i <;> rfl
    have hg : g ∘ (Fin.succ : Fin 2 → Fin 3) = fun _ ↦ 1 := by ext i; fin_cases i <;> rfl
    rw [hf, hg]
    simp

end HolomorphicAnosov.Topology
