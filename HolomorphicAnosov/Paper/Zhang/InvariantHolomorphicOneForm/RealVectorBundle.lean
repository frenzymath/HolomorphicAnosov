import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Tactic

open Bundle Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle


universe u

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle ℂ F E]

/-- A complex vector bundle is a real vector bundle after restriction of scalars, with transition
maps given by the real restrictions of the complex transition maps. -/
theorem real_vector_bundle : VectorBundle ℝ F E := by
  have hlinear : ∀ (e : Trivialization F (π F E)) [MemTrivializationAtlas e],
      e.IsLinear ℝ := by
    intro e he
    constructor
    intro x hx
    have hc := e.coe_linearMapAt_of_mem (R := ℂ) hx
    rw [← hc]
    exact (e.linearMapAt ℂ x).isLinearMap_of_compatibleSMul ℝ
  refine ⟨hlinear, ?_⟩
  intro e e' he he'
  let : e.IsLinear ℝ := hlinear e
  let : e'.IsLinear ℝ := hlinear e'
  have hcont := (ContinuousLinearMap.continuous_restrictScalars (E := F) (F := F) ℝ).comp_continuousOn
    (continuousOn_coordChange ℂ e e')
  apply hcont.congr
  intro x hx
  ext v
  change e.coordChangeL ℝ e' x v = e.coordChangeL ℂ e' x v
  rw [Trivialization.coordChangeL_apply (R := ℝ) e e' hx,
    Trivialization.coordChangeL_apply (R := ℂ) e e' hx]


end HolomorphicAnosov.OneFormBundle
