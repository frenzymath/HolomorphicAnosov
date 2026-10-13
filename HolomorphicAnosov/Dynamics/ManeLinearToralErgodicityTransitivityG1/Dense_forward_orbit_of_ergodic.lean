import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1.Definitions

import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Eigenspace.Matrix

namespace HolomorphicAnosov.Dynamics
open MeasureTheory
noncomputable section

theorem dense_forward_orbit_of_ergodic {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {f : X → X} (hf : Continuous f) (he : Ergodic f μ) :
    ∃ x : X, DenseRange (fun j : ℕ ↦ f^[j] x) := by
  classical
  let B := TopologicalSpace.countableBasis X
  let S (U : Set X) := ⋃ j : ℕ, f^[j] ⁻¹' U
  have hS (U : Set X) (hU : IsOpen U) (hne : U.Nonempty) : ∀ᵐ x ∂μ, x ∈ S U := by
    have hSo : IsOpen (S U) := isOpen_iUnion fun j ↦ hU.preimage (hf.iterate j)
    have hsub : f ⁻¹' S U ⊆ S U := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
      apply Set.mem_iUnion.mpr
      exact ⟨j + 1, by simpa only [Set.mem_preimage, Function.iterate_succ_apply] using hj⟩
    rcases he.ae_empty_or_univ_of_preimage_ae_le hSo.measurableSet.nullMeasurableSet
      (Filter.Eventually.of_forall hsub) with hnull | hfull
    · have hSUzero : μ (S U) = 0 := MeasureTheory.ae_eq_empty.mp hnull
      have hUz : μ U = 0 := measure_mono_null (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨0, hx⟩) hSUzero
      exact False.elim (hU.measure_ne_zero μ hne hUz)
    · filter_upwards [hfull] with x hx
      simpa only [Set.mem_univ, eq_iff_iff, iff_true] using hx
  have hcommon : ∀ᵐ x ∂μ, ∀ U : B, x ∈ S U := by
    rw [MeasureTheory.ae_all_iff]
    intro U
    exact hS U (TopologicalSpace.isOpen_of_mem_countableBasis U.property)
      (Set.nonempty_iff_ne_empty.mpr fun h ↦
        TopologicalSpace.empty_notMem_countableBasis X (h ▸ U.property))
  obtain ⟨x, hx⟩ := hcommon.exists
  refine ⟨x, dense_iff_inter_open.mpr ?_⟩
  intro U hU hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨V, hVB, hyV, hVU⟩ :=
    (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open hy hU
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hx ⟨V, hVB⟩)
  exact ⟨f^[j] x, ⟨hVU hj, ⟨j, rfl⟩⟩⟩

end
end HolomorphicAnosov.Dynamics
