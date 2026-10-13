import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import HolomorphicAnosov.Geometry.ComplexProjectiveLineBase
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveSourceMk
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveFunMk
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveOtherNe
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveInvMem
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveRightInv
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveLeftInv
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveQuotientMap
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveSourceOpen
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveFunContinuous
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveInvContinuous
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveTransition
import HolomorphicAnosov.Geometry.ComplexProjectiveLineProjectiveOverlapNe





/-! This file equips the complex projective line with its two homogeneous-coordinate charts and complex manifold structure. (Demailly, V §15.A, p. 277; Ghys, p. 597).
-/
namespace HolomorphicAnosov

open scoped ContDiff

noncomputable section

/-- The explicit quotient ratio charts and normalized inverses satisfy the required source, continuity, and inverse properties. (Demailly, V §15.A, p. 277). -/
theorem complexProjectiveLineChart_properties (j : Fin 2) :
    IsOpen (complexProjectiveLineChartSource j) ∧
    ContinuousOn (complexProjectiveLineChartFun j) (complexProjectiveLineChartSource j) ∧
    Continuous (complexProjectiveLineChartInv j) ∧
    (∀ z, complexProjectiveLineChartInv j z ∈ complexProjectiveLineChartSource j) ∧
    (∀ p ∈ complexProjectiveLineChartSource j,
      complexProjectiveLineChartInv j (complexProjectiveLineChartFun j p) = p) ∧
    (∀ z, complexProjectiveLineChartFun j (complexProjectiveLineChartInv j z) = z) := by
  exact ⟨projective_source_open j, projective_fun_continuous j, projective_inv_continuous j,
    projective_inv_mem j, projective_left_inv j, projective_right_inv j⟩

/-- The `j`th homogeneous chart is an open partial homeomorphism with the displayed ratio map and normalized inverse. (Demailly, V §15.A, p. 277). -/
def complexProjectiveLineChart (j : Fin 2) :
    OpenPartialHomeomorph ComplexProjectiveLine (ComplexModel 1) where
  toFun := complexProjectiveLineChartFun j
  invFun := complexProjectiveLineChartInv j
  source := complexProjectiveLineChartSource j
  target := Set.univ
  map_source' := fun {_} _ ↦ Set.mem_univ _
  map_target' := fun {z} _ ↦ (complexProjectiveLineChart_properties j).2.2.2.1 z
  left_inv' := fun {p} h ↦ (complexProjectiveLineChart_properties j).2.2.2.2.1 p h
  right_inv' := fun {z} _ ↦ (complexProjectiveLineChart_properties j).2.2.2.2.2 z
  continuousOn_toFun := (complexProjectiveLineChart_properties j).2.1
  continuousOn_invFun := (complexProjectiveLineChart_properties j).2.2.1.continuousOn
  open_source := (complexProjectiveLineChart_properties j).1
  open_target := isOpen_univ

/-- The finite point is the projective class `[z:1]`. (Demailly, V §15.A, p. 277; Ghys, p. 597). -/
def complexProjectiveLineFinite (z : ℂ) : ComplexProjectiveLine :=
  complexProjectiveLineChartInv 1 (fun _ ↦ z)

/-- The point at infinity is the projective class `[1:0]`. (Demailly, V §15.A, p. 277). -/
def complexProjectiveLineInfinity : ComplexProjectiveLine :=
  complexProjectiveLineChartInv 0 0

/-- The two homogeneous chart sources cover the projective line. (Demailly, V §15.A, p. 277). -/
theorem complexProjectiveLineChart_cover (p : ComplexProjectiveLine) :
    p ∈ complexProjectiveLineChartSource 1 ∨ p ∈ complexProjectiveLineChartSource 0 := by
  by_cases h₁ : p.rep 1 ≠ 0
  · exact Or.inl h₁
  · right
    intro h₀
    apply p.rep_nonzero
    ext i
    fin_cases i
    · exact h₀
    · exact not_ne_iff.mp h₁

/-- The preferred chart uses the finite coordinate whenever it is defined. (Demailly, V §15.A, p. 277). -/
def complexProjectiveLineChartAt (p : ComplexProjectiveLine) :
    OpenPartialHomeomorph ComplexProjectiveLine (ComplexModel 1) := by
  classical
  exact if p ∈ complexProjectiveLineChartSource 1 then complexProjectiveLineChart 1
    else complexProjectiveLineChart 0

/-- This is the explicit two-chart atlas on the quotient topology. (Demailly, V §15.A, p. 277). -/
instance complexProjectiveLineChartedSpace : ChartedSpace (ComplexModel 1)
    ComplexProjectiveLine where
  atlas := Set.range complexProjectiveLineChart
  chartAt := complexProjectiveLineChartAt
  mem_chart_source := fun p ↦ by
    unfold complexProjectiveLineChartAt
    split_ifs with h
    · exact h
    · exact (complexProjectiveLineChart_cover p).resolve_left h
  chart_mem_atlas := fun p ↦ by
    unfold complexProjectiveLineChartAt
    split_ifs
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- The two homogeneous-coordinate charts are compatible as a complex atlas. (Demailly, V §15.A, p. 277). -/
theorem complexProjectiveLine_isManifold :
    IsManifold (complexModel 1) ∞ ComplexProjectiveLine := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨j, rfl⟩ := he
  obtain ⟨k, rfl⟩ := he'
  simp only [complexModel, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.range_id, Set.preimage_id, Set.inter_univ,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  change ContDiffOn ℂ ∞
    (complexProjectiveLineChartFun k ∘ complexProjectiveLineChartInv j)
    (Set.univ ∩ {z | complexProjectiveLineChartInv j z ∈ complexProjectiveLineChartSource k})
  rw [Set.univ_inter]
  by_cases hjk : j = k
  · subst k
    apply contDiffOn_id.congr
    intro z _
    exact projective_right_inv j z
  · have hnonzero : ∀ z ∈ {z | complexProjectiveLineChartInv j z ∈ complexProjectiveLineChartSource k},
        z 0 ≠ 0 := fun z hz ↦ projective_overlap_ne j k hjk z hz
    have hinv : ContDiffOn ℂ ∞ (fun z : ComplexModel 1 ↦ fun _ : Fin 1 ↦ (z 0)⁻¹)
        {z | complexProjectiveLineChartInv j z ∈ complexProjectiveLineChartSource k} := by
      apply contDiffOn_pi.mpr
      intro i
      exact (contDiff_apply ℂ ℂ (0 : Fin 1)).contDiffOn.inv hnonzero
    apply hinv.congr
    intro z _
    exact (projective_transition j k z).trans (ite_eq_right hjk)

/-- The homogeneous-coordinate atlas defines the complex manifold structure on the projective line. (Demailly, V §15.A, p. 277). -/
instance complexProjectiveLineIsManifold :
    IsManifold (complexModel 1) ∞ ComplexProjectiveLine :=
  complexProjectiveLine_isManifold

/-- A local biholomorphism into the projective line is locally an open homeomorphism that is complex smooth in both directions. (Ghys, p. 597; Demailly, V §15.A, p. 277). -/
def IsLocalBiholomorphToProjectiveLine {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (f : X → ComplexProjectiveLine) : Prop :=
  ∀ x, ∃ e : OpenPartialHomeomorph X ComplexProjectiveLine,
    x ∈ e.source ∧ Set.EqOn e f e.source ∧
    ContMDiffOn (complexModel d) (complexModel 1) ∞ e e.source ∧
    ContMDiffOn (complexModel 1) (complexModel d) ∞ e.symm e.target



end

end HolomorphicAnosov
