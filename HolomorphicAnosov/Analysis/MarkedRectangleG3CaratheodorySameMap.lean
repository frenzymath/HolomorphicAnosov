import HolomorphicAnosov.Analysis.InjectiveClosedDiskExtension
import HolomorphicAnosov.Analysis.HolomorphicDiskHomeomorphEnergy
import HolomorphicAnosov.Analysis.ClosedDiskOscillationExtension
import HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCapControl
import HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts
import HolomorphicAnosov.Topology.OpenConnectedFrontierComponent
import HolomorphicAnosov.Analysis.HolomorphicBijOnDerivative
import HolomorphicAnosov.Analysis.Complex.ClosedDiskWinding
import HolomorphicAnosov.Topology.CircleHomeomorphCyclicOrder
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open scoped Topology
namespace HolomorphicAnosov.Analysis.MarkedRectangle
noncomputable section
/-- The open unit disk in the complex plane. -/
def unitDisk : Set ℂ := {z | ‖z‖ < 1}

/-- The closed unit disk, including its circle boundary. -/
def closedUnitDisk : Set ℂ := {z | ‖z‖ ≤ 1}

/-- A counterclockwise parametrization with period one of the unit circle. -/
def circlePhase (t : ℝ) : Circle := Circle.exp (2 * Real.pi * t)

/-- The phase parametrization has period one, by the fundamental exponential period.
This is the endpoint identity used when closing lifted circle paths in the positive
orientation argument. -/
theorem circlePhase_add_one (t : ℝ) : circlePhase (t + 1) = circlePhase t := by
  rw [circlePhase, mul_add, Circle.exp_add]
  rw [show 2 * Real.pi * (1 : ℝ) = 2 * Real.pi by ring]
  rw [show Circle.exp (2 * Real.pi) = 1 by
    apply Circle.ext
    rw [Circle.coe_exp]
    rw [show (2 * Real.pi : ℝ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I by norm_num]
    simp]
  simp [circlePhase]

/-- Iterating the unit-period identity gives the same parametrized circle point
after any natural-number number of full turns. This is the finite-period form
used when extending a lifted boundary phase across successive intervals. -/
theorem circlePhase_add_nat (t : ℝ) (n : ℕ) :
    circlePhase (t + n) = circlePhase t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    rw [show t + (↑n + 1 : ℝ) = (t + ↑n) + 1 by ring]
    rw [circlePhase_add_one, ih]

/-- Every phase point lies on the unit circle and hence in the closed disk.

This is the elementary geometric fact behind the canonical inclusion of the phase
parametrization into `closedUnitDisk`; it follows from the norm-one property of the
complex exponential on purely imaginary inputs. -/
private theorem circlePhase_mem_closedUnitDisk (t : ℝ) :
    (circlePhase t : ℂ) ∈ closedUnitDisk := by
  change ‖(circlePhase t : ℂ)‖ ≤ 1
  rw [circlePhase, Circle.coe_exp, Complex.norm_exp_ofReal_mul_I]

/-- The canonical inclusion of the unit circle into the closed unit disk. -/
def circleInClosedDisk (z : Circle) : closedUnitDisk :=
  ⟨(z : ℂ), by simp [closedUnitDisk]⟩

/-- A Jordan boundary is the image of a topological embedding of the circle.
No differentiability or rectifiability is required. Source: Cairns, pp.860–867. -/
def HasJordanBoundary (Q : Set ℂ) : Prop :=
  ∃ j : Circle → ℂ, Topology.IsEmbedding j ∧ Set.range j = frontier Q

/-- Winding number one of a continuous loop about a point, expressed by an actual
continuous logarithm lift on the closed parameter interval. Exponentiation ensures
avoidance of the point; the endpoint increment fixes the positive orientation.
Source: Tao 246A Notes 3, Theorem 50 and orientation convention immediately following it. -/
def WindsOncePositively (γ : ℝ → ℂ) (q : ℂ) : Prop :=
  ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = γ 1 ∧
    ∃ L : C(Set.Icc (0 : ℝ) 1, ℂ),
      (∀ t : Set.Icc (0 : ℝ) 1, Complex.exp (L t) = γ t - q) ∧
      L ⟨1, by simp⟩ - L ⟨0, by simp⟩ = (2 * Real.pi : ℂ) * Complex.I

/-- A Jordan boundary parametrization is positive if its loop has winding number
one about every point of the region. This is a definition, not an orientation premise
for the conformal extension theorem. Source: Tao 246A Notes 3 after Theorem 50. -/
def PositiveBoundaryParametrization (Q : Set ℂ) (β : Circle ≃ₜ frontier Q) : Prop :=
  ∀ q ∈ Q, WindsOncePositively (fun t ↦ (β (circlePhase t) : ℂ)) q

/-- Four circle points are positively cyclic when they have increasing angle
representatives in a single period. The strict inequalities enforce distinctness
and allow any initial cut. Source: Lyubich §1.11, pp.53–54. -/
def PositiveCircleFour (u : Fin 4 → Circle) : Prop :=
  ∃ t : Fin 4 → ℝ, StrictMono t ∧ t 3 < t 0 + 1 ∧
    ∀ i, u i = circlePhase (t i)

/-- Four boundary marks are positively cyclic if they occur in that order in a
positive topological boundary parametrization. Source: Lyubich §1.11, pp.53–54.
The parametrization is required to wind positively; orientation is not arbitrary. -/
def PositiveBoundaryFour (Q : Set ℂ) (p : Fin 4 → ℂ) : Prop :=
  ∃ β : Circle ≃ₜ frontier Q, PositiveBoundaryParametrization Q β ∧
    ∃ u : Fin 4 → Circle, PositiveCircleFour u ∧ ∀ i, (β (u i) : ℂ) = p i

/-- Agreement with the literal original map at every point of its open-disk domain.
Off-disk values of the total function representing that map play no role. -/
def ExtendsDiskMap (Q : Set ℂ) (φ : ℂ → ℂ)
    (Φ : closedUnitDisk ≃ₜ closure Q) : Prop :=
  ∀ (z : ℂ) (hz : z ∈ unitDisk),
    (Φ ⟨z, by
      change ‖z‖ ≤ 1
      exact le_of_lt (show ‖z‖ < 1 from hz)⟩ : ℂ) = φ z

open HolomorphicAnosov Set Metric
lemma positive_of_winding {Q : Set ℂ} (β : Circle ≃ₜ frontier Q) (q : ℂ)
    (hb : ∀ z, (β z : ℂ) ≠ q)
    (hw : loopWinding ⟨fun z ↦ (β z : ℂ), by fun_prop⟩ q hb = 1) :
    WindsOncePositively (fun t ↦ (β (circlePhase t) : ℂ)) q := by
  let γ : ComplexLoop := ⟨fun z ↦ (β z : ℂ), by fun_prop⟩
  obtain ⟨L, hL, hinc⟩ := loopWinding_lift γ q hb
  refine ⟨?_, ?_, L, hL, ?_⟩
  · exact (γ.continuous.comp (Circle.exp.continuous.comp
      (continuous_const.mul continuous_id))).continuousOn
  · change (β (circlePhase 0) : ℂ) = β (circlePhase 1)
    rw [show circlePhase (1 : ℝ) = circlePhase 0 by simpa using circlePhase_add_one 0]
  · rw [hw] at hinc
    simpa using sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hinc)
lemma winding_of_positive {Q : Set ℂ} (β : Circle ≃ₜ frontier Q) (q : ℂ)
    (hb : ∀ z, (β z : ℂ) ≠ q)
    (hp : WindsOncePositively (fun t ↦ (β (circlePhase t) : ℂ)) q) :
    loopWinding ⟨fun z ↦ (β z : ℂ), by fun_prop⟩ q hb = 1 := by
  obtain ⟨_, _, L, hL, hinc⟩ := hp
  apply loopWinding_eq_of_increment ⟨fun z ↦ (β z : ℂ), by fun_prop⟩ q hb L hL 1
  simpa using hinc
lemma extension_positive {Q : Set ℂ} {φ : ℂ → ℂ} (hQ : IsOpen Q)
    (hh : DifferentiableOn ℂ φ unitDisk) (hb : BijOn φ unitDisk Q)
    (hd : ∀ x ∈ unitDisk, deriv φ x ≠ 0)
    (Φ : closedUnitDisk ≃ₜ closure Q) (he : ExtendsDiskMap Q φ Φ)
    (β : Circle ≃ₜ frontier Q)
    (hβ : ∀ ζ, (β ζ : ℂ) = (Φ (circleInClosedDisk ζ) : ℂ)) :
    PositiveBoundaryParametrization Q β := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := hb.surjOn hq
  have havoid : ∀ ζ, (β ζ : ℂ) ≠ φ x := by
    intro ζ heq
    have hn := (β ζ).property.2
    rw [hQ.interior_eq] at hn
    exact hn (heq ▸ hq)
  apply positive_of_winding β (φ x) havoid
  let F : closedBall (0 : ℂ) 1 → ℂ := fun z ↦ (Φ ⟨z, by simpa only [closedUnitDisk, mem_ofPred_eq, mem_closedBall, dist_zero_right] using z.property⟩ : ℂ)
  have hF : Continuous F := (continuous_subtype_val.comp Φ.continuous).comp (by fun_prop)
  have hFi : Function.Injective F := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : closedUnitDisk ↦ (z : ℂ)) (Φ.injective (Subtype.ext heq)))
  have hFe : ∀ z (hz : z ∈ ball (0 : ℂ) 1), F ⟨z, ball_subset_closedBall hz⟩ = φ z :=
    fun z hz ↦ he z (by simpa [unitDisk] using hz)
  have hw := closed_disk_winding_one (by simpa [unitDisk, ball, dist_zero_right] using hh)
    F hF hFi hFe (by simpa [unitDisk] using hx) (hd x hx)
  let γ : ComplexLoop := ⟨fun ζ ↦ F ⟨ζ, sphere_subset_closedBall ζ.property⟩,
    hF.comp (continuous_subtype_val.subtype_mk _)⟩
  have hγ : γ = ⟨fun z ↦ (β z : ℂ), by fun_prop⟩ := by
    ext ζ
    exact (hβ ζ).symm
  change ∀ hb : ∀ ζ, γ ζ ≠ φ x, loopWinding γ (φ x) hb = 1 at hw
  rw [hγ] at hw
  exact hw havoid
end
end HolomorphicAnosov.Analysis.MarkedRectangle
namespace HolomorphicAnosov.Analysis.MarkedRectangle
noncomputable section
open HolomorphicAnosov Set Metric Filter
lemma extension_preserves_four {Q : Set ℂ} {φ : ℂ → ℂ} (hQ : IsOpen Q)
    (hh : DifferentiableOn ℂ φ unitDisk) (hb : BijOn φ unitDisk Q)
    (hd : deriv φ 0 ≠ 0)
    (Φ : closedUnitDisk ≃ₜ closure Q) (he : ExtendsDiskMap Q φ Φ)
    (β : Circle ≃ₜ frontier Q)
    (hβ : ∀ ζ, (β ζ : ℂ) = (Φ (circleInClosedDisk ζ) : ℂ)) :
    ∀ p : Fin 4 → ℂ, PositiveBoundaryFour Q p →
      ∃ u : Fin 4 → Circle, PositiveCircleFour u ∧
        ∀ i, (Φ (circleInClosedDisk (u i)) : ℂ) = p i := by
  classical
  intro p hp
  obtain ⟨β', hp', u, ⟨t, ht, htturn, hut⟩, hpu⟩ := hp
  let h := β'.trans β.symm
  let F : ℂ → ℂ := fun z ↦ if hz : z ∈ closedUnitDisk then (Φ ⟨z, hz⟩ : ℂ) else 0
  have hFval (z : ℂ) (hz : z ∈ closedUnitDisk) : F z = (Φ ⟨z, hz⟩ : ℂ) := by simp [F, hz]
  have hzero : (0 : ℂ) ∈ unitDisk := by simp [unitDisk]
  have hFeq : F =ᶠ[𝓝 (0 : ℂ)] φ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    have hzu : z ∈ unitDisk := by simpa [unitDisk] using hz
    exact (hFval z (show ‖z‖ ≤ 1 from le_of_lt hzu)).trans (he z hzu)
  have hF0 : F 0 = φ 0 := (hFval 0 (by simp [closedUnitDisk])).trans (he 0 hzero)
  have hFc : ContinuousOn F (closedBall (0 : ℂ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hh : (fun z : closedBall (0 : ℂ) 1 ↦ F z) =
        fun z : closedBall (0 : ℂ) 1 ↦ (Φ ⟨z, by simpa only [closedUnitDisk, mem_ofPred_eq, mem_closedBall, dist_zero_right] using z.property⟩ : ℂ) := by
      funext z
      exact hFval z _
    change Continuous (fun z : closedBall (0 : ℂ) 1 ↦ F z)
    rw [hh]
    exact (continuous_subtype_val.comp Φ.continuous).comp (by fun_prop)
  have hFd : DifferentiableAt ℂ F 0 :=
    (hh 0 hzero).differentiableAt (by simpa [unitDisk, ball, dist_zero_right] using
      (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball (0 : ℂ) 1))) |>.congr_of_eventuallyEq hFeq
  have hFder : deriv F 0 ≠ 0 := by rw [hFeq.deriv_eq]; exact hd
  have hFi : InjOn F (closedBall (0 : ℂ) 1) := by
    intro z hz w hw heq
    rw [hFval z (by simpa only [closedUnitDisk, mem_ofPred_eq, mem_closedBall, dist_zero_right] using hz),
      hFval w (by simpa only [closedUnitDisk, mem_ofPred_eq, mem_closedBall, dist_zero_right] using hw)] at heq
    exact congrArg Subtype.val (Φ.injective (Subtype.ext heq))
  have hQ0 : F 0 ∈ Q := hF0.symm ▸ hb.mapsTo hzero
  have havoid : ∀ z, (β' z : ℂ) ≠ F 0 := by
    intro z heq
    have hn := (β' z).property.2
    rw [hQ.interior_eq] at hn
    exact hn (heq ▸ hQ0)
  have hw' := winding_of_positive β' (F 0) havoid (hp' (F 0) hQ0)
  have hw := winding_transport_closed_disk hFc hFd hFder hFi ⟨h, h.continuous⟩
  have htrace (z : Circle) : F (h z : ℂ) = (β' z : ℂ) := by
    rw [hFval _ (by simp [closedUnitDisk])]
    exact (hβ (h z)).symm.trans (by simp [h])
  let γ : ComplexLoop := ⟨fun z ↦ F (h z : ℂ), hFc.comp_continuous (by fun_prop) (by intro z; simp)⟩
  have hγ : γ = ⟨fun z ↦ (β' z : ℂ), by fun_prop⟩ := by ext z; exact htrace z
  change ∀ hb : ∀ z, γ z ≠ F 0, loopWinding γ (F 0) hb = _ at hw
  rw [hγ] at hw
  have hwh : loopWinding ⟨fun z ↦ (h z : ℂ), by fun_prop⟩ 0 (fun z ↦ Circle.coe_ne_zero _) = 1 :=
    (hw havoid).symm.trans hw'
  obtain ⟨v, hv, hvturn, htv⟩ := circle_homeomorph_preserves_four h hwh t ht htturn
  refine ⟨fun i ↦ h (u i), ⟨v, hv, hvturn, ?_⟩, ?_⟩
  · intro i
    change h (u i) = circlePhase (v i)
    rw [hut i]
    exact htv i
  · intro i
    exact (hβ (h (u i))).symm.trans ((by simp [h] : (β (h (u i)) : ℂ) = β' (u i)).trans (hpu i))
end
end HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov.Analysis.MarkedRectangle
noncomputable section
open Set Metric
/-- Tao, Theorem 20, extension-uniqueness paragraph: the actual open disk is dense
in its closed disk. Mathlib `closure_ball` and `denseRange_inclusion_iff` implement
the same density without selecting a boundary parametrization. -/
private theorem unitDisk_closure : closure unitDisk = closedUnitDisk := by
  simpa only [unitDisk, closedUnitDisk, Metric.ball, Metric.closedBall, dist_zero_right]
    using closure_ball (0 : ℂ) one_ne_zero

/-- Tao, Theorem 20: interior approaches are dense in the original closed disk;
Mathlib's subtype inclusion uses the unchanged underlying complex coordinates. -/
private theorem diskInclusion_dense :
    DenseRange (Set.inclusion (show unitDisk ⊆ closedUnitDisk from
      fun _ hz ↦ (show ‖_‖ ≤ 1 from le_of_lt hz))) := by
  rw [denseRange_inclusion_iff]
  rw [unitDisk_closure]

/-- Tao, Theorem 20, uniqueness: continuous extensions of the literal given map
agree on the dense open disk, hence everywhere. No boundary injectivity or
orientation premise is used. -/
private theorem extension_unique {Q : Set ℂ} {φ : ℂ → ℂ}
    (Φ Ψ : closedUnitDisk ≃ₜ closure Q)
    (hΦ : ExtendsDiskMap Q φ Φ) (hΨ : ExtendsDiskMap Q φ Ψ) : Φ = Ψ := by
  apply Homeomorph.ext
  have heq : (fun z : closedUnitDisk ↦ (Φ z : ℂ)) =
      (fun z : closedUnitDisk ↦ (Ψ z : ℂ)) := by
    apply diskInclusion_dense.equalizer
      (continuous_subtype_val.comp Φ.continuous)
      (continuous_subtype_val.comp Ψ.continuous)
    funext z
    exact (hΦ z z.property).trans (hΨ z z.property).symm
  intro z
  exact Subtype.ext (congrFun heq z)

/-- Tao, Theorem 20, interior/boundary separation: for any genuine extension,
membership in the original region is exactly membership in the original open disk.
Only the given interior bijection and the extension's injectivity are used. -/
private theorem extension_mem_region_iff {Q : Set ℂ} {φ : ℂ → ℂ}
    (hφ : Set.BijOn φ unitDisk Q) (Φ : closedUnitDisk ≃ₜ closure Q)
    (hΦ : ExtendsDiskMap Q φ Φ) (z : closedUnitDisk) :
    (Φ z : ℂ) ∈ Q ↔ (z : ℂ) ∈ unitDisk := by
  constructor
  · intro hz
    obtain ⟨w, hw, hweq⟩ := hφ.surjOn hz
    let w' : closedUnitDisk := ⟨w, show ‖w‖ ≤ 1 from le_of_lt hw⟩
    have hzw : z = w' := Φ.injective (Subtype.ext (by
      rw [hΦ w hw]
      exact hweq.symm))
    simpa only [hzw] using hw
  · intro hz
    rw [hΦ z hz]
    exact hφ.mapsTo hz

/-- Tao, Theorem 20: an extension of the given interior bijection sends exactly
the source circle to the original frontier. Mathlib `frontier` is closure minus
interior, so this retains the original planar topology and open region. -/
private theorem extension_mem_frontier_iff {Q : Set ℂ} {φ : ℂ → ℂ}
    (hQ : IsOpen Q) (hφ : Set.BijOn φ unitDisk Q)
    (Φ : closedUnitDisk ≃ₜ closure Q) (hΦ : ExtendsDiskMap Q φ Φ)
    (z : closedUnitDisk) :
    (Φ z : ℂ) ∈ frontier Q ↔ ‖(z : ℂ)‖ = 1 := by
  rw [frontier, hQ.interior_eq, Set.mem_sdiff]
  simp only [(Φ z).property, true_and, extension_mem_region_iff hφ Φ hΦ]
  change ¬ ‖(z : ℂ)‖ < 1 ↔ ‖(z : ℂ)‖ = 1
  exact ⟨fun hz ↦ le_antisymm z.property (le_of_not_gt hz), fun hz ↦ by rw [hz]; simp⟩

private theorem continuous_extension_range {Q : Set ℂ} {φ : ℂ → ℂ}
    (hφ : Set.BijOn φ unitDisk Q)
    (F : closedUnitDisk → ℂ) (hF : Continuous F)
    (hInterior : ∀ z : unitDisk,
      F ⟨z, show ‖(z : ℂ)‖ ≤ 1 from le_of_lt z.property⟩ = φ z) :
    Set.range F = closure Q := by
  let ι : unitDisk → closedUnitDisk :=
    Set.inclusion (show unitDisk ⊆ closedUnitDisk from
      fun _ hz ↦ (show ‖_‖ ≤ 1 from le_of_lt hz))
  have hι : DenseRange ι := diskInclusion_dense
  have himage : F '' Set.range ι = Q := by
    ext q
    constructor
    · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
      rw [hInterior]
      exact hφ.mapsTo w.property
    · intro hq
      obtain ⟨w, hw, hweq⟩ := hφ.surjOn hq
      refine ⟨ι ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
      exact (hInterior ⟨w, hw⟩).trans hweq
  have hsubset : Set.range F ⊆ closure Q := by
    rw [← himage]
    exact hF.range_subset_closure_image_dense hι
  have hcompact : IsCompact closedUnitDisk := by
    simpa only [closedUnitDisk, Metric.closedBall, dist_zero_right]
      using isCompact_closedBall (0 : ℂ) 1
  let : CompactSpace closedUnitDisk := isCompact_iff_compactSpace.mp hcompact
  have hclosed : IsClosed (Set.range F) := (isCompact_range hF).isClosed
  apply Set.Subset.antisymm hsubset
  apply closure_minimal _ hclosed
  intro q hq
  rw [← himage] at hq
  exact Set.image_subset_range _ _ hq

/-- Tao, Theorem 20, endpoint exclusion: continuity of the literal interior
inverse prevents any new closed-disk point from mapping into the open region.
The dense equalities are passed to the limit only where that inverse is
continuous, so no boundary continuity of the inverse is presupposed. -/
private theorem continuous_extension_mem_region_iff {Q : Set ℂ} {φ : ℂ → ℂ}
    (hQ : IsOpen Q) (e : unitDisk ≃ₜ Q)
    (he : ∀ z : unitDisk, (e z : ℂ) = φ z)
    (F : closedUnitDisk → ℂ) (hF : Continuous F)
    (hInterior : ∀ z : unitDisk,
      F ⟨z, show ‖(z : ℂ)‖ ≤ 1 from le_of_lt z.property⟩ = φ z)
    (z : closedUnitDisk) : F z ∈ Q ↔ (z : ℂ) ∈ unitDisk := by
  classical
  let inv : ℂ → ℂ := fun y ↦ if hy : y ∈ Q then (e.symm ⟨y, hy⟩ : ℂ) else 0
  have hinv : ContinuousOn inv Q := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun y : Q ↦ inv y)
    have hh : (fun y : Q ↦ inv y) = fun y : Q ↦ (e.symm y : ℂ) := by
      funext y
      simp only [inv, dite_eq_left y.property]
    rw [hh]
    exact continuous_subtype_val.comp e.symm.continuous
  let ι : unitDisk → closedUnitDisk := Set.inclusion (show unitDisk ⊆ closedUnitDisk from
    fun _ hz ↦ (show ‖_‖ ≤ 1 from le_of_lt hz))
  constructor
  · intro hz
    have hc : ContinuousAt (fun x : closedUnitDisk ↦ inv (F x) - (x : ℂ)) z :=
      ((hinv.continuousAt (hQ.mem_nhds hz)).comp hF.continuousAt).sub
        continuous_subtype_val.continuousAt
    have hzero : inv (F z) - (z : ℂ) ∈ closure ({0} : Set ℂ) := by
      apply hc.continuousWithinAt.mem_closure (diskInclusion_dense z)
      rintro _ ⟨w, rfl⟩
      change inv (F (ι w)) - (w : ℂ) ∈ ({0} : Set ℂ)
      rw [hInterior, ← he]
      simp [inv]
    have heq : inv (F z) = (z : ℂ) := by
      simpa only [isClosed_singleton.closure_eq, mem_singleton_iff, sub_eq_zero] using hzero
    have hmem : inv (F z) ∈ unitDisk := by
      simp only [inv, dite_eq_left hz]
      exact (e.symm ⟨F z, hz⟩).property
    exact heq ▸ hmem
  · intro hz
    have h := (e ⟨z, hz⟩).property
    rw [he, ← hInterior] at h
    exact h

/-- Tao, Theorem 20: restrict the genuine same-map closed-disk homeomorphism
to the original circle and frontier. The membership equivalence above supplies
both directions, and compactness of `Circle` makes the resulting continuous
bijection a homeomorphism. This does not assert positive orientation yet. -/
private theorem extension_boundary_homeomorph {Q : Set ℂ} {φ : ℂ → ℂ}
    (hQ : IsOpen Q) (hφ : Set.BijOn φ unitDisk Q)
    (Φ : closedUnitDisk ≃ₜ closure Q) (hΦ : ExtendsDiskMap Q φ Φ) :
    ∃ β : Circle ≃ₜ frontier Q,
      ∀ ζ : Circle, (β ζ : ℂ) = (Φ (circleInClosedDisk ζ) : ℂ) := by
  let b : Circle → frontier Q := fun ζ ↦
    ⟨(Φ (circleInClosedDisk ζ) : ℂ),
      (extension_mem_frontier_iff hQ hφ Φ hΦ _).mpr (Circle.norm_coe ζ)⟩
  have hb : Function.Bijective b := by
    constructor
    · intro ζ ω h
      apply Circle.coe_injective
      have he : circleInClosedDisk ζ = circleInClosedDisk ω :=
        Φ.injective (Subtype.ext (congrArg (fun q : frontier Q ↦ (q : ℂ)) h))
      exact congrArg (fun z : closedUnitDisk ↦ (z : ℂ)) he
    · intro q
      let z := Φ.symm ⟨q, frontier_subset_closure q.property⟩
      have hz : ‖(z : ℂ)‖ = 1 :=
        (extension_mem_frontier_iff hQ hφ Φ hΦ z).mp (by
          simpa only [z, Φ.apply_symm_apply] using q.property)
      let ζ : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
      refine ⟨ζ, ?_⟩
      apply Subtype.ext
      change (Φ (circleInClosedDisk ζ) : ℂ) = (q : ℂ)
      have he : circleInClosedDisk ζ = z := Subtype.ext rfl
      rw [he]
      exact congrArg Subtype.val (Φ.apply_symm_apply _)
  have hc : Continuous b := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp Φ.continuous).comp
      (continuous_subtype_val.subtype_mk _)
  let e := Equiv.ofBijective b hb
  exact ⟨e.toHomeomorphOfContinuousClosed hc hc.isClosedMap, fun _ ↦ rfl⟩


end
end HolomorphicAnosov.Analysis.MarkedRectangle
namespace HolomorphicAnosov.Analysis.MarkedRectangle
noncomputable section
open Set Metric
lemma complete_injective_extension {Q : Set ℂ} {φ : ℂ → ℂ} (hQ : IsOpen Q)
    (hh : DifferentiableOn ℂ φ unitDisk) (hb : BijOn φ unitDisk Q)
    (hd : ∀ x ∈ unitDisk, deriv φ x ≠ 0)
    (F : closedUnitDisk → ℂ) (hF : Continuous F) (hi : Function.Injective F)
    (hInterior : ∀ z : unitDisk, F ⟨z, show ‖(z : ℂ)‖ ≤ 1 from le_of_lt z.property⟩ = φ z) :
    ∃ Φ : closedUnitDisk ≃ₜ closure Q,
      ExtendsDiskMap Q φ Φ ∧
      (∀ Ψ : closedUnitDisk ≃ₜ closure Q, ExtendsDiskMap Q φ Ψ → Ψ = Φ) ∧
      (∃ β : Circle ≃ₜ frontier Q,
        (∀ ζ : Circle, (β ζ : ℂ) = (Φ (circleInClosedDisk ζ) : ℂ)) ∧
        PositiveBoundaryParametrization Q β) ∧
      (∀ p : Fin 4 → ℂ, PositiveBoundaryFour Q p →
        ∃ u : Fin 4 → Circle, PositiveCircleFour u ∧
          ∀ i, (Φ (circleInClosedDisk (u i)) : ℂ) = p i) := by
  have hRange := continuous_extension_range hb F hF hInterior
  let G : closedUnitDisk → closure Q := fun z ↦ ⟨F z, hRange ▸ mem_range_self z⟩
  have hGc : Continuous G := hF.subtype_mk _
  have hGi : Function.Injective G := fun a b heq ↦ hi (congrArg Subtype.val heq)
  have hGs : Function.Surjective G := by
    intro y
    have hy : (y : ℂ) ∈ Set.range F := hRange.symm ▸ y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hcompact : IsCompact closedUnitDisk := by
    simpa only [closedUnitDisk, Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ℂ) 1
  let : CompactSpace closedUnitDisk := isCompact_iff_compactSpace.mp hcompact
  let E := Equiv.ofBijective G ⟨hGi, hGs⟩
  let Φ := E.toHomeomorphOfContinuousClosed hGc hGc.isClosedMap
  have hΦ : ExtendsDiskMap Q φ Φ := fun z hz ↦ hInterior ⟨z, hz⟩
  obtain ⟨β, hβ⟩ := extension_boundary_homeomorph hQ hb Φ hΦ
  exact ⟨Φ, hΦ, fun Ψ hΨ ↦ extension_unique Ψ Φ hΨ hΦ,
    ⟨β, hβ, extension_positive hQ hh hb hd Φ hΦ β hβ⟩,
    extension_preserves_four hQ hh hb (hd 0 (by simp [unitDisk])) Φ hΦ β hβ⟩
end
end HolomorphicAnosov.Analysis.MarkedRectangle

namespace HolomorphicAnosov.Analysis.MarkedRectangle
noncomputable section
open Filter
open HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts
/-- Reparametrizing by a monotone map cannot increase polygonal variation.
This is the affine transport used to feed normalized short crosscuts into the cap provider. -/
private theorem eVariationOn_comp_monotoneOn_le
    {α E : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    {f : α → E} {g : α → α} {s t : Set α}
    (hg : MonotoneOn g s) (hmap : Set.MapsTo g s t) :
    eVariationOn (f ∘ g) s ≤ eVariationOn f t := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  let v : ℕ → α := g ∘ u
  have hv : Monotone v := fun i j hij => hg (hus i) (hus j) (hu hij)
  have hvs : ∀ i, v i ∈ t := fun i => hmap (hus i)
  exact eVariationOn.sum_le hv hvs

/--
Carathéodory extension for the same holomorphic bijection, including positive
boundary orientation and preservation of four cyclic marks.

Source: Terence Tao, 246C Notes2(12April2018), §2 Theorem 20 and proof, literature/Tao-246C-Notes2-2018.txt:249–269; marked positive vertices line271. Independent topology: Cairns1951 printed860–867, especially lemma5.1 p866. Reflection: existing generic analysis.schwarz_real_boundary_extension_g6_20261007, Shaun Bullett MTH6111 Complex Analysis Section V, Proposition 23.1 printed p.3, literal conjugate reflection on U=B(a,r); McMullen Theorem 1.36 pp.24–25 supplies corroborating context. Positive boundary orientation: Lyubich Conformal Geometry §3.3 pp107–108, exact continuous winding/argument principle bank. All obtained primary PDFs inspected; no polygonal boundary restriction. Orientation convention: acquired Tao246A Notes3 (2 October2016), Theorem 50 and immediate subsequent clockwise/anticlockwise definition, literature/Tao-246A-Notes3-2016.txt:751–776. Cyclic-order convention: Lyubich §1.11 printed pp.53–54 and §19.8.4 circle-homeomorphism paragraph; omitted comparison is explicitly expanded by the exponential lift and exact interval monotonicity theorem below. Current cap source: Conway, Functions of One Complex Variable II (1995), Chapter14 Theorem5.5(d⇒a) printed p.50, Definition2.1/Lemma2.2 p.33, Definition2.3 p.34 and written Janiszewski Lemma5.4 p.49, including coincident endpoints and fixed-interior-point cap selection. Current interior inverse source: McMullen Advanced Complex Analysis Theorem1.31 printed p.15 and univalence paragraph p.58; exact analytic power/root proof and literal open coordinate inverse are recorded in analysis.qc_holomorphic_embedding_inverse. These provider proofs do not close their independent lower source obligations, including Whyburn separation.

Complete natural-language proof:

1. Use the existing holomorphic BijOn homeomorphism theorem to obtain the literal interior homeomorphism. The new derivative-nonvanishing child adapts it to an open coordinate homeomorphism and applies the public literal inverse derivative theorem; hence φ′ never vanishes on the disk.

2. Because Q is bounded, its planar area is finite. At z∈D the complex scalar derivative φ′(z) is the complex Fréchet derivative h↦φ′(z)h; restrict this actual derivative to real scalars. In the real basis(1,i) its matrix is [[Re φ′,−Im φ′],[Im φ′,Re φ′]], whose determinant is |φ′|² by direct2×2 algebra, without division by φ′. Apply the injective real-Jacobian lower-integral theorem on measurable D, with g=1 and φ(D)=Q. It gives ∫_D|φ′|²=area(Q)<∞ using the canonical actual area measure, with no probability normalization.

3. First identify Q with the bounded Jordan complementary component using the independent Cairns theorem. Q is disjoint from Γ=∂Q because Q is open. On either component of ℂ∖Γ, intersection with Q is relatively open and relatively closed: any relative frontier point would be in ∂Q=Γ, impossible. Hence a connected complement component meeting Q lies wholly in Q. Connectedness and nonemptiness of Q select exactly one component; boundedness excludes the exterior. For each ζ∈S¹, the finite nonnegative Dirichlet lower integral from step2 meets the exact crosscut child premise. That child yields strictly decreasing 0<r_n<1, r_n→0, rectifiable closed image-arc completions with endpoints on ∂Q and lengths L_n→0, without a boundary extension. Apply the short-cap child to the literal interior homeomorphism φ and these arcs to obtain diam φ(D∩B(ζ,r_n))→0. Endpoint coincidence is retained by the Conway crosscut definition. For coincident endpoints the cap proof uses a singleton connecting boundary set, and for distinct endpoints a small Jordan boundary subarc; Janiszewski then places all points outside the small endpoint ball in the component containing φ(0), leaving the source cap in the small other component. Thus no distinct-endpoint assumption or omitted parent-source cap exception is added. This is the current short-cap provider’s complete one-level source proof; its Whyburn separation and connected-complement lower prerequisites remain open.

4. Fix ζ and let A_n=D∩B(ζ,r_n), K_n=closure(φ(A_n)). Each cap is nonempty (take (1−δ)ζ with 0<δ<min(r_n,1)), and the decreasing radii give nesting. Choose a closed ball containing bounded Q; closure(Q) and each K_n are closed subsets of this compact ball, hence compact by the named compactness leaves. Each K_n is nonempty and closed. Apply the exact decreasing-compact-intersection leaf to get y_ζ in every K_n. Closure does not increase a finite diameter: approximate two closure points by image points and pass the continuous distance inequality to the limit. Thus diam K_n→0, and if y,y′ lie in every K_n, their distance is at most each shrinking diameter, hence zero. The intersection is exactly {y_ζ}. Given ε>0, some K_n has all its points within ε of y_ζ; every interior source point sufficiently close to ζ lies in A_n. Thus φ(z)→y_ζ for every interior approach. If y_ζ∈Q, the continuous inverse applied to the particular sequence (1−1/(k+2))ζ would have limit φ⁻¹(y_ζ)∈D and also ζ∈S¹, contradicting uniqueness of limits in ℂ. Therefore y_ζ∈∂Q. Define the literal extension Φ by φ on D and y_ζ on S¹. The exact closed-disk extension theorem now proves the continuous extension directly from the shrinking image-cap conclusion, using completeness and dense-subspace neighborhood filters; its continuous extension agrees with the literal interior map and is unique.

5. For boundary continuity at ζ and ε>0 choose n with diam K_n<ε/2. Interior source points within r_n/2 of ζ lie in A_n. If η∈S¹ has |η−ζ|<r_n/2, every sufficiently small η-cap lies in A_n by the triangle inequality. Its closure image, and hence y_η, lie in K_n. Both interior images and these neighboring boundary values are therefore within ε/2 of y_ζ. This proves continuity for arbitrary mixed boundary/interior and tangential approaches; on D continuity is already known. The closed source disk is compact by the closed-ball leaf. The continuous Φ image is compact and closed in the Hausdorff target ℂ, contains Q and is contained in closure(Q); closure minimality proves its image equals closure(Q). Thus Φ is onto. Joint boundary continuity and uniqueness of the extension are supplied by analysis.closed_disk_extension_shrinking_caps_g6, whose local-oscillation proof does not require a uniform radius over all boundary points.

6. The disjointness of Q and∂Q and interior injectivity leave only boundary collisions to exclude. If ζ≠ω have common value p, apply the collapsed-boundary-arc source child. The image of their source chord is a simple Jordan loop whose only intersection with∂Q is p; its bounded inside is contained in Q because the exterior of Q is connected to infinity. One chord-cap maps to that inside, forcing its circle arc into closure inside intersect∂Q={p}. Thus Φ is constant on a nontrivial circle arc, without having assumed boundary injectivity.

7. Suppose step6 yields a nonempty open circle arc on which Φ=p. Choose a point ρ∈S¹ outside a proper subarc of this arc and put M(z)=i(1+z/ρ)/(1−z/ρ), N(v)=ρ(v−i)/(v+i). Direct algebra gives M∘N=id and N∘M=id wherever the denominators are nonzero, and Im M(z)=(1−|z/ρ|²)/|1−z/ρ|². Thus M maps the source disk to the upper halfplane and the circle away from ρ to ℝ. Its inverse N is holomorphic away from −i, by analytic division of affine polynomials. Choose real a in the image of the constant subarc and a sufficiently small r>0 (also r<1) so U=B(a,r) avoids −i and N maps the real diameter into that subarc. Compose the literal φ with N above the real axis and subtract p. Analytic composition gives holomorphy there; Φ∘N−p supplies the continuous upper-closed-halfdisk values and is zero on its real diameter. Since U is open and invariant under conjugation, apply the exact generic Bullett real-boundary reflection theorem. Its literal conjugate formula extends this function holomorphically across the diameter. Convert it to analyticity. If its germ at a were nonzero, the named analytic factorization would have finite order m and expression (v−a)^m u(v), u(a)≠0. Continuity makes u nonzero on a neighborhood, so the germ would have no other nearby zeros; the interval zeros contradict this. The germ is zero. A zero neighborhood includes upper-halfplane points, and N carries such a neighborhood to a nonempty open subset of D. The connected-domain identity theorem then gives φ≡p on D, contradicting injectivity (D has distinct points) or the nonempty open image Q. Only the smooth source circle is flattened; the target boundary is arbitrary and no boundary derivative is used.

8. The now continuous bijection Φ:closed D→closure Q defines an equivalence whose forward function is literally Φ. Compact closed D and Hausdorff closure Q give the homeomorphism by the named exact leaf. Any other continuous extension Ψ agrees on D. For z∈closed D the interior points z_k=(1−1/(k+2))z lie in D and converge to z, including z=0; continuity yields Φ(z)=lim φ(z_k)=Ψ(z). This supplies both density and uniqueness explicitly, without a separate density axiom. Interior and boundary values are disjoint, and surjectivity then shows Φ(S¹)=∂Q; its restriction and inverse restriction are continuous, so it is a boundary homeomorphism.

9. For q∈Q choose its unique preimage x in D. Choose |x|<r<1. The closed-disk winding child counts the unique simple zero x of φ−φ(x) on the r-disk and deforms its image circle radially to the boundary without meeting q, using the injectivity already proved. Its winding is one. A continuous logarithm lift supplied by the winding provider has endpoint increment 2πi, exactly the positive boundary parametrization definition. This handles every q directly.

10. For any positive parametrization β′ used to specify the marks, let h=β⁻¹∘β′, where β is the restriction of the constructed Φ. Extend Φ to a total plane function arbitrarily outside the closed disk; it is continuous and injective on the disk and equals φ near zero. The winding-transport child, using its zero-free divided difference, identifies winding(h,0) with winding(β′,φ(0)), which is one by β′ positivity. The degree-one circle-order child then lifts h after a cut at the first marked angle and gives increasing image angles spanning less than one turn. Their phase points are precisely h of the original four parameters and hence map under Φ to the given marks.

-/
theorem caratheodory_same_map
    (Q : Set ℂ) (hQne : Q.Nonempty) (hQopen : IsOpen Q)
    (hQbounded : Bornology.IsBounded Q) (hQsimply : IsSimplyConnected Q)
    (hQjordan : HasJordanBoundary Q) (φ : ℂ → ℂ)
    (hφholomorphic : DifferentiableOn ℂ φ unitDisk)
    (hφbijective : Set.BijOn φ unitDisk Q) :
    ∃ Φ : closedUnitDisk ≃ₜ closure Q,
      ExtendsDiskMap Q φ Φ ∧
      (∀ Ψ : closedUnitDisk ≃ₜ closure Q, ExtendsDiskMap Q φ Ψ → Ψ = Φ) ∧
      (∃ β : Circle ≃ₜ frontier Q,
        (∀ ζ : Circle, (β ζ : ℂ) = (Φ (circleInClosedDisk ζ) : ℂ)) ∧
        PositiveBoundaryParametrization Q β) ∧
      (∀ p : Fin 4 → ℂ, PositiveBoundaryFour Q p →
        ∃ u : Fin 4 → Circle, PositiveCircleFour u ∧
          ∀ i, (Φ (circleInClosedDisk (u i)) : ℂ) = p i) := by
  have hDisk : unitDisk = Metric.ball (0 : ℂ) 1 := by
    ext z
    simp [unitDisk, Metric.mem_ball, dist_zero_right]
  have hhol : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1) :=
    hDisk ▸ hφholomorphic
  have hbij : Set.BijOn φ (Metric.ball (0 : ℂ) 1) Q := hDisk ▸ hφbijective
  obtain ⟨e, he⟩ :=
    HolomorphicAnosov.Analysis.exists_homeomorph_eq_holomorphic_bijOn
      Metric.isOpen_ball hhol hbij
  obtain ⟨hext, hextHol, henergy⟩ :=
    HolomorphicAnosov.Analysis.diskExtension_eq_holomorphic_finite_energy hQbounded e φ hhol he
  obtain ⟨j, hjemb, hjfrontier⟩ := hQjordan
  obtain ⟨q, hqQ⟩ := hQne
  have hQcomponent_frontier : connectedComponentIn (frontier Q)ᶜ q = Q :=
    HolomorphicAnosov.open_connected_frontier_component hQopen hQsimply.isPathConnected.isConnected.isPreconnected hqQ
  have hQcomponent : Q = connectedComponentIn (Set.range j)ᶜ q := by
    rw [hjfrontier]
    exact hQcomponent_frontier.symm
  have hcaps : ∀ ζ : Circle, ∃ r : ℕ → ℝ,
      (∀ n, 0 < r n) ∧
      Tendsto (fun n ↦ Metric.ediam
        ((fun z : Metric.ball (0 : ℂ) 1 ↦ (e z : ℂ)) ''
          {z : Metric.ball (0 : ℂ) 1 | dist (z : ℂ) (ζ : ℂ) < r n}))
        atTop (𝓝 0) := by
    intro ζ
    obtain ⟨r, Ψ, hranti, hrpos, hrzero, hdetails, hvar⟩ :=
      HolomorphicAnosov.Analysis.MarkedRectangleG3ShortCrosscuts.exists_short_crosscuts
        hQopen e hextHol henergy ζ (by simp)
    let β : ℕ → ℝ → ℂ := fun n t => Ψ n (arcStart (r n) +
        (arcEnd (r n) - arcStart (r n)) * t)
    have hβ_cont : ∀ n, ContinuousOn (β n) (Set.Icc 0 1) := by
      intro n
      rcases hdetails n with ⟨hAE, hwidth, hcc, hci, himo, himc, hsn, hen, hpc, hEq,
        hpi, hvf, hf0, hf1⟩
      apply hpc.comp
      · fun_prop
      · intro t ht
        dsimp [β]
        constructor <;> nlinarith [hAE, ht.1, ht.2]
    have hβ_arc : ∀ n t, t ∈ Set.Ioo (0 : ℝ) 1 →
        ∃ hb : β n t ∈ Q,
          (e.symm ⟨β n t, hb⟩ : ℂ) = markedRectangleG3CircularArc ζ (r n) t := by
      intro n t ht
      rcases hdetails n with ⟨hAE, hwidth, hcc, hci, himo, himc, hsn, hen, hpc, hEq,
        hpi, hvf, hf⟩
      let s := arcStart (r n) + (arcEnd (r n) - arcStart (r n)) * t
      have hs : s ∈ Set.Ioo (arcStart (r n)) (arcEnd (r n)) := by
        dsimp [s]
        constructor <;> nlinarith [hAE, ht.1, ht.2]
      have heq := hEq hs
      have hsball : circleArcMap ζ (r n) s ∈ Metric.ball (0 : ℂ) 1 := by
        have hpair : circleArcMap ζ (r n) s ∈ Metric.ball (0 : ℂ) 1 ∩ Metric.sphere ζ (r n) := by
          rw [← himo]
          exact ⟨s, hs, rfl⟩
        exact hpair.1
      have hb : β n t ∈ Q := by
        dsimp [β]
        rw [heq]
        simp only [Function.comp_apply, diskExtension, dite_eq_left hsball]
        exact (e ⟨circleArcMap ζ (r n) s, hsball⟩).property
      refine ⟨hb, ?_⟩
      have hye : (⟨β n t, hb⟩ : Q) = e ⟨circleArcMap ζ (r n) s, hsball⟩ := by
        apply Subtype.ext
        dsimp [β]
        rw [heq]
        simp only [Function.comp_apply, diskExtension, dite_eq_left hsball]
      have hsub : e.symm ⟨β n t, hb⟩ = ⟨circleArcMap ζ (r n) s, hsball⟩ := by
        calc
          e.symm ⟨β n t, hb⟩ = e.symm (e ⟨circleArcMap ζ (r n) s, hsball⟩) := congrArg e.symm hye
          _ = _ := e.symm_apply_apply _
      rw [hsub]
      change circleArcMap ζ (r n) s = _
      unfold markedRectangleG3CircularArc circleMap
      rw [show Real.arccos (-(r n) / 2) = Real.pi - Real.arccos (r n / 2) by
        rw [← Real.arccos_neg]; congr 1; ring]
      have hsangle : s = Real.pi - Real.arccos (r n / 2) +
          2 * Real.arccos (r n / 2) * t := by
        dsimp [s, arcStart, arcEnd]
        ring
      rw [hsangle]
      unfold circleArcMap circleMap
      push_cast
      ring_nf
    have hβ_frontier : ∀ n, β n 0 ∈ frontier Q ∧ β n 1 ∈ frontier Q := by
      intro n
      rcases hdetails n with ⟨hAE, hwidth, hcc, hci, himo, himc, hsn, hen, hpc, hEq,
        hpi, hvf, hf0, hf1⟩
      dsimp [β]
      simpa using ⟨hf0, hf1⟩
    have hβ_rectifiable : ∀ n, BoundedVariationOn (β n) (Set.Icc 0 1) := by
      intro n
      rcases hdetails n with ⟨hAE, hwidth, hcc, hci, himo, himc, hsn, hen, hpc, hEq,
        hpi, hvf, hf0, hf1⟩
      apply ne_top_of_le_ne_top hvf.ne
      apply eVariationOn_comp_monotoneOn_le
      · intro x hx y hy hxy
        nlinarith [hAE]
      · intro x hx
        constructor <;> nlinarith [hAE, hx.1, hx.2]
    have hβ_length_zero : Tendsto (fun n ↦ eVariationOn (β n) (Set.Icc 0 1))
        atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvar
      · intro n; exact bot_le
      · intro n
        rcases hdetails n with ⟨hAE, hwidth, hcc, hci, himo, himc, hsn, hen, hpc, hEq,
          hpi, hvf, hf0, hf1⟩
        exact eVariationOn_comp_monotoneOn_le
          (fun x hx y hy hxy => by nlinarith [hAE])
          (fun x hx => by constructor <;> nlinarith [hAE, hx.1, hx.2])
    have hcap := HolomorphicAnosov.Analysis.markedRectangleG3ShortCapControl
      j hjemb Q q hQcomponent hQbounded e ζ (by simp)
      r hrpos hrzero β hβ_cont hβ_arc hβ_frontier
      hβ_rectifiable hβ_length_zero
    exact ⟨r, (fun n => (hrpos n).1), hcap⟩
  obtain ⟨F, hF, hFuniq⟩ :=
    HolomorphicAnosov.Analysis.exists_unique_closed_disk_extension_of_shrinking_caps
      (fun z : Metric.ball (0 : ℂ) 1 ↦ (e z : ℂ))
      (continuous_subtype_val.comp e.continuous)
      (fun ζ hζ ↦ hcaps ⟨ζ, hζ⟩)
  have hFclosure : ∀ z : Metric.closedBall (0 : ℂ) 1, F z ∈ closure Q := by
    let S : Set (Metric.closedBall (0 : ℂ) 1) := {z | (z : ℂ) ∈ Metric.ball (0 : ℂ) 1}
    have hS : Dense S := by
      rw [Subtype.dense_iff]
      have he : (Subtype.val : Metric.closedBall (0 : ℂ) 1 → ℂ) '' S =
          Metric.ball (0 : ℂ) 1 := by
        ext z
        constructor
        · rintro ⟨a, ha, rfl⟩
          exact ha
        · intro hz
          exact ⟨⟨z, Metric.ball_subset_closedBall hz⟩, hz, rfl⟩
      rw [he, closure_ball (0 : ℂ) one_ne_zero]
    have hpre : IsClosed (F ⁻¹' closure Q) := isClosed_closure.preimage hF.1
    have hsub : S ⊆ F ⁻¹' closure Q := by
      intro z hz
      change F z ∈ closure Q
      have hagree := hF.2 ⟨z, hz⟩
      rw [show F z = (e ⟨z, hz⟩ : ℂ) by simpa using hagree]
      exact subset_closure (e ⟨z, hz⟩).property
    have hcl : closure S ⊆ F ⁻¹' closure Q := closure_minimal hsub hpre
    intro z
    exact hcl (by simp [hS.closure_eq])
  let F' : closedUnitDisk → ℂ := fun z ↦ F ⟨z, by
    simpa only [closedUnitDisk, Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] using z.property⟩
  have hF' : Continuous F' := hF.1.comp (by fun_prop)
  have hInterior : ∀ z : unitDisk,
      F' ⟨z, show ‖(z : ℂ)‖ ≤ 1 from le_of_lt z.property⟩ = φ z := by
    intro z
    exact (hF.2 ⟨z, hDisk ▸ z.property⟩).trans (he ⟨z, hDisk ▸ z.property⟩)
  let e' : unitDisk ≃ₜ Q := (Homeomorph.setCongr hDisk).trans e
  have he' : ∀ z : unitDisk, (e' z : ℂ) = φ z := fun z ↦ he ⟨z, hDisk ▸ z.property⟩
  have hRegion := continuous_extension_mem_region_iff hQopen e' he' F' hF' hInterior
  let G : Complex.UnitClosedDisc → closure Q := fun z ↦ ⟨F z, hFclosure z⟩
  have hGc : Continuous G := hF.1.subtype_mk _
  have hGagree : ∀ z (hz : z ∈ Metric.ball (0 : ℂ) 1),
      (G ⟨z, Metric.ball_subset_closedBall hz⟩ : ℂ) = φ z :=
    fun z hz ↦ (hF.2 ⟨z, hz⟩).trans (he ⟨z, hz⟩)
  have hGboundary : ∀ ζ : Circle,
      HolomorphicAnosov.MarkedRectangleG3CollapsedBoundaryArc.boundaryValue G ζ ∈ frontier Q := by
    intro ζ
    rw [frontier, hQopen.interior_eq]
    refine ⟨(G ⟨ζ, Metric.sphere_subset_closedBall ζ.property⟩).property, ?_⟩
    intro hq
    have hz := (hRegion (circleInClosedDisk ζ)).mp hq
    simp [unitDisk, circleInClosedDisk] at hz
  have hJordan : HolomorphicAnosov.MarkedRectangleG3CollapsedBoundaryArc.IsBoundedJordanDomain Q := by
    refine ⟨j, hjemb, q, ?_, hQcomponent, hQbounded⟩
    rw [hjfrontier]
    exact fun hf ↦ (by simpa [hQopen.interior_eq] using hf.2 : q ∉ Q) hqQ
  have hGi := HolomorphicAnosov.injective_closed_disk_extension hQopen hJordan φ
    hhol hbij e he G hGc hGagree hGboundary
  have hFi : Function.Injective F' := by
    intro a b heq
    have hh : G ⟨a, by simpa only [closedUnitDisk, Set.mem_ofPred_eq, Submonoid.mem_unitClosedBall, Metric.mem_closedBall, dist_zero_right] using a.property⟩ =
        G ⟨b, by simpa only [closedUnitDisk, Set.mem_ofPred_eq, Submonoid.mem_unitClosedBall, Metric.mem_closedBall, dist_zero_right] using b.property⟩ := Subtype.ext heq
    exact Subtype.ext (congrArg (fun z : Complex.UnitClosedDisc ↦ (z : ℂ)) (hGi hh))
  apply complete_injective_extension hQopen hφholomorphic hφbijective
    (fun x hx ↦ HolomorphicAnosov.Analysis.deriv_ne_zero_bijOn Metric.isOpen_ball hQopen
      hhol hbij x (hDisk ▸ hx)) F' hF' hFi hInterior

end
end HolomorphicAnosov.Analysis.MarkedRectangle
