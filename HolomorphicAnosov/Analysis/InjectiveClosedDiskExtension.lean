import HolomorphicAnosov.Analysis.HolomorphicDiskExtensionNoConstantArc
import HolomorphicAnosov.Analysis.MarkedRectangleG3CollapsedBoundaryArc

open Set Metric
open HolomorphicAnosov.MarkedRectangleG3CollapsedBoundaryArc

namespace HolomorphicAnosov

/-- A continuous extension of an injective holomorphic disk parametrization into
its domain closure is injective if its circle values lie on the frontier.

Source: Tao, 246C Notes 2, Theorem 20 final injectivity paragraph,
`literature/Tao-246C-Notes2-2018.txt:269`. The imported collapsed-boundary-arc
provider carries the independent Jordan separation step; the imported
no-constant-open-circle-arc theorem carries Schwarz reflection and the explicit
local Cayley transport.

Proof: An extension value belongs to the open target exactly when its source
point belongs to the open disk. The forward direction uses the stated frontier
condition, and the reverse uses interior agreement and the disk bijection.
Thus equal values cannot mix interior and boundary points. Interior collisions
contradict the original injectivity. Two distinct circle points with the same
value give a nonempty open constant circle arc by the collapsed-arc provider.
The no-constant-arc theorem contradicts holomorphy and injectivity on the disk.
No short-cap estimate or assumed boundary injectivity enters this step. -/
theorem injective_closed_disk_extension {Q : Set ℂ} (hQopen : IsOpen Q) (hQ : IsBoundedJordanDomain Q)
    (φ : ℂ → ℂ) (hhol : DifferentiableOn ℂ φ (ball (0 : ℂ) 1))
    (hbij : BijOn φ (ball (0 : ℂ) 1) Q)
    (e : Complex.UnitDisc ≃ₜ Q) (he : ∀ z : Complex.UnitDisc, (e z : ℂ) = φ z)
    (F : Complex.UnitClosedDisc → closure Q) (hF : Continuous F)
    (hagree : ∀ z (hz : z ∈ ball (0 : ℂ) 1),
      (F ⟨z, ball_subset_closedBall hz⟩ : ℂ) = φ z)
    (hboundary : ∀ ζ : Circle, boundaryValue F ζ ∈ frontier Q) :
    Function.Injective F := by
  have hinterior (z : Complex.UnitDisc) : (F (diskInclusion z) : ℂ) = (e z : ℂ) :=
    (hagree z z.property).trans (he z).symm
  have hmem (z : Complex.UnitClosedDisc) : (F z : ℂ) ∈ Q ↔ ‖(z : ℂ)‖ < 1 := by
    constructor
    · intro hzQ
      by_contra! hz
      have hnorm : ‖(z : ℂ)‖ = 1 := le_antisymm
        z.norm_le_one hz
      let ζ : Circle := ⟨z, by change dist (z : ℂ) 0 = 1; simpa only [dist_zero_right] using hnorm⟩
      have hfront : (F z : ℂ) ∈ frontier Q := hboundary ζ
      have hnot : (F z : ℂ) ∉ Q := by
        simpa only [hQopen.interior_eq] using hfront.2
      exact hnot hzQ
    · intro hz
      have hzball : (z : ℂ) ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hz
      exact (hagree z hzball).symm ▸ hbij.mapsTo hzball
  intro x y hxy
  by_cases hx : ‖(x : ℂ)‖ < 1
  · have hy : ‖(y : ℂ)‖ < 1 := (hmem y).mp (hxy ▸ (hmem x).mpr hx)
    apply Subtype.ext
    have hxball : (x : ℂ) ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hx
    have hyball : (y : ℂ) ∈ ball (0 : ℂ) 1 := by simpa only [mem_ball, dist_zero_right] using hy
    apply hbij.injOn hxball hyball
    exact (hagree x hxball).symm.trans ((congrArg Subtype.val hxy).trans (hagree y hyball))
  · have hy : ¬ ‖(y : ℂ)‖ < 1 := by
      intro hy
      exact hx ((hmem x).mp (hxy.symm ▸ (hmem y).mpr hy))
    have hxn : ‖(x : ℂ)‖ = 1 := le_antisymm
      x.norm_le_one (le_of_not_gt hx)
    have hyn : ‖(y : ℂ)‖ = 1 := le_antisymm
      y.norm_le_one (le_of_not_gt hy)
    let ζ : Circle := ⟨x, by change dist (x : ℂ) 0 = 1; simpa only [dist_zero_right] using hxn⟩
    let ω : Circle := ⟨y, by change dist (y : ℂ) 0 = 1; simpa only [dist_zero_right] using hyn⟩
    by_contra hne
    have hdistinct : ζ ≠ ω := by
      intro heq
      exact hne (Subtype.ext (congrArg (fun z : Circle ↦ (z : ℂ)) heq))
    have hζ : boundaryValue F ζ = (F x : ℂ) := rfl
    have hω : boundaryValue F ω = (F x : ℂ) := congrArg Subtype.val hxy.symm
    have hcollapse := collapsed_boundary_arc hQ F hF e hinterior hboundary
      ζ ω hdistinct (F x : ℂ) hζ hω
    rcases hcollapse with h | h
    · exact HolomorphicAnosov.no_constant_open_circle_arc φ hhol hbij.injOn
        (fun z ↦ (F z : ℂ)) (continuous_subtype_val.comp hF) hagree
        (openDirectedArc ζ ω) h.2.2.1 h.2.1 (F x : ℂ) h.2.2.2
    · exact HolomorphicAnosov.no_constant_open_circle_arc φ hhol hbij.injOn
        (fun z ↦ (F z : ℂ)) (continuous_subtype_val.comp hF) hagree
        (openDirectedArc ω ζ) h.2.2.1 h.2.1 (F x : ℂ) h.2.2.2

end HolomorphicAnosov
