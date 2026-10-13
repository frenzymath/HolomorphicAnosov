import HolomorphicAnosov.Analysis.FrameRatioOperatorNorm
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Topology _root_.Topology

namespace HolomorphicAnosov
noncomputable section

/-- Operator norms vary continuously when frame and image norms are jointly continuous.
Restrict to the compact unit sphere of the finite dimensional frame model. The frame
norm is positive there, so its ratio with the image norm is jointly continuous. Compact
supremum continuity and `frame_ratio_norm` give the conclusion, including zero rank.
This is a coordinate proof of the continuous Finsler norm argument used in HPS p.8. -/
lemma continuous_norm_of_frame {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E F : X → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    (j : ∀ x, V ≃L[ℝ] E x) (L : ∀ x, E x →L[ℝ] F x)
    (hden : Continuous (fun z : X × V ↦ ‖j z.1 z.2‖))
    (hnum : Continuous (fun z : X × V ↦ ‖L z.1 (j z.1 z.2)‖)) :
    Continuous (fun x ↦ ‖L x‖) := by
  let S := Metric.sphere (0 : V) 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hcoords : Continuous (fun z : X × S ↦ (z.1, z.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hnz : ∀ z : X × S, ‖j z.1 z.2.val‖ ≠ 0 := by
    intro z
    apply norm_ne_zero_iff.mpr
    intro hz
    have hv : z.2.val = 0 := (j z.1).injective (hz.trans (map_zero _).symm)
    have hvnorm : ‖z.2.val‖ = 1 := by simp [S]
    simp [hv] at hvnorm
  have hr : Continuous (fun z : X × S ↦ ‖L z.1 (j z.1 z.2.val)‖ / ‖j z.1 z.2.val‖) :=
    (hnum.comp hcoords).div (hden.comp hcoords) hnz
  have hc := (isCompact_univ : IsCompact (univ : Set S)).continuous_sSup
    (f := fun (x : X) (u : S) ↦ ‖L x (j x u.val)‖ / ‖j x u.val‖) hr
  exact hc.congr (fun x ↦ (frame_ratio_norm (j x) (L x)).symm)

end
end HolomorphicAnosov
