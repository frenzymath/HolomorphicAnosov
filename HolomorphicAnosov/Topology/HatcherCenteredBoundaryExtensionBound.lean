import HolomorphicAnosov.Topology.NullhomotopicSphereDiskExtension
import Mathlib.Topology.Homotopy.Contractible

namespace HolomorphicAnosov
open Metric Set

/-- A sphere map into a centered inner ball extends to the disk with image in the outer ball,
provided the inner-ball inclusion is nullhomotopic.

Source: Hatcher, Algebraic Topology, Theorem A.7, printed p.526. Regard the boundary map as
ball-valued, compose it with the given nullhomotopic inclusion, and fill its nullhomotopy using
the sphere-disk extension theorem with the outer ball as codomain. Identify the norm-level sphere
and disk with the metric sphere and closed ball. Composing the resulting outer-ball-valued disk
map with subtype inclusion preserves the boundary equation and gives the strict radius bound.
This argument does not need a separation axiom or a nonempty interior for the carrier. -/
theorem hatcher_centered_boundary_extension_bound
    {X : Type*} [PseudoMetricSpace X]
    (C : Set X) (c : C) (r R : ℝ) (_hr : 0 < r)
    (hball : Metric.ball c r ⊆ Metric.ball c R)
    (hnull : (ContinuousMap.inclusion hball).Nullhomotopic)
    {d : ℕ} (hd : 1 ≤ d)
    (b : C(sphere (0 : Fin d → ℝ) 1, C))
    (hb : ∀ s, b s ∈ Metric.ball c r) :
    ∃ F : C(closedBall (0 : Fin d → ℝ) 1, C),
      (∀ x, dist (F x) c < R) ∧
      ∀ s : sphere (0 : Fin d → ℝ) 1,
        F ⟨s.val, sphere_subset_closedBall s.property⟩ = b s := by
  let bsmall : C(sphere (0 : Fin d → ℝ) 1, Metric.ball c r) :=
    { toFun := fun s => ⟨b s, hb s⟩
      continuous_toFun := b.continuous.subtype_mk _ }
  let blarge : C(sphere (0 : Fin d → ℝ) 1, Metric.ball c R) :=
    { toFun := fun s => ⟨b s, hball (hb s)⟩
      continuous_toFun := b.continuous.subtype_mk _ }
  have hcomp :
      (ContinuousMap.inclusion hball).comp bsmall = blarge := by
    ext s
    rfl
  have hblarge : blarge.Nullhomotopic := by
    rw [← hcomp]
    exact hnull.comp_left bsmall
  have hsphere : sphere (0 : Fin d → ℝ) 1 = {v : Fin d → ℝ | ‖v‖ = 1} := by
    ext v
    simp
  let es : sphere (0 : Fin d → ℝ) 1 ≃ₜ
      {v : Fin d → ℝ // ‖v‖ = 1} := Homeomorph.setCongr hsphere
  let bex : C({v : Fin d → ℝ // ‖v‖ = 1}, Metric.ball c R) :=
    { toFun := fun s => blarge (es.symm s)
      continuous_toFun := blarge.continuous.comp es.symm.continuous }
  let esmap : C({v : Fin d → ℝ // ‖v‖ = 1}, sphere (0 : Fin d → ℝ) 1) :=
    { toFun := es.symm
      continuous_toFun := es.symm.continuous }
  have hblarge' : bex.Nullhomotopic := by
    exact hblarge.comp_left esmap
  obtain ⟨ystar, hH⟩ := hblarge'
  obtain ⟨H⟩ := hH
  obtain ⟨B, hB, hBboundary⟩ :=
    nullhomotopic_sphere_disk_extension d hd bex bex.continuous
      ⟨ystar, H.toContinuousMap, H.toContinuousMap.continuous,
        H.map_zero_left, H.map_one_left⟩
  have hdisk : closedBall (0 : Fin d → ℝ) 1 = {v : Fin d → ℝ | ‖v‖ ≤ 1} := by
    ext v
    simp [Metric.mem_closedBall]
  let ed : closedBall (0 : Fin d → ℝ) 1 ≃ₜ
      {v : Fin d → ℝ // ‖v‖ ≤ 1} := Homeomorph.setCongr hdisk
  let Bnative : C(closedBall (0 : Fin d → ℝ) 1, Metric.ball c R) :=
    { toFun := fun u => B (ed u)
      continuous_toFun := hB.comp ed.continuous }
  let inclC : C(Metric.ball c R, C) :=
    { toFun := fun x => x.1
      continuous_toFun := continuous_subtype_val }
  let F : C(closedBall (0 : Fin d → ℝ) 1, C) := inclC.comp Bnative
  refine ⟨F, ?_, ?_⟩
  · intro x
    exact (Bnative x).property
  · intro s
    have hs := hBboundary (es s)
    dsimp [F, inclC, Bnative]
    change B (ed ⟨s.val, sphere_subset_closedBall s.property⟩) = b s
    have hed : ed ⟨s.val, sphere_subset_closedBall s.property⟩ =
        (⟨(es s).val, le_of_eq (es s).property⟩ : {v : Fin d → ℝ // ‖v‖ ≤ 1}) := by
      apply Subtype.ext
      rfl
    rw [hed, hs]
    rfl


end HolomorphicAnosov
