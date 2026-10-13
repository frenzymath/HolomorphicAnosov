import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Joint derivatives of locally biholomorphic slices

Source: Demailly, *Complex Analytic and Differential Geometry* (2012), I §3.A (3.3),
p. 21 and §3.B, pp. 22–23, continuity of derivations; Ghys, *Holomorphic Anosov
systems* (1995), Lemma 3.3, p. 592. This applies that analytic result to the local
intrinsic biholomorphic overlap certificates used in a finite flowbox cover.
-/

open Set TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov

/-- A jointly continuous family whose scalar slices are locally biholomorphic has
jointly continuous first and second within derivatives on its original open domain.

Source: Demailly I §3.A (3.3), p. 21 and §3.B, pp. 22–23; Ghys Lemma 3.3, p. 592.
At each point the slice agrees on an open neighborhood with the inclusion of a
holomorphic diffeomorphism between open subsets of the complex line. Smoothness
of the inclusion and the open-subtype criterion give ordinary complex
differentiability at that point. The source holomorphic-slice derivative theorem
then gives joint continuity of the first derivative. Apply it again to that
continuous derivative family, whose slices remain holomorphic, for the second
derivative. On the open slices, within derivatives equal ordinary derivatives;
this equality holds near each point and can be differentiated again. Empty domains
and empty slices are included. No differentiation of the parameter is used. -/
theorem localBiholomorphicSlice_derivatives
    {T : Type*} [TopologicalSpace T] (Ω : Set (ℂ × T)) (hΩ : IsOpen Ω)
    (h : ℂ × T → ℂ) (hh : ContinuousOn h Ω)
    (hloc : ∀ p ∈ Ω, ∃ (A B : Opens ℂ), p.1 ∈ A ∧
      (∀ z ∈ A, (z, p.2) ∈ Ω) ∧
      ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A B ∞,
        ∀ z : A, (e z : ℂ) = h (z.val, p.2)) :
    ContinuousOn (fun p : ℂ × T ↦
      derivWithin (fun z ↦ h (z, p.2)) {z | (z, p.2) ∈ Ω} p.1) Ω ∧
    ContinuousOn (fun p : ℂ × T ↦
      derivWithin (derivWithin (fun z ↦ h (z, p.2)) {z | (z, p.2) ∈ Ω})
        {z | (z, p.2) ∈ Ω} p.1) Ω := by
  have hd : ∀ t, DifferentiableOn ℂ (fun z ↦ h (z, t)) {z | (z, t) ∈ Ω} := by
    intro t z hz
    obtain ⟨A, B, hzA, _, e, he⟩ := hloc (z, t) hz
    have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ (fun w : A ↦ h (w.val, t)) := by
      have hc := (contMDiff_subtype_val (I := 𝓘(ℂ)) (U := B)).comp e.contMDiff
      convert hc using 1
      funext w
      exact (he w).symm
    have hc' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (fun w ↦ h (w, t)) z :=
      (contMDiffAt_subtype_iff (I := 𝓘(ℂ)) (I' := 𝓘(ℂ))
        (U := A) (f := fun w ↦ h (w, t)) (x := ⟨z, hzA⟩)).mp (hc ⟨z, hzA⟩)
    exact (hc'.contDiffAt.differentiableAt (by simp)).differentiableWithinAt
  have hs (t : T) : IsOpen {z : ℂ | (z, t) ∈ Ω} :=
    hΩ.preimage (continuous_id.prodMk continuous_const)
  have hfirst := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ h hh hd
  have hsecond := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hΩ
    (fun p ↦ deriv (fun z ↦ h (z, p.2)) p.1) hfirst
    (fun t ↦ (hd t).deriv (hs t))
  constructor
  · exact hfirst.congr (fun p hp ↦ (derivWithin_of_isOpen (hs p.2) hp))
  · exact hsecond.congr (fun p hp ↦
      (SliceDerivativePreparation.second_derivWithin_of_isOpen
        (fun z ↦ h (z, p.2)) {z | (z, p.2) ∈ Ω} (hs p.2) p.1 hp))

end HolomorphicAnosov
