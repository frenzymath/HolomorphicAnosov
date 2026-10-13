import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Regularity of scalar expressions for leaf transports. Source: Ghys p.591–592. -/

namespace HolomorphicAnosov.Ghys
open Set Filter _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
universe u v w z

/-- The scalar expression of a leaf transport is holomorphic on every source slice. Source: Ghys p.591–592. -/
theorem jetFlowboxTransport_slice
    {M : Type u} [TopologicalSpace M] {Q : Type v} {L : Q → Type w}
    [∀ q, TopologicalSpace (L q)] [∀ q, ChartedSpace ℂ (L q)]
    [∀ q, IsManifold 𝓘(ℂ) ∞ (L q)]
    {T : Type z} [TopologicalSpace T]
    (inclusion : ∀ q, L q → M) (σ : Q → Q)
    (F : ∀ q, Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (L q) (L (σ q)) ∞)
    (f : M → M) (hF : ∀ q x, inclusion (σ q) (F q x) = f (inclusion q x))
    (c d : OpenPartialHomeomorph M (ℂ × T)) (V : Set T)
    (label : V → Q) (branch : ∀ t, Opens (L (label t)))
    (param : ∀ t : V, Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
      (⟨{z | (z, t.val) ∈ c.target}, c.open_target.preimage
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℂ ↦ t.val)))⟩ : Opens ℂ)
      (branch t) ∞)
    (htarget : ∀ p ∈ c.target, p.2 ∈ V)
    (hparam : ∀ t z, c.symm (z.val, t.val) = inclusion (label t) (param t z).val)
    (hscalar : ∀ q x, inclusion q x ∈ d.source →
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (fun y ↦ (d (inclusion q y)).1) x)
    (p : ℂ × T) (hp : p ∈ c.target) (hfp : f (c.symm p) ∈ d.source) :
    ContDiffAt ℂ ∞ (fun z ↦ (d (f (c.symm (z, p.2)))).1) p.1 := by
  let t : V := ⟨p.2, htarget p hp⟩
  let W : Opens ℂ := ⟨{z | (z, t.val) ∈ c.target},
    c.open_target.preimage (continuous_id.prodMk continuous_const)⟩
  let w : W := ⟨p.1, hp⟩
  have hmem : inclusion (σ (label t)) (F (label t) (param t w).val) ∈ d.source := by
    rw [hF, ← hparam]
    exact hfp
  have hcomp := (hscalar _ _ hmem).comp w
    ((F (label t)).contMDiffAt.comp w
      ((contMDiff_subtype_val.comp (param t).contMDiff).contMDiffAt))
  have heq : (fun z : W ↦ (d (f (c.symm (z.val, p.2)))).1) =
      (fun z : W ↦ (d (inclusion (σ (label t)) (F (label t) (param t z).val))).1) := by
    funext z
    rw [hF, ← hparam]
  have hsub : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
      (fun z : W ↦ (d (f (c.symm (z.val, p.2)))).1) w := by
    rw [heq]
    exact hcomp
  exact ((contMDiffAt_subtype_iff (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (U := W)
    (f := fun z ↦ (d (f (c.symm (z, p.2)))).1)).mp hsub).contDiffAt

/-- Joint continuity of both dynamic scalar derivatives on the genuine open overlap. -/
theorem jetFlowboxTransport_derivatives
    {M : Type u} [TopologicalSpace M] {T : Type z} [TopologicalSpace T]
    (c d : OpenPartialHomeomorph M (ℂ × T)) (f : M → M) (hf : Continuous f)
    (hs : ∀ p ∈ c.target ∩ (f ∘ c.symm) ⁻¹' d.source,
      ContDiffAt ℂ ∞ (fun z ↦ (d (f (c.symm (z, p.2)))).1) p.1) :
    let Ω := c.target ∩ (f ∘ c.symm) ⁻¹' d.source
    let H := fun p : ℂ × T ↦ (d (f (c.symm p))).1
    IsOpen Ω ∧ ContinuousOn (fun p ↦ d (f (c.symm p))) Ω ∧
      ContinuousOn (fun p ↦ deriv (fun z ↦ H (z, p.2)) p.1) Ω ∧
      ContinuousOn (fun p ↦ iteratedDeriv 2 (fun z ↦ H (z, p.2)) p.1) Ω := by
  dsimp only
  let Ω := c.target ∩ (f ∘ c.symm) ⁻¹' d.source
  let H := fun p : ℂ × T ↦ (d (f (c.symm p))).1
  have hopen : IsOpen Ω :=
    (hf.comp_continuousOn c.symm.continuousOn).isOpen_inter_preimage c.open_target d.open_source
  have hcont : ContinuousOn (fun p ↦ d (f (c.symm p))) Ω :=
    d.continuousOn.comp ((hf.comp_continuousOn c.symm.continuousOn).mono inter_subset_left)
      (fun _ hp ↦ hp.2)
  have hd : ∀ t, DifferentiableOn ℂ (fun z ↦ H (z, t)) {z | (z, t) ∈ Ω} := by
    intro t z hz
    exact ((hs (z, t) hz).differentiableAt (by simp)).differentiableWithinAt
  have h1 := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hopen H hcont.fst hd
  have h2 := SliceDerivativePreparation.joint_deriv_continuousOn_open Ω hopen
    (fun p ↦ deriv (fun z ↦ H (z, p.2)) p.1) h1
    (fun t ↦ (hd t).deriv (hopen.preimage (continuous_id.prodMk continuous_const)))
  refine ⟨hopen, hcont, h1, ?_⟩
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h2

end HolomorphicAnosov.Ghys
