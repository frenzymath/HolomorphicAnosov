import HolomorphicAnosov.Analysis.ComplexPlaneBiholomorphismAffine
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic.Module

/-!
# Continuity propagated through local affine coordinates

This is an agent-written expansion of the family-continuity step in Zhang,
Lemma 2.7, p.9. Two continuous anchor values determine an affine function in
any local scalar coordinate. Connectedness propagates continuity from a seed
neighborhood to the whole coordinate domain.
-/

open Set Filter
open scoped Topology

namespace HolomorphicAnosov

/-- Suppose a parameter family is locally affine in jointly continuous scalar
coordinates on a connected space. Each scalar coordinate is nonconstant on
 every nonempty open subset of its domain at the reference parameter. If the
family is jointly continuous at all points of one nonempty open seed, it is
jointly continuous at every point over that reference parameter.

Proof: call a point good when some neighborhood consists of continuity points.
This is an open set. In a scalar-coordinate neighborhood meeting the good set,
choose two good anchors with distinct scalar values. Their two evaluations
recover the affine slope by division by the scalar difference, and then recover
the intercept. Both vary continuously near the reference parameter. Substitution
proves continuity on the whole coordinate neighborhood. Thus every point of the
closure of the good set is good. The good set is nonempty, open and closed, so
connectedness makes it the whole space. No continuity of the initially supplied
affine coefficients is assumed. -/
theorem continuousAt_of_locally_affine_family
    {P D E : Type*} [TopologicalSpace P] [TopologicalSpace D] [PreconnectedSpace D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : P × D → E) (p₀ : P)
    (hlocal : ∀ q : D, ∃ Q : Set D, IsOpen Q ∧ q ∈ Q ∧
      ∃ g : P × D → ℂ,
        (∀ z ∈ Q, ContinuousAt g (p₀, z)) ∧
        (∀ V : Set D, IsOpen V → (V ∩ Q).Nonempty →
          ∃ z ∈ V ∩ Q, ∃ w ∈ V ∩ Q, g (p₀, z) ≠ g (p₀, w)) ∧
        (∀ᶠ p in 𝓝 p₀, ∃ a b : E, ∀ z ∈ Q, F (p, z) = g (p, z) • a + b))
    (hseed : ∃ W : Set D, IsOpen W ∧ W.Nonempty ∧
      ∀ z ∈ W, ContinuousAt F (p₀, z)) :
    ∀ z : D, ContinuousAt F (p₀, z) := by
  classical
  let G : Set D := {z | ∃ W : Set D, IsOpen W ∧ z ∈ W ∧
    ∀ w ∈ W, ContinuousAt F (p₀, w)}
  have hGo : IsOpen G := isOpen_iff_mem_nhds.mpr fun z hz ↦ by
    obtain ⟨W, hWo, hzW, hW⟩ := hz
    exact mem_of_superset (hWo.mem_nhds hzW) fun w hw ↦ ⟨W, hWo, hw, hW⟩
  have hGc : IsClosed G := isClosed_of_closure_subset fun q hq ↦ by
    obtain ⟨Q, hQo, hqQ, g, hg, hgnonconst, haff⟩ := hlocal q
    have hmeet : (G ∩ Q).Nonempty := by
      obtain ⟨z, hzQ, hzG⟩ := mem_closure_iff.mp hq Q hQo hqQ
      exact ⟨z, hzG, hzQ⟩
    obtain ⟨z, hz, w, hw, hzw⟩ := hgnonconst G hGo hmeet
    obtain ⟨Wz, hWzo, hzWz, hWz⟩ := hz.1
    obtain ⟨Ww, hWwo, hwWw, hWw⟩ := hw.1
    have hcFz : ContinuousAt (fun p ↦ F (p, z)) p₀ :=
      (hWz z hzWz).comp (f := fun p : P ↦ (p, z)) (continuous_id.prodMk continuous_const).continuousAt
    have hcFw : ContinuousAt (fun p ↦ F (p, w)) p₀ :=
      (hWw w hwWw).comp (f := fun p : P ↦ (p, w)) (continuous_id.prodMk continuous_const).continuousAt
    have hcgz : ContinuousAt (fun p ↦ g (p, z)) p₀ :=
      (hg z hz.2).comp (f := fun p : P ↦ (p, z)) (continuous_id.prodMk continuous_const).continuousAt
    have hcgw : ContinuousAt (fun p ↦ g (p, w)) p₀ :=
      (hg w hw.2).comp (f := fun p : P ↦ (p, w)) (continuous_id.prodMk continuous_const).continuousAt
    have hne : g (p₀, w) - g (p₀, z) ≠ 0 := sub_ne_zero.mpr hzw.symm
    let A : P → E := fun p ↦ (g (p, w) - g (p, z))⁻¹ • (F (p, w) - F (p, z))
    let B : P → E := fun p ↦ F (p, z) - g (p, z) • A p
    have hcA : ContinuousAt A p₀ := ((hcgw.sub hcgz).inv₀ hne).smul (hcFw.sub hcFz)
    have hcB : ContinuousAt B p₀ := hcFz.sub (hcgz.smul hcA)
    have heq : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ Q, F (p, y) = g (p, y) • A p + B p := by
      filter_upwards [haff, (hcgw.sub hcgz).eventually_ne hne] with p hp hpne
      obtain ⟨a, b, hab⟩ := hp
      change g (p, w) - g (p, z) ≠ 0 at hpne
      have hA : A p = a := by
        dsimp only [A]
        rw [hab w hw.2, hab z hz.2, add_sub_add_right_eq_sub, ← sub_smul,
          smul_smul, inv_mul_cancel₀ hpne, one_smul]
      intro y hy
      dsimp only [B]
      rw [hA, hab y hy, hab z hz.2]
      module
    refine ⟨Q, hQo, hqQ, fun y hy ↦ ?_⟩
    have hc : ContinuousAt (fun r : P × D ↦ g r • A r.1 + B r.1) (p₀, y) :=
      ((hg y hy).smul (hcA.comp continuous_fst.continuousAt)).add
        (hcB.comp continuous_fst.continuousAt)
    apply hc.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually heq,
      continuous_snd.continuousAt.eventually (hQo.mem_nhds hy)] with r hr hrQ
    exact hr r.2 hrQ
  have hGne : G.Nonempty := by
    obtain ⟨W, hWo, ⟨z, hz⟩, hW⟩ := hseed
    exact ⟨z, W, hWo, hz, hW⟩
  have hGall : G = univ := (show IsClopen G from ⟨hGc, hGo⟩).eq_univ hGne
  intro z
  have hz : z ∈ G := hGall ▸ mem_univ z
  obtain ⟨W, hWo, hzW, hW⟩ := hz
  exact hW z hzW

open scoped Manifold ContDiff

/-- Express one complete line chart affinely in another after identifying its
receiving line with the complex plane. This is the scalar automorphism theorem
transported through the two given linear identifications. -/
theorem biholomorph_affine_in_scalar_coordinate
    {L E E' : Type*} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [IsManifold (complexModel 1) ∞ L]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (e : Diffeomorph (complexModel 1) 𝓘(ℂ, E) L E ∞)
    (e' : Diffeomorph (complexModel 1) 𝓘(ℂ, E') L E' ∞)
    (c : E ≃L[ℂ] ℂ) (c' : E' ≃L[ℂ] ℂ) :
    ∃ a b : E, ∀ p : L, e p = c' (e' p) • a + b := by
  let k : Diffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ℂ ℂ ∞ :=
    ((c'.symm.toDiffeomorph.trans e'.symm).trans e).trans c.toDiffeomorph
  have hk : Differentiable ℂ k :=
    (contMDiff_iff_contDiff.mp k.contMDiff).differentiable (by simp)
  have hki : Differentiable ℂ k.symm :=
    (contMDiff_iff_contDiff.mp k.symm.contMDiff).differentiable (by simp)
  obtain ⟨ab, hab, _⟩ := complex_plane_biholomorphism_affine.1 k k.symm hk hki
    k.symm_apply_apply k.apply_symm_apply
  refine ⟨c.symm ab.1, c.symm ab.2, fun p ↦ ?_⟩
  apply c.injective
  have he := hab.2.1 (c' (e' p))
  simpa [k, map_add, map_smul, smul_eq_mul, mul_comm] using he

end HolomorphicAnosov


