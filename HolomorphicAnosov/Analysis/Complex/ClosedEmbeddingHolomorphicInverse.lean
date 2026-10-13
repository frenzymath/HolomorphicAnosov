import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Holomorphic inverse agreeing with a prescribed continuous extension

Source: McMullen, *Advanced Complex Analysis*, univalence paragraph p.58,
and Lebl, *Tasty Bits of Several Complex Variables*, Version 3.4,
§1.6 Theorem 1.6.5, pp.37–38, in complex dimension one.
-/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Complex

/-- The inverse of a holomorphic bijection agrees on its open target with the
inverse of any supplied continuous extension homeomorphism.

Source: McMullen, *Advanced Complex Analysis*, p.58, and Lebl Version 3.4,
§1.6 Theorem 1.6.5, pp.37–38. The inverse-extension compatibility is the
literal map construction used for the rectangle argument of Farb–Margalit,
Version 5.0, §11.5 Theorem 11.10, pp.341–343.

Proof: Extend the inverse subtype homeomorphism by zero outside its carrier.
On that carrier it is the prescribed inverse and is continuous. Every point
of the open target has a preimage in the open source by the given bijection;
the extension equality and homeomorphism inverse identity show that the
constructed inverse takes precisely that preimage. This proves the two inverse
identities and the reverse bijection. At any target point, openness and carrier
inclusion turn carrier continuity into ambient continuity. The forward
holomorphic injection has nonzero complex derivative at its inverse point.
The ordinary local-inverse derivative theorem therefore makes the constructed
inverse complex differentiable. No regularity on either carrier boundary is used.
-/
theorem exists_holomorphic_inverse_extension
    {U V K L : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUK : U ⊆ K) (hVL : V ⊆ L)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V)
    (e : K ≃ₜ L) (he : ∀ z : K, (z : ℂ) ∈ U → (e z : ℂ) = f z) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g V ∧ BijOn g V U ∧
      (∀ w : L, g w = (e.symm w : ℂ)) := by
  classical
  let g : ℂ → ℂ := Function.extend Subtype.val (fun w : L ↦ (e.symm w : ℂ)) (fun _ ↦ 0)
  have hg (w : ℂ) (hw : w ∈ L) : g w = (e.symm ⟨w, hw⟩ : ℂ) :=
    Subtype.val_injective.extend_apply _ _ ⟨w, hw⟩
  have hgc : ContinuousOn g L := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (fun w : L ↦ g w) = (fun w : L ↦ (e.symm w : ℂ)) :=
      funext fun w ↦ hg w w.property
    change Continuous (fun w : L ↦ g w)
    rw [heq]
    exact continuous_subtype_val.comp e.symm.continuous
  have hgf (z : ℂ) (hz : z ∈ U) : g (f z) = z := by
    have hez := he ⟨z, hUK hz⟩ hz
    rw [← hez, hg _ (e ⟨z, hUK hz⟩).property]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hUK hz⟩)
  have hgu (w : ℂ) (hw : w ∈ V) : g w ∈ U ∧ f (g w) = w := by
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
    rw [hgf z hz]
    exact ⟨hz, rfl⟩
  refine ⟨g, ?_, ?_, fun w ↦ hg w w.property⟩
  · intro w hw
    have hcont : ContinuousAt g w :=
      hgc.continuousAt (mem_of_superset (hV.mem_nhds hw) hVL)
    have hd := (hf.differentiableAt (hU.mem_nhds (hgu w hw).1)).hasDerivAt
    have hne := HolomorphicAnosov.lebl_scalar_deriv_ne_zero hU hf hbij.injOn _ (hgu w hw).1
    have hi : ∀ᶠ t in 𝓝 w, f (g t) = t := by
      filter_upwards [hV.mem_nhds hw] with t ht
      exact (hgu t ht).2
    exact (HasDerivAt.of_local_left_inverse hcont hd hne hi).differentiableAt.differentiableWithinAt
  · refine ⟨fun w hw ↦ (hgu w hw).1, ?_, ?_⟩
    · intro w hw v hv heq
      calc
        w = f (g w) := (hgu w hw).2.symm
        _ = f (g v) := congrArg f heq
        _ = v := (hgu v hv).2
    · intro z hz
      exact ⟨f z, hbij.mapsTo hz, hgf z hz⟩

end HolomorphicAnosov.Analysis.Complex

