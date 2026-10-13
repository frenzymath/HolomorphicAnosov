import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Constructions
import HolomorphicAnosov.Analysis.Complex.NormalizedUnivalentDefinitions

/-!
# Pointwise continuity of univalent maps with two fixed values

This is an agent-written expansion of the continuity step omitted in Ghys,
*Holomorphic Anosov systems* (1995), Proposition 3.1, pp.590–593.
The analytic input is the compactness theorem of Lyubich, §4.4 Theorem 4.12,
pp.113–114, supplied explicitly as a hypothesis. The derivative is nonzero
for the local biholomorphic developments to which the parent applies this lemma.
-/

noncomputable section
open Set Filter _root_.Topology

namespace HolomorphicAnosov

/-- A pointwise continuous family of univalent disk maps normalized at two
distinct points is continuous in the compact-open topology.

Proof: divide each map by the norm of its nonzero derivative at zero to obtain
a member of the compact derivative-normalized family. On that family, evaluation
at the nonzero anchor never vanishes, by injectivity and the normalization at zero.
Thus division by the anchor value is continuous and has compact image. The original
family takes values in this image. Evaluation embeds this compact image into the
Hausdorff product of scalar value spaces, so its inverse on the image is continuous.
Pointwise continuity therefore implies compact-open continuity. This argument
allows arbitrary topological parameter spaces and does not differentiate a
pointwise limit. No boundary regularity or transverse differentiability is assumed.

Source: agent-written omitted-step expansion for Ghys Proposition 3.1;
the compactness input is Lyubich Theorem 4.12, pp.113–114.
-/
theorem continuous_anchored_univalent
    (hcompact : IsCompact {g : C(Complex.UnitDisc, ℂ) | IsNormalizedUnivalent g})
    {T : Type*} [TopologicalSpace T] (F : T → C(Complex.UnitDisc, ℂ))
    (b : Complex.UnitDisc) (hb : b ≠ 0)
    (hF : ∀ t, DifferentiableOn ℂ (unitDiscExtension (F t)) (Metric.ball 0 1) ∧
      Function.Injective (F t) ∧ F t 0 = 0 ∧ F t b = 1 ∧
      deriv (unitDiscExtension (F t)) 0 ≠ 0)
    (hpoint : ∀ z, Continuous (fun t ↦ F t z)) : Continuous F := by
  let K : Set C(Complex.UnitDisc, ℂ) := {g | IsNormalizedUnivalent g}
  let R : C(Complex.UnitDisc, ℂ) → C(Complex.UnitDisc, ℂ) := fun g ↦ (g b)⁻¹ • g
  have hbK : ∀ g ∈ K, g b ≠ 0 := by
    intro g hg heq
    apply hb
    exact hg.2.1 (heq.trans hg.2.2.1.symm)
  have hR : ContinuousOn R K := by
    exact ((continuous_eval_const b).continuousOn.inv₀ hbK).smul continuousOn_id
  have hRK : IsCompact (R '' K) := hcompact.image_of_continuousOn hR
  have hmem : ∀ t, F t ∈ R '' K := by
    intro t
    obtain ⟨hd, hinj, hzero, hone, hderiv⟩ := hF t
    let c : ℂ := (‖deriv (unitDiscExtension (F t)) 0‖ : ℂ)⁻¹
    have hn : ‖deriv (unitDiscExtension (F t)) 0‖ ≠ 0 := norm_ne_zero_iff.mpr hderiv
    have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
    let g : C(Complex.UnitDisc, ℂ) := c • F t
    have hext : unitDiscExtension g = fun z ↦ c * unitDiscExtension (F t) z := by
      funext z
      simp only [unitDiscExtension, g]
      split_ifs
      · rfl
      · exact (mul_zero c).symm
    have hg : IsNormalizedUnivalent g := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hext]
        exact hd.const_mul c
      · intro z w h
        apply hinj
        exact mul_left_cancel₀ hc h
      · change c * F t 0 = 0
        rw [hzero, mul_zero]
      · rw [hext, deriv_const_mul_field, norm_mul]
        simp only [c, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact inv_mul_cancel₀ hn
    refine ⟨g, hg, ?_⟩
    ext z
    change (c * F t b)⁻¹ * (c * F t z) = F t z
    rw [hone, mul_one, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  let : CompactSpace (R '' K) := isCompact_iff_compactSpace.mp hRK
  let E : (R '' K) → (Complex.UnitDisc → ℂ) := fun g ↦ g.val
  have hE : Continuous E := continuous_coeFun.comp continuous_subtype_val
  have hEinj : Function.Injective E := by
    intro g h heq
    apply Subtype.ext
    exact DFunLike.coe_injective heq
  have hFE : Continuous (fun t ↦ E ⟨F t, hmem t⟩) := continuous_pi hpoint
  have hFK : Continuous (fun t ↦ (⟨F t, hmem t⟩ : R '' K)) :=
    (hE.isClosedEmbedding hEinj).isEmbedding.isInducing.continuous_iff.mpr hFE
  exact continuous_subtype_val.comp hFK


end HolomorphicAnosov
