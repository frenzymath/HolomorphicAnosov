import HolomorphicAnosov.Topology.Franks.NativePointedSemiconjugacy
import HolomorphicAnosov.Topology.Franks.GlobalProductInjectivity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Properness of a bounded coordinate correction

Source: Franks, *Anosov Diffeomorphisms* (1970), Lemma 3.4, pp.75–76,
and Franks (1969), Lemma 1.6 and §1.8, pp.120–123. A bounded difference
between a coordinate homeomorphism and a continuous correction is proper.
-/

namespace HolomorphicAnosov.FranksOriginalCover

/-- A bounded correction of topological real coordinates is proper on the
original source. For compact K, the coordinate norm on its inverse image
is bounded by the correction bound, the center norm and a norm bound on K.
That coordinate image is closed, hence compact by finite-dimensional
Heine–Borel. Transport compactness back by the actual homeomorphism.
This is the bounded-correction properness argument used in Franks (1969),
Lemma1.6 p.121 and Franks (1970), Lemma3.4 pp.75–76. -/
theorem proper_of_bounded_coordinate_correction_g2
    {n : ℕ} {P : Type*} [TopologicalSpace P]
    (Q : P ≃ₜ (Fin n → ℝ)) (H : C(P, Fin n → ℝ))
    (c : Fin n → ℝ) (K : ℝ)
    (hb : ∀ x, ‖(Q x - c) - H x‖ ≤ K) : IsProperMap H := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨H.continuous, ?_⟩
  intro C hC
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  let S : Set (Fin n → ℝ) := (H ∘ Q.symm) ⁻¹' C
  have hSclosed : IsClosed S := hC.isClosed.preimage (H.continuous.comp Q.symm.continuous)
  have hSbound : Bornology.IsBounded S := by
    apply (isBounded_iff_forall_norm_le).mpr
    refine ⟨K + ‖c‖ + R, ?_⟩
    intro v hv
    have he : v = ((v - c) - H (Q.symm v)) + c + H (Q.symm v) := by abel
    have hB : ‖(v - c) - H (Q.symm v)‖ ≤ K := by
      simpa only [Q.apply_symm_apply] using hb (Q.symm v)
    calc
      ‖v‖ = ‖((v - c) - H (Q.symm v)) + c + H (Q.symm v)‖ := congrArg norm he
      _ ≤ ‖(v - c) - H (Q.symm v)‖ + ‖c‖ + ‖H (Q.symm v)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ K + ‖c‖ + R := add_le_add (add_le_add hB le_rfl) (hR _ hv)
  have hcompact := (Metric.isCompact_of_isClosed_isBounded hSclosed hSbound).image Q.symm.continuous
  have heq : Q.symm '' S = H ⁻¹' C := by
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hx
      exact ⟨Q x, by simpa only [S, Set.mem_preimage, Function.comp_apply,
        Q.symm_apply_apply] using hx, Q.symm_apply_apply x⟩
  rwa [heq] at hcompact


end HolomorphicAnosov.FranksOriginalCover

