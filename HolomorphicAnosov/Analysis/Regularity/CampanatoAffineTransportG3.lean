import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace HolomorphicAnosov.Analysis.Regularity

/-- Affine change of variables for a measurable set in Euclidean space.

Source: Campanato, *Proprietà di una famiglia di spazi funzionali* (1964),
Lemma [2.I], equation (2.12), p.143, together with the real Jacobian
change-of-variables theorem. This provider records the scalar Jacobian and
preimage explicitly, independently of the polynomial coefficient estimate.
Proof: realize dilation followed by translation as a measurable equivalence.
Dilation pushes volume forward to the inverse N-th power times volume, while
translation preserves volume. Transport the set integral through the equivalence
and cancel the nonzero power. This works even for arbitrary sets and functions,
so the stated null-measurability and integrability assumptions cause no restriction.
-/
theorem campanato_affine_setIntegral_transport_g3
    (N : ℕ) (a : EuclideanSpace ℝ (Fin N)) (ρ : ℝ)
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (E : Set (EuclideanSpace ℝ (Fin N)))
    (hρ : 0 < ρ) (_hE : NullMeasurableSet E volume)
    (_hf : IntegrableOn f E volume) :
    (∫ x in E, f x) =
      ρ ^ N * ∫ y in ((fun y ↦ a + ρ • y) ⁻¹' E), f (a + ρ • y) := by
  let e : EuclideanSpace ℝ (Fin N) ≃ᵐ EuclideanSpace ℝ (Fin N) :=
    (MeasurableEquiv.smul₀ ρ hρ.ne').trans (MeasurableEquiv.addLeft a)
  have he : ∀ y : EuclideanSpace ℝ (Fin N), e y = a + ρ • y := by
    intro y
    rfl
  have hmap : Measure.map (e : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) volume =
      ENNReal.ofReal ((ρ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)))⁻¹) • volume := by
    calc
      Measure.map (e : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) volume =
          Measure.map (fun x : EuclideanSpace ℝ (Fin N) ↦ a + x)
            (Measure.map (fun y : EuclideanSpace ℝ (Fin N) ↦ ρ • y) volume) := by
        rw [Measure.map_map]
        · rfl
        · fun_prop
        · fun_prop
      _ = Measure.map (fun x : EuclideanSpace ℝ (Fin N) ↦ a + x)
            (ENNReal.ofReal |(ρ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)))⁻¹| • volume) := by
        rw [Measure.map_addHaar_smul volume hρ.ne']
      _ = ENNReal.ofReal |(ρ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)))⁻¹| • volume := by
        rw [Measure.map_smul]
        · rw [map_add_left_eq_self]
        · fun_prop
      _ = ENNReal.ofReal ((ρ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin N)))⁻¹) • volume := by
        rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hρ.le _))]
  have htransport := MeasureTheory.setIntegral_map_equiv (μ := volume) e f E
  rw [hmap] at htransport
  rw [Measure.restrict_smul, integral_smul_measure] at htransport
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := by simp
  have hnonneg : 0 ≤ (ρ ^ N)⁻¹ := inv_nonneg.2 (pow_nonneg hρ.le _)
  rw [hdim, ENNReal.toReal_ofReal hnonneg, smul_eq_mul] at htransport
  have hp : 0 < ρ ^ N := pow_pos hρ N
  have hpre : (e ⁻¹' E) = ((fun y : EuclideanSpace ℝ (Fin N) ↦ a + ρ • y) ⁻¹' E) := by
    ext y
    change e y ∈ E ↔ a + ρ • y ∈ E
    rw [he]
  have hfun : (fun x : EuclideanSpace ℝ (Fin N) ↦ f (e x)) =
      (fun y : EuclideanSpace ℝ (Fin N) ↦ f (a + ρ • y)) := by
    funext y
    rw [he]
  calc
    (∫ x in E, f x) = ρ ^ N * ((ρ ^ N)⁻¹ * (∫ x in E, f x)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    _ = ρ ^ N * (∫ x in e ⁻¹' E, f (e x)) := by rw [htransport]
    _ = ρ ^ N * (∫ y in ((fun y ↦ a + ρ • y) ⁻¹' E), f (a + ρ • y)) := by
      rw [hpre, hfun]

end HolomorphicAnosov.Analysis.Regularity
