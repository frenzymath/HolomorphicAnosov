import HolomorphicAnosov.Analysis.ComplexDifferentiableOfComplexRange
import HolomorphicAnosov.Geometry.ComplexLinearLeftInverse
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition.EuclideanInverse
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! Real projected coordinates give holomorphic graph parametrizations for smooth maps with complex
tangent ranges. (Demailly, Lemma I.7.15, p. 60) -/

namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff Manifold Topology _root_.Topology

/-- An injective real-linear map with complex-invariant range admits a complex-linear projection
whose composition with that map is invertible over ℝ. (Demailly, Lemma I.7.15, p. 60) -/
theorem real_complex_projection
    {k d : ℕ} (D : (Fin (2*k) → ℝ) →L[ℝ] ComplexModel d)
    (hi : Function.Injective D)
    (hD : ∀ a : ℂ, ∀ v, a • D v ∈ D.range) :
    ∃ P : ComplexModel d →L[ℂ] ComplexModel k,
      Function.Bijective ((P.restrictScalars ℝ).comp D) := by
  let V : Submodule ℂ (ComplexModel d) :=
    { carrier := D.range
      zero_mem' := D.range.zero_mem
      add_mem' := D.range.add_mem
      smul_mem' := by
        intro a w hw
        obtain ⟨v, rfl⟩ := hw
        exact hD a v }
  have hV : V.restrictScalars ℝ = D.range := rfl
  have hd : 2 * Module.finrank ℂ V = 2*k := by
    rw [← finrank_real_of_complex]
    change Module.finrank ℝ (V.restrictScalars ℝ) = 2*k
    rw [hV, LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]
  have hdim : Module.finrank ℂ (ComplexModel k) = Module.finrank ℂ V := by
    rw [Module.finrank_fin_fun]
    omega
  let e : ComplexModel k ≃L[ℂ] V :=
    (LinearEquiv.ofFinrankEq (ComplexModel k) V hdim).toContinuousLinearEquiv
  let A : ComplexModel k →L[ℂ] ComplexModel d := V.subtypeL.comp e.toContinuousLinearMap
  obtain ⟨P, hP⟩ := complex_linear_left_inverse_of_injective A
    (Subtype.val_injective.comp e.injective)
  have hPA (z : ComplexModel k) : P (A z) = z :=
    congrArg (fun T : ComplexModel k →L[ℂ] ComplexModel k ↦ T z) hP
  have hevery (v : Fin (2*k) → ℝ) : A (e.symm ⟨D v, ⟨v, rfl⟩⟩) = D v := by
    change (e (e.symm ⟨D v, ⟨v, rfl⟩⟩) : ComplexModel d) = D v
    simp
  have hPD : Function.Injective ((P.restrictScalars ℝ).comp D) := by
    intro v w hvw
    apply hi
    rw [← hevery v, ← hevery w]
    congr 1
    rw [← hPA (e.symm ⟨D v, ⟨v, rfl⟩⟩), ← hPA (e.symm ⟨D w, ⟨w, rfl⟩⟩)]
    rw [hevery, hevery]
    exact hvw
  refine ⟨P, hPD, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hPD
  rw [Module.finrank_fin_fun, finrank_real_of_complex, Module.finrank_fin_fun]

/-- A smooth map with complex tangent ranges admits local real inverse-function coordinates in which
its graph parametrization is holomorphic and has injective derivative. (Demailly, Lemma I.7.15,
p. 60) -/
theorem real_complex_projected_graph
    {k d : ℕ} {g : (Fin (2*k) → ℝ) → ComplexModel d}
    {U : Set (Fin (2*k) → ℝ)} (hU : IsOpen U)
    {a : Fin (2*k) → ℝ} (ha : a ∈ U)
    (hg : ContDiffOn ℝ ∞ g U)
    (hi : Function.Injective (fderiv ℝ g a))
    (hD : ∀ z ∈ U, ∀ b : ℂ, ∀ v, b • fderiv ℝ g z v ∈ (fderiv ℝ g z).range) :
    ∃ p : OpenPartialHomeomorph (Fin (2*k) → ℝ) (ComplexModel k),
      a ∈ p.source ∧ p.source ⊆ U ∧
      ContDiffOn ℝ ∞ p p.source ∧ ContDiffOn ℝ ∞ p.symm p.target ∧
      ContDiffOn ℂ ∞ (g ∘ p.symm) p.target ∧
      Function.Injective (fderiv ℂ (g ∘ p.symm) (p a)) := by
  obtain ⟨P, hP⟩ := real_complex_projection (fderiv ℝ g a) hi (hD a ha)
  let D := (P.restrictScalars ℝ).comp (fderiv ℝ g a)
  let e : (Fin (2*k) → ℝ) ≃L[ℝ] ComplexModel k :=
    (LinearEquiv.ofBijective D.toLinearMap hP).toContinuousLinearEquiv
  have hPg : ContDiffOn ℝ ∞ (P ∘ g) U :=
    (P.restrictScalars ℝ).contDiff.comp_contDiffOn hg
  have hder : HasFDerivAt (P ∘ g) e.toContinuousLinearMap a :=
    (P.restrictScalars ℝ).hasFDerivAt.comp a
      ((hg.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨p, hpa, hpU, hp⟩ := W07ManifoldInverseFunction.euclidean_inverse hU ha hPg e hder
  let q := p.toOpenPartialHomeomorph
  have hq : (q : (Fin (2*k) → ℝ) → ComplexModel k) = P ∘ g := hp
  have hqs : ContDiffOn ℝ ∞ q q.source := p.contMDiffOn.contDiffOn
  have hqi : ContDiffOn ℝ ∞ q.symm q.target := p.symm.contMDiffOn.contDiffOn
  have hgr : ContDiffOn ℝ ∞ (g ∘ q.symm) q.target :=
    hg.comp hqi (fun z hz ↦ hpU (q.map_target hz))
  have hleft (z) (hz : z ∈ q.target) :
      (P.restrictScalars ℝ).comp (fderiv ℝ (g ∘ q.symm) z) =
        ContinuousLinearMap.id ℝ (ComplexModel k) := by
    have heq : P ∘ (g ∘ q.symm) =ᶠ[𝓝 z] id := by
      filter_upwards [q.open_target.mem_nhds hz] with w hw
      change P (g (q.symm w)) = w
      rw [← Function.comp_apply (f := P), ← hq]
      exact q.right_inv hw
    have hf := (hgr.contDiffAt (q.open_target.mem_nhds hz)).differentiableAt (by simp)
    rw [← ((P.restrictScalars ℝ).hasFDerivAt.comp z hf.hasFDerivAt).fderiv]
    change fderiv ℝ (P ∘ (g ∘ q.symm)) z = _
    rw [heq.fderiv_eq, fderiv_id]
  have hgc : DifferentiableOn ℂ (g ∘ q.symm) q.target := by
    intro z hz
    have hgz := (hg.contDiffAt (hU.mem_nhds (hpU (q.map_target hz)))).differentiableAt (by simp)
    have hqz := (hqi.contDiffAt (q.open_target.mem_nhds hz)).differentiableAt (by simp)
    apply (complex_differentiableAt_of_complex_range
      (hgz.comp z hqz) P ?_ ?_).differentiableWithinAt
    · intro v
      exact congrArg (fun T : ComplexModel k →L[ℝ] ComplexModel k ↦ T v) (hleft z hz)
    · intro b v
      rw [fderiv_comp z hgz hqz]
      obtain ⟨w, hw⟩ := hD (q.symm z) (hpU (q.map_target hz)) b (fderiv ℝ q.symm z v)
      have hpm : q.symm.MDifferentiable (realModel k) 𝓘(ℝ, Fin (2*k) → ℝ) :=
        ⟨p.symm.mdifferentiableOn (by simp), p.mdifferentiableOn (by simp)⟩
      have hsurj := hpm.mfderiv_surjective hz
      rw [mfderiv_eq_fderiv] at hsurj
      change Function.Surjective (fderiv ℝ q.symm z : ComplexModel k → (Fin (2*k) → ℝ)) at hsurj
      obtain ⟨v', hv'⟩ := hsurj w
      refine ⟨v', ?_⟩
      change fderiv ℝ g (q.symm z) (fderiv ℝ q.symm z v') = _
      rw [hv']
      exact hw
  have hgsm := (complex_contDiffOn_iff_differentiableOn q.open_target).mpr hgc
  refine ⟨q, hpa, hpU, hqs, hqi, hgsm, ?_⟩
  have hz := q.map_source hpa
  have hc := (hgc (q a) hz).differentiableAt (q.open_target.mem_nhds hz)
  have hr := hleft (q a) hz
  rw [hc.fderiv_restrictScalars (𝕜 := ℝ)] at hr
  intro v w hvw
  have hh := congrArg P hvw
  have hv := congrArg (fun T : ComplexModel k →L[ℝ] ComplexModel k ↦ T v) hr
  have hw := congrArg (fun T : ComplexModel k →L[ℝ] ComplexModel k ↦ T w) hr
  exact hv.symm.trans (hh.trans hw)

end HolomorphicAnosov

