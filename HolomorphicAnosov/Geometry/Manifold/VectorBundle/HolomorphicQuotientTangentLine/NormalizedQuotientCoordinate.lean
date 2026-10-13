import Mathlib.LinearAlgebra.Dimension.Finrank
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.Basic

/-! Normalized continuous linear coordinates on one-dimensional tangent quotient fibres (Demailly, V
§1, pp.253–254, §11, p.267, (14.1), p.273; Zhang, §2.1, pp.4–5). -/

open Bundle Set
open scoped Manifold ContDiff Topology _root_.Topology Classical

noncomputable section

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

omit [IsManifold (complexModel d) ∞ X] in
/-- A transverse tangent vector determines a quotient coordinate normalized to send its class to
`1`. The inverse sends a scalar `c` to the class of `c • T x`. -/
theorem normalized_quotient_coordinate
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hline : IsQuotientTangentLine P) (V : Set X)
    (T : (x : X) → TangentSpace (complexModel d) x)
    (hT : ∀ x ∈ V, T x ∉ P x) :
    ∃ (θ : (x : X) → TangentSpace (complexModel d) x →L[ℂ] ℂ),
      (∀ x ∈ V, (θ x).ker = P x) ∧ (∀ x ∈ V, θ x (T x) = 1) ∧
      ∀ x ∈ V, ∃ L : HolomorphicQuotientTangentLine P x ≃L[ℂ] ℂ,
        (∀ v, L ((P x).mkQ v) = θ x v) ∧
        (∀ c, L.symm c = (P x).mkQ (c • T x)) := by
  classical
  let A (x : X) : HolomorphicQuotientTangentLine P x ≃ₗ[ℂ] ℂ :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hline x)
  let b (x : X) := A x ((P x).mkQ (T x))
  have hb : ∀ x ∈ V, b x ≠ 0 := by
    intro x hx hzero
    apply hT x hx
    apply (Submodule.Quotient.mk_eq_zero (P x)).mp
    apply (A x).injective
    simpa [b] using hzero
  let θ (x : X) : TangentSpace (complexModel d) x →L[ℂ] ℂ :=
    ((b x)⁻¹ • ((A x).toLinearMap.comp (P x).mkQ)).toContinuousLinearMap
  have hker : ∀ x ∈ V, (θ x).ker = P x := by
    intro x hx
    ext v
    change (b x)⁻¹ * A x ((P x).mkQ v) = 0 ↔ v ∈ P x
    rw [mul_eq_zero, inv_eq_zero, or_iff_right (hb x hx), (A x).map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero (P x)
  have hθT : ∀ x ∈ V, θ x (T x) = 1 := by
    intro x hx
    change (b x)⁻¹ * b x = 1
    exact inv_mul_cancel₀ (hb x hx)
  refine ⟨θ, hker, hθT, ?_⟩
  intro x hx
  let f := (P x).liftQL (θ x) (hker x hx).ge
  have hf : Function.Bijective f := by
    refine ⟨LinearMap.ker_eq_bot.mp ?_, ?_⟩
    · exact (P x).ker_liftQ_eq_bot (θ x).toLinearMap (hker x hx).ge (hker x hx).le
    · intro c
      refine ⟨(P x).mkQ (c • T x), ?_⟩
      change θ x (c • T x) = c
      simp [hθT x hx]
  let L := LinearEquiv.ofBijective f.toLinearMap hf
  have hinv : ∀ c, L.symm c = (P x).mkQ (c • T x) := by
    intro c
    apply L.injective
    rw [L.apply_symm_apply]
    change c = θ x (c • T x)
    simp [hθT x hx]
  let C : HolomorphicQuotientTangentLine P x ≃L[ℂ] ℂ := {
    toLinearEquiv := L
    continuous_toFun := f.continuous
    continuous_invFun := by
      have hc : Continuous (fun c : ℂ ↦ (P x).mkQ (c • T x)) :=
        (P x).mkQL.continuous.comp (continuous_id.smul continuous_const)
      exact hc.congr (fun c ↦ (hinv c).symm) }
  exact ⟨C, fun _ ↦ rfl, hinv⟩


end HolomorphicAnosov
