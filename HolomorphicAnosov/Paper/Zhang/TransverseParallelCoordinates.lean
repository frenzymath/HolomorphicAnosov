import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import HolomorphicAnosov.Paper.Zhang.Support.HolomorphicScalarSubmersion
import HolomorphicAnosov.Paper.Zhang.Support.BottBracketChartTransport
import HolomorphicAnosov.Paper.Zhang.Support.ScalarDirectionalChartTransport
import HolomorphicAnosov.Paper.Zhang.Support.ImaginaryFieldChartTransport
import HolomorphicAnosov.Paper.Zhang.Support.RealCovariantExteriorCoordinateEvaluation
import HolomorphicAnosov.Paper.Zhang.Support.CovariantExteriorBottCancel
import HolomorphicAnosov.Paper.Zhang.Support.HolomorphicTangentFieldExtension
import HolomorphicAnosov.Paper.Zhang.Support.CoordinateExteriorRankOne
import HolomorphicAnosov.Paper.Zhang.Support.QuotientCoordinateFormRegularity
import HolomorphicAnosov.Paper.Zhang.Support.ParallelFrameOfIntegratingFactor
import HolomorphicAnosov.Paper.Zhang.Support.FlatCoordinateIntegratingFactor
import HolomorphicAnosov.Paper.Zhang.Support.CoordinateIntegratingFactorPullback
import HolomorphicAnosov.Paper.Zhang.Support.CoordinateIntegratingFactorHolomorphic
import HolomorphicAnosov.Paper.Zhang.Support.HolomorphicFrameRestriction
import HolomorphicAnosov.Paper.Zhang.Support.ClosedCoordinateFormPrimitive
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.SmoothTangentFieldOfHolomorphic
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus
import HolomorphicAnosov.Paper.Zhang.ConnectionHolomorphicFlat
import HolomorphicAnosov.Paper.Zhang.RankOneStableHolomorphicUnstable
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.Geometry.Manifold.Submersion

/-! Local holomorphic transverse coordinates and parallel frames for the quotient by the unstable
bundle. (Zhang, Lemma 2.4, p.7, equations (12)–(13)) -/

noncomputable section

namespace HolomorphicAnosov.Paper.Zhang

open scoped ContDiff Manifold

attribute [local instance] complex_isManifold_real

universe u

/-- The differential of `t` on the complex tangent fibre, with its target identified with `ℂ`.
(Zhang, Lemma 2.4, p.7) -/
def transverseScalarDifferential {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    (t : X → ℂ) (y : X) : TangentSpace (complexModel d) y →L[ℂ] ℂ :=
  (tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y)).toContinuousLinearMap.comp
    (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y)

namespace TransverseParallelSupport

/-- If `π = dt ⊗ σ` with `σ ≠ 0`, then `dt` has kernel `U` and a continuous linear right inverse.
(Zhang, Lemma 2.4, p.7) -/
theorem differential_quotient_data
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : (y : X) → Submodule ℂ (TangentSpace (complexModel d) y))
    (t : X → ℂ) (y : X) (σ : QuotientLineConnection.Fibre U y) (hσ : σ ≠ 0)
    (hformula : ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t y v • σ) :
    (transverseScalarDifferential t y).ker = U y ∧
      ∃ R : ℂ →L[ℂ] TangentSpace (complexModel d) y,
        (transverseScalarDifferential t y).comp R = ContinuousLinearMap.id ℂ ℂ := by
  constructor
  · ext v
    change transverseScalarDifferential t y v = 0 ↔ v ∈ U y
    rw [← Submodule.Quotient.mk_eq_zero]
    change _ ↔ QuotientLineConnection.projection U y v = 0
    rw [hformula v]
    simp [hσ]
  · obtain ⟨v, hv⟩ := (U y).mkQ_surjective σ
    have hvone : transverseScalarDifferential t y v = 1 := by
      apply smul_left_injective ℂ hσ
      simpa only [one_smul] using (hformula v).symm.trans hv
    refine ⟨(ContinuousLinearMap.id ℂ ℂ).smulRight v, ?_⟩
    apply ContinuousLinearMap.ext
    intro z
    simp [hvone]

/-- The manifold derivative of `t` is surjective when the quotient projection equals `dt ⊗ σ` with
`σ ≠ 0`. -/
theorem mfderiv_surjective_of_quotient_formula
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : (y : X) → Submodule ℂ (TangentSpace (complexModel d) y))
    (t : X → ℂ) (y : X) (σ : QuotientLineConnection.Fibre U y) (hσ : σ ≠ 0)
    (hformula : ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t y v • σ) :
    Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y) := by
  obtain ⟨_, R, hR⟩ := differential_quotient_data U t y σ hσ hformula
  intro w
  refine ⟨R (tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y) w), ?_⟩
  apply (tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y)).injective
  exact DFunLike.congr_fun hR _

/-- The scalar differential of `t` is surjective when the quotient projection equals `dt ⊗ σ` with
`σ ≠ 0`. -/
theorem differential_surjective_of_quotient_formula
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (U : (y : X) → Submodule ℂ (TangentSpace (complexModel d) y))
    (t : X → ℂ) (y : X) (σ : QuotientLineConnection.Fibre U y) (hσ : σ ≠ 0)
    (hformula : ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t y v • σ) :
    Function.Surjective (transverseScalarDifferential (d := d) t y) := by
  obtain ⟨_, R, hR⟩ := differential_quotient_data U t y σ hσ hformula
  intro z
  refine ⟨R z, ?_⟩
  exact DFunLike.congr_fun hR z

/-- An alternating complex bilinear form annihilating `U` vanishes if the quotient by `U` is
one-dimensional. (Zhang, Lemma 2.4, p.7, equation (13)) -/
theorem alternating_form_zero_of_quotient_line
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (U : Submodule ℂ E) (e : (E ⧸ U) ≃ₗ[ℂ] ℂ)
    (β : E →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (halt : ∀ v, β v v = 0)
    (hU : ∀ v ∈ U, ∀ w, β v w = 0) : β = 0 := by
  have hswap : ∀ v w, β v w = -β w v := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have hUright : ∀ w ∈ U, ∀ v, β v w = 0 := by
    intro w hw v
    rw [hswap, hU w hw v, neg_zero]
  obtain ⟨v₀, hv₀⟩ := U.mkQ_surjective (e.symm 1)
  have hres : ∀ v : E, v - e (U.mkQ v) • v₀ ∈ U := by
    intro v
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (v - e (U.mkQ v) • v₀) = 0
    rw [map_sub, map_smul, hv₀]
    apply e.injective
    simp
  have hleft : ∀ v w, β v w = e (U.mkQ v) * β v₀ w := by
    intro v w
    have h := hU _ (hres v) w
    simpa only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, sub_eq_zero] using h
  ext v w
  change β v w = 0
  rw [hleft v w, hswap v₀ w, hleft w v₀, halt v₀, mul_zero, neg_zero, mul_zero]

end TransverseParallelSupport
end HolomorphicAnosov.Paper.Zhang

namespace HolomorphicAnosov.Paper.Zhang
open TransverseParallelSupport
open Set TopologicalSpace Bundle
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
/-- For a compact complex manifold of dimension at least three with a holomorphic Anosov
diffeomorphism and one-dimensional stable bundle, the unstable quotient line admits local
nonvanishing parallel holomorphic frames `σ` and holomorphic submersions `t` satisfying `π = dt
⊗ σ` and `ker dt = Eᵘ`. (Zhang, Lemma 2.4, p.7, equations (12)–(13); Definition 2.1, p.4,
equation (2); Demailly, Ch. V, §2, equations (2.1)–(2.3), p.255, and §3, equations (3.1)–(3.2),
p.256) -/
theorem transverse_parallel_coordinates
    {d : ℕ} (hd : 3 ≤ d) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hunstable : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : QuotientLineConnection.Connection U)
    (hcontinuous : QuotientLineConnection.IsContinuous nabla)
    (hcompatible : QuotientLineConnection.IsCompatible nabla)
    (hinvariant : QuotientLineConnection.IsInvariant nabla f hU) :
    ∀ x : X, ∃ V : TopologicalSpace.Opens X, x ∈ V ∧
      ∃ (σ : (y : X) → QuotientLineConnection.Fibre U y) (t : X → ℂ),
        QuotientLineConnection.IsHolomorphicSection U V σ ∧
        (∀ y ∈ V, σ y ≠ 0) ∧
        QuotientLineConnection.IsParallelOn nabla V σ ∧
        ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V ∧
        (∀ y ∈ V, Manifold.IsSubmersionAt (complexModel d) 𝓘(ℂ, ℂ) ∞ t y) ∧
        ∀ y ∈ V,
          (∀ v : TangentSpace (complexModel d) y,
            QuotientLineConnection.projection U y v =
              transverseScalarDifferential t y v • σ y) ∧
          (transverseScalarDifferential t y).ker = U y := by
  have hprimitive
      {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
      [IsManifold (complexModel d) ∞ X]
      (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
      (hU : IsHolomorphicTangentSubbundle r U) (hline : IsQuotientTangentLine U)
      (nabla : QuotientLineConnection.Connection U)
      (hcompatible : QuotientLineConnection.IsCompatible nabla)
      (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
      (hzero : ∀ y ∈ V, nabla.form V e y = 0) (x : X) (hx : x ∈ V) :
      ∃ W : Opens X, x ∈ W ∧ W ≤ V ∧ ∃ t : X → ℂ,
        ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t W ∧
        ∀ y ∈ W,
          (∀ v : TangentSpace (complexModel d) y,
            QuotientLineConnection.projection U y v =
              transverseScalarDifferential t y v • e.sectionValue y) ∧
          (transverseScalarDifferential t y).ker = U y ∧
          Function.Surjective (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y) := by
    classical
    have hclosure
        {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
        [IsManifold (complexModel d) ∞ X]
        (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
        (hU : IsHolomorphicTangentSubbundle r U) (hline : IsQuotientTangentLine U)
        (nabla : QuotientLineConnection.Connection U)
        (hcompatible : QuotientLineConnection.IsCompatible nabla)
        (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
        (c : OpenPartialHomeomorph X (ComplexModel d)) (hc : c ∈ atlas (ComplexModel d) X)
        (θ : ComplexModel d → ComplexModel d →L[ℂ] ℂ)
        (hθ : ∀ w (hw : w ∈ c.target ∩ c.symm ⁻¹' (V : Set X)), ∀ v : ComplexModel d,
          θ w v = e.coordinate (c.symm w) hw.2
            (QuotientLineConnection.projection U (c.symm w)
              (mfderiv (complexModel d) (complexModel d) c.symm w
                ((NormedSpace.fromTangentSpace w).symm v))))
        {z : ComplexModel d} (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X)) :
        ∀ v w : ComplexModel d,
          fderiv ℝ θ z v w - fderiv ℝ θ z w v +
            QuotientLineConnection.coordinateForm nabla e c z v * θ z w -
            QuotientLineConnection.coordinateForm nabla e c z w * θ z v = 0 := by
      have hBott
          {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
          [IsManifold (complexModel d) ∞ X]
          (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
          (nabla : QuotientLineConnection.Connection U)
          (hcompatible : QuotientLineConnection.IsCompatible nabla)
          (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
          (c : OpenPartialHomeomorph X (ComplexModel d)) (hc : c ∈ atlas (ComplexModel d) X)
          (θ : ComplexModel d → ComplexModel d →L[ℂ] ℂ)
          (hθ : ∀ w (hw : w ∈ c.target ∩ c.symm ⁻¹' (V : Set X)), ∀ v : ComplexModel d,
            θ w v = e.coordinate (c.symm w) hw.2
              (QuotientLineConnection.projection U (c.symm w)
                (mfderiv (complexModel d) (complexModel d) c.symm w
                  ((NormedSpace.fromTangentSpace w).symm v))))
          {z : ComplexModel d} (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
          (hθd : DifferentiableAt ℂ θ z)
          (Y Z : (x : X) → TangentSpace (complexModel d) x)
          (hY : QuotientLineConnection.IsSmoothTangentField V Y)
          (hZ : QuotientLineConnection.IsSmoothTangentField V Z)
          (hIY : QuotientLineConnection.IsSmoothTangentField V (fun x ↦ Complex.I • Y x))
          (hIZ : QuotientLineConnection.IsSmoothTangentField V (fun x ↦ Complex.I • Z x))
          (hYU : ∀ x ∈ V, Y x ∈ U x) :
          let Yc : ComplexModel d → ComplexModel d := VectorField.mpullback (realModel d)
            (realModel d) c.symm (fun x ↦ complexTangentToReal d x (Y x))
          let Zc : ComplexModel d → ComplexModel d := VectorField.mpullback (realModel d)
            (realModel d) c.symm (fun x ↦ complexTangentToReal d x (Z x))
          let A := QuotientLineConnection.coordinateForm nabla e c z
          fderiv ℝ θ z (Yc z) (Zc z) - fderiv ℝ θ z (Zc z) (Yc z) +
            A (Yc z) * θ z (Zc z) - A (Zc z) * θ z (Yc z) = 0 := by
        let Tc (T : (x : X) → TangentSpace (complexModel d) x) :
            ComplexModel d → ComplexModel d := VectorField.mpullback (realModel d)
              (realModel d) c.symm (fun x ↦ complexTangentToReal d x (T x))
        let g (T : (x : X) → TangentSpace (complexModel d) x) :=
          e.coefficient (fun x ↦ QuotientLineConnection.projection U x (T x))
        have hcm : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
          IsManifold.subset_maximalAtlas hc
        have hrm : c ∈ IsManifold.maximalAtlas (realModel d) ∞ X :=
          IsManifold.subset_maximalAtlas hc
        have hrm1 : c ∈ IsManifold.maximalAtlas (realModel d) 1 X :=
          IsManifold.subset_maximalAtlas hc
        have hci := contMDiffAt_symm_of_mem_maximalAtlas hrm hz.1
        have hi (w : ComplexModel d) (hw : w ∈ c.target) :
            (mfderiv (realModel d) (realModel d) c.symm w).IsInvertible := by
          have h := isInvertible_mfderivWithin_extend_symm (I := realModel d) hrm1
            (y := w) (by simpa using hw)
          simpa using h
        have hder (w : ComplexModel d) (hw : w ∈ c.target) :
            mfderiv (realModel d) (realModel d) c.symm w =
              (mfderiv (complexModel d) (complexModel d) c.symm w).restrictScalars ℝ := by
          have hf := (contMDiffAt_symm_of_mem_maximalAtlas hcm hw).mdifferentiableAt (by simp)
          have hr := (contMDiffAt_symm_of_mem_maximalAtlas hrm hw).mdifferentiableAt (by simp)
          ext v
          apply (tangentSpaceCastModel (realModel d) (c.symm w)).injective
          rw [hf.mfderiv_abuse, hr.mfderiv_abuse]
          have hd := hf.differentiableWithinAt_writtenInExtChartAt
          change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel d) w c.symm)
            (range (complexModel d)) (extChartAt (complexModel d) w w)) v =
            (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel d) w c.symm)
            (range (complexModel d)) (extChartAt (complexModel d) w w)) v
          exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
        have hcoef (T : (x : X) → TangentSpace (complexModel d) x)
            (w : ComplexModel d) (hw : w ∈ c.target ∩ c.symm ⁻¹' (V : Set X)) :
            θ w (Tc T w) = g T (c.symm w) := by
          rw [hθ w hw]
          have h := (hi w hw.1).self_apply_inverse
            (complexTangentToReal d (c.symm w) (T (c.symm w)))
          change mfderiv (realModel d) (realModel d) c.symm w (Tc T w) =
            complexTangentToReal d (c.symm w) (T (c.symm w)) at h
          rw [hder w hw.1] at h
          change mfderiv (complexModel d) (complexModel d) c.symm w
            ((NormedSpace.fromTangentSpace w).symm (Tc T w)) = T (c.symm w) at h
          rw [h]
          simp only [g, QuotientLineConnection.HolomorphicFrame.coefficient,
            dite_eq_left (show c.symm w ∈ V from hw.2)]
        have hdir (T : (x : X) → TangentSpace (complexModel d) x)
            (hgT : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (g T) (c.symm z))
            (S : (x : X) → TangentSpace (complexModel d) x) :
            fderiv ℝ (fun w ↦ θ w (Tc T w)) z (Tc S z) =
              QuotientLineConnection.realDifferential (g T) (c.symm z)
                (complexTangentToReal d (c.symm z) (S (c.symm z))) := by
          have heq : (fun w ↦ θ w (Tc T w)) =ᶠ[nhds z] (g T ∘ c.symm) := by
            filter_upwards [(c.isOpen_inter_preimage_symm V.isOpen).mem_nhds hz] with w hw
            exact hcoef T w hw
          rw [heq.fderiv_eq]
          exact scalar_directional_chart_transport c hc (g T) hz.1 hgT
            (fun x ↦ complexTangentToReal d x (S x))
        have hIdir (T : (x : X) → TangentSpace (complexModel d) x)
            (hgT : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (g T) (c.symm z))
            (S : (x : X) → TangentSpace (complexModel d) x) :
            fderiv ℝ (fun w ↦ θ w (Tc T w)) z (Complex.I • Tc S z) =
              QuotientLineConnection.realDifferential (g T) (c.symm z)
                (complexTangentToReal d (c.symm z) (Complex.I • S (c.symm z))) := by
          rw [← imaginary_field_chart_transport c hc S hz.1]
          exact hdir T hgT (fun x ↦ Complex.I • S x)
        have hA (T : (x : X) → TangentSpace (complexModel d) x) :
            QuotientLineConnection.coordinateForm nabla e c z (Tc T z) =
              nabla.form V e (c.symm z) (complexTangentToReal d (c.symm z) (T (c.symm z))) := by
          exact congrArg (nabla.form V e (c.symm z))
            ((hi z hz.1).self_apply_inverse
              (complexTangentToReal d (c.symm z) (T (c.symm z))))
        have hAI (v : ComplexModel d) :
            QuotientLineConnection.coordinateForm nabla e c z (Complex.I • v) =
              Complex.I * QuotientLineConnection.coordinateForm nabla e c z v := by
          change nabla.form V e (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z (Complex.I • v)) =
            Complex.I * nabla.form V e (c.symm z)
              (mfderiv (realModel d) (realModel d) c.symm z v)
          rw [hder z hz.1]
          change nabla.form V e (c.symm z)
            (complexTangentToReal d (c.symm z)
              (mfderiv (complexModel d) (complexModel d) c.symm z (Complex.I • v))) =
            Complex.I * nabla.form V e (c.symm z)
              (complexTangentToReal d (c.symm z)
                (mfderiv (complexModel d) (complexModel d) c.symm z v))
          rw [map_smul]
          exact hcompatible.1 V e (c.symm z) hz.2 _
        have hTp (T : (x : X) → TangentSpace (complexModel d) x)
            (hT : QuotientLineConnection.IsSmoothTangentField V T) :
            ContMDiffAt (realModel d) (realModel d).tangent ∞
              (fun x ↦ (⟨x, complexTangentToReal d x (T x)⟩ : TangentBundle (realModel d) X))
              (c.symm z) := (hT _ hz.2).contMDiffAt (V.isOpen.mem_nhds hz.2)
        have hTcd (T : (x : X) → TangentSpace (complexModel d) x)
            (hT : QuotientLineConnection.IsSmoothTangentField V T) :
            DifferentiableAt ℝ (Tc T) z := by
          have h := (hTp T hT).mpullback_vectorField_preimage hci (hi z hz.1) (by simp)
          exact (contMDiffAt_vectorSpace_iff_contDiffAt.mp h).differentiableAt (by simp)
        have hgd (T : (x : X) → TangentSpace (complexModel d) x)
            (hT : QuotientLineConnection.IsSmoothTangentField V T) :
            MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (g T) (c.symm z) := by
          let R := ContinuousLinearMap.restrictScalarsL ℂ (ComplexModel d) ℂ ℝ ℝ
          have hdc := (R.differentiableAt.comp z (hθd.restrictScalars ℝ)).clm_apply (hTcd T hT)
          change DifferentiableAt ℝ (fun w ↦ θ w (Tc T w)) z at hdc
          have heq : (g T ∘ c.symm) =ᶠ[nhds z] (fun w ↦ θ w (Tc T w)) := by
            filter_upwards [(c.isOpen_inter_preimage_symm V.isOpen).mem_nhds hz] with w hw
            exact (hcoef T w hw).symm
          have hgc := (hdc.congr_of_eventuallyEq heq).mdifferentiableAt
          have hgc' : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (g T ∘ c.symm)
              (c (c.symm z)) := by simpa only [c.right_inv hz.1] using hgc
          have hcomp := hgc'.comp (c.symm z)
            ((contMDiffAt_of_mem_maximalAtlas hrm (c.map_target hz.1)).mdifferentiableAt (by simp))
          apply hcomp.congr_of_eventuallyEq
          filter_upwards [c.open_source.mem_nhds (c.map_target hz.1)] with y hy
          change g T y = g T (c.symm (c y))
          rw [c.left_inv hy]
        have hgY := hgd Y hY
        have hgZ := hgd Z hZ
        have hbr := bott_bracket_chart_transport c hci Y Z
          ((hTp Y hY).mdifferentiableAt (by simp))
          ((hTp Z hZ).mdifferentiableAt (by simp))
          ((hTp _ hIY).mdifferentiableAt (by simp))
          ((hTp _ hIZ).mdifferentiableAt (by simp))
        have hIT (T : (x : X) → TangentSpace (complexModel d) x) :
            Tc (fun x ↦ Complex.I • T x) =ᶠ[nhds z] (fun w ↦ Complex.I • Tc T w) := by
          filter_upwards [c.open_target.mem_nhds hz.1] with w hw
          exact imaginary_field_chart_transport c hc T hw
        have hbr' := (hIT Y).lieBracket_vectorField_eq (𝕜 := ℝ) (hIT Z)
        change Tc (QuotientLineConnection.bottBracket Y Z) z =
          (1 / 2 : ℝ) • (VectorField.lieBracket ℝ (Tc Y) (Tc Z) z -
            VectorField.lieBracket ℝ (Tc (fun x ↦ Complex.I • Y x))
              (Tc (fun x ↦ Complex.I • Z x)) z) at hbr
        rw [hbr'] at hbr
        have hbcoef := hcoef (QuotientLineConnection.bottBracket Y Z) z hz
        rw [hbr] at hbcoef
        have hid := real_covariant_exterior_coordinate_evaluation θ
          (QuotientLineConnection.coordinateForm nabla e c z) (Tc Y) (Tc Z)
          (fderiv ℂ θ z) hθd.hasFDerivAt hAI (hTcd Y hY) (hTcd Z hZ)
        have hn := congrArg (e.coordinate (c.symm z) hz.2)
          (covariant_exterior_bott_cancel nabla hcompatible V e Y Z hY hZ hYU (c.symm z) hz.2)
        simp only [map_sub, map_smul, map_zero, QuotientLineConnection.covariantDerivative,
          LinearEquiv.apply_symm_apply, smul_eq_mul] at hn
        change _ = 0
        rw [← hid]
        rw [hdir Z hgZ Y, hdir Y hgY Z, hIdir Z hgZ Y, hIdir Y hgY Z,
          hbcoef, hcoef Z z hz, hcoef Y z hz, hAI, hAI, hA Y, hA Z]
        have htypeY := hcompatible.1 V e (c.symm z) hz.2 (Y (c.symm z))
        have htypeZ := hcompatible.1 V e (c.symm z) hz.2 (Z (c.symm z))
        rw [htypeY, htypeZ] at hn
        have hbval : g (QuotientLineConnection.bottBracket Y Z) (c.symm z) =
            e.coordinate (c.symm z) hz.2 (QuotientLineConnection.projection U (c.symm z)
              (QuotientLineConnection.bottBracket Y Z (c.symm z))) := by
          simp only [g, QuotientLineConnection.HolomorphicFrame.coefficient,
            dite_eq_left (show c.symm z ∈ V from hz.2)]
        rw [hbval]
        simpa only [mul_comm] using hn
      have hreg := quotient_coordinate_form_regularity U hU hline V e c
        (IsManifold.subset_maximalAtlas hc) θ hθ
      have hθd := (hreg.1.differentiableOn (by simp) z hz).differentiableAt
        ((c.isOpen_inter_preimage_symm V.isOpen).mem_nhds hz)
      have hcm : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
        IsManifold.subset_maximalAtlas hc
      have hrm : c ∈ IsManifold.maximalAtlas (realModel d) ∞ X :=
        IsManifold.subset_maximalAtlas hc
      have hrm1 : c ∈ IsManifold.maximalAtlas (realModel d) 1 X :=
        IsManifold.subset_maximalAtlas hc
      have hi : (mfderiv (realModel d) (realModel d) c.symm z).IsInvertible := by
        have h := isInvertible_mfderivWithin_extend_symm (I := realModel d) hrm1
          (y := z) (by simpa using hz.1)
        simpa using h
      have hder : mfderiv (realModel d) (realModel d) c.symm z =
          (mfderiv (complexModel d) (complexModel d) c.symm z).restrictScalars ℝ := by
        have hf := (contMDiffAt_symm_of_mem_maximalAtlas hcm hz.1).mdifferentiableAt (by simp)
        have hr := (contMDiffAt_symm_of_mem_maximalAtlas hrm hz.1).mdifferentiableAt (by simp)
        ext v
        apply (tangentSpaceCastModel (realModel d) (c.symm z)).injective
        rw [hf.mfderiv_abuse, hr.mfderiv_abuse]
        have hd := hf.differentiableWithinAt_writtenInExtChartAt
        change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel d) z c.symm)
          (range (complexModel d)) (extChartAt (complexModel d) z z)) v =
          (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel d) z c.symm)
          (range (complexModel d)) (extChartAt (complexModel d) z z)) v
        exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
      have hAI (v : ComplexModel d) :
          QuotientLineConnection.coordinateForm nabla e c z (Complex.I • v) =
            Complex.I * QuotientLineConnection.coordinateForm nabla e c z v := by
        change nabla.form V e (c.symm z)
          (mfderiv (realModel d) (realModel d) c.symm z (Complex.I • v)) =
          Complex.I * nabla.form V e (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z v)
        rw [hder]
        change nabla.form V e (c.symm z)
          (complexTangentToReal d (c.symm z)
            (mfderiv (complexModel d) (complexModel d) c.symm z (Complex.I • v))) =
          Complex.I * nabla.form V e (c.symm z)
            (complexTangentToReal d (c.symm z)
              (mfderiv (complexModel d) (complexModel d) c.symm z v))
        rw [map_smul]
        exact hcompatible.1 V e (c.symm z) hz.2 _
      apply coordinate_exterior_rank_one θ (QuotientLineConnection.coordinateForm nabla e c z)
        hθd hAI
      intro v hv w
      let D : ComplexModel d →L[ℂ] TangentSpace (complexModel d) (c.symm z) :=
        (mfderiv (complexModel d) (complexModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap
      have hvU : D v ∈ U (c.symm z) := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        apply (e.coordinate (c.symm z) hz.2).injective
        rw [map_zero]
        change e.coordinate (c.symm z) hz.2
          (QuotientLineConnection.projection U (c.symm z) (D v)) = 0
        exact (hθ z hz v).symm.trans hv
      obtain ⟨W, Y, Z, hxW, hWV, hYx, hZx, hYhol, hZhol, hYU⟩ :=
        holomorphic_tangent_field_extension U hU V (c.symm z) hz.2 (D v) (D w) hvU
      obtain ⟨eW, hsection, hform⟩ := holomorphic_frame_restriction nabla e
        (show (W : Set X) ⊆ V from hWV)
      have hcoordinate (y : X) (hy : y ∈ W) (q : QuotientLineConnection.Fibre U y) :
          eW.coordinate y hy q = e.coordinate y (hWV hy) q := by
        have hq : q = e.coordinate y (hWV hy) q • e.sectionValue y := by
          apply (e.coordinate y (hWV hy)).injective
          rw [map_smul, e.normalized, smul_eq_mul, mul_one]
        calc
          eW.coordinate y hy q = eW.coordinate y hy
              (e.coordinate y (hWV hy) q • e.sectionValue y) := congrArg _ hq
          _ = e.coordinate y (hWV hy) q := by
            rw [← congrFun hsection y, map_smul, eW.normalized, smul_eq_mul, mul_one]
      have hθW : ∀ b (hb : b ∈ c.target ∩ c.symm ⁻¹' (W : Set X)), ∀ t : ComplexModel d,
          θ b t = eW.coordinate (c.symm b) hb.2
            (QuotientLineConnection.projection U (c.symm b)
              (mfderiv (complexModel d) (complexModel d) c.symm b
                ((NormedSpace.fromTangentSpace b).symm t))) := by
        intro b hb t
        rw [hcoordinate]
        exact hθ b ⟨hb.1, hWV hb.2⟩ t
      have hY := ConnectionCalculus.smoothTangentField_of_holomorphic W.isOpen hYhol
      have hZ := ConnectionCalculus.smoothTangentField_of_holomorphic W.isOpen hZhol
      have hIY := ConnectionCalculus.smoothTangentField_of_holomorphic W.isOpen
        (hYhol.const_smul_section (a := Complex.I))
      have hIZ := ConnectionCalculus.smoothTangentField_of_holomorphic W.isOpen
        (hZhol.const_smul_section (a := Complex.I))
      have hcancel := hBott U nabla hcompatible W eW c hc θ hθW ⟨hz.1, hxW⟩
        hθd Y Z hY hZ hIY hIZ hYU
      have hpullY : VectorField.mpullback (realModel d) (realModel d) c.symm
          (fun y ↦ complexTangentToReal d y (Y y)) z = v := by
        apply hi.inverse_apply_eq.mpr
        change complexTangentToReal d (c.symm z) (Y (c.symm z)) =
          mfderiv (realModel d) (realModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm v)
        rw [hYx, hder]
        rfl
      have hpullZ : VectorField.mpullback (realModel d) (realModel d) c.symm
          (fun y ↦ complexTangentToReal d y (Z y)) z = w := by
        apply hi.inverse_apply_eq.mpr
        change complexTangentToReal d (c.symm z) (Z (c.symm z)) =
          mfderiv (realModel d) (realModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm w)
        rw [hZx, hder]
        rfl
      have hAeq : QuotientLineConnection.coordinateForm nabla eW c z =
          QuotientLineConnection.coordinateForm nabla e c z := by
        unfold QuotientLineConnection.coordinateForm
        rw [hform (c.symm z) hxW]
      dsimp only at hcancel
      rw [hpullY, hpullZ, hAeq] at hcancel
      exact hcancel
    let α : (y : X) → TangentSpace (complexModel d) y →L[ℂ] ℂ := fun y ↦
      if hy : y ∈ V then
        ((e.coordinate y hy).toLinearMap.comp (U y).mkQ).toContinuousLinearMap
      else 0
    have hα (y : X) (hy : y ∈ V) (v : TangentSpace (complexModel d) y) :
        α y v = e.coordinate y hy (QuotientLineConnection.projection U y v) := by
      simp only [α, dite_eq_left hy]
      rfl
    let c := chartAt (ComplexModel d) x
    have hc : c ∈ atlas (ComplexModel d) X := chart_mem_atlas _ _
    have hxc : x ∈ c.source := mem_chart_source _ _
    let θ : ComplexModel d → ComplexModel d →L[ℂ] ℂ := fun z ↦
      (α (c.symm z)).comp ((mfderiv (complexModel d) (complexModel d) c.symm z).comp
        (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)
    have hθ : ∀ z (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X)), ∀ v : ComplexModel d,
        θ z v = e.coordinate (c.symm z) hz.2
          (QuotientLineConnection.projection U (c.symm z)
            (mfderiv (complexModel d) (complexModel d) c.symm z
              ((NormedSpace.fromTangentSpace z).symm v))) := by
      intro z hz v
      exact hα (c.symm z) hz.2 _
    have hreg := quotient_coordinate_form_regularity U hU hline V e c
      (IsManifold.subset_maximalAtlas hc) θ hθ
    have hcx : c x ∈ c.target ∩ c.symm ⁻¹' (V : Set X) := by
      refine ⟨c.map_source hxc, ?_⟩
      change c.symm (c x) ∈ V
      rwa [c.left_inv hxc]
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
      (c.isOpen_inter_preimage_symm V.isOpen) (c x) hcx
    let B := Metric.ball (c x) ε
    have hclosed (z : ComplexModel d) (hz : z ∈ B) (v w : ComplexModel d) :
        fderiv ℝ θ z v w = fderiv ℝ θ z w v := by
      have h := hclosure U hU hline nabla hcompatible V e c hc θ hθ (hball hz) v w
      have hAz : QuotientLineConnection.coordinateForm nabla e c z = 0 := by
        unfold QuotientLineConnection.coordinateForm
        rw [hzero (c.symm z) (hball hz).2]
        simp
      simpa only [hAz, zero_apply, zero_mul, add_zero, sub_zero,
        sub_eq_zero] using h
    have hprim := closed_coordinate_form_primitive α c (IsManifold.subset_maximalAtlas hc)
      B Metric.isOpen_ball (convex_ball (c x) ε) (fun _ hz ↦ (hball hz).1)
      (c x) (Metric.mem_ball_self hε) θ (fun _ _ _ ↦ rfl)
      (hreg.2.mono hball) hclosed
    let W : Opens X := ⟨c.source ∩ c ⁻¹' B, c.isOpen_inter_preimage Metric.isOpen_ball⟩
    have hWV : W ≤ V := by
      intro y hy
      have hv := (hball hy.2).2
      change c.symm (c y) ∈ V at hv
      rwa [c.left_inv hy.1] at hv
    let t : X → ℂ := fun y ↦ curveIntegral θ (Path.segment (c x) (c y))
    refine ⟨W, ⟨hxc, Metric.mem_ball_self hε⟩, hWV, t, hprim.1, ?_⟩
    intro y hy
    have hσ : e.sectionValue y ≠ 0 := by
      intro he
      have hn := e.normalized y (hWV hy)
      rw [he, map_zero] at hn
      exact zero_ne_one hn
    have hformula (v : TangentSpace (complexModel d) y) :
        QuotientLineConnection.projection U y v =
          transverseScalarDifferential t y v • e.sectionValue y := by
      apply (e.coordinate y (hWV hy)).injective
      rw [map_smul, e.normalized, smul_eq_mul, mul_one]
      change e.coordinate y (hWV hy) (QuotientLineConnection.projection U y v) =
        tangentSpaceCastModel 𝓘(ℂ, ℂ) (t y) (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t y v)
      rw [hprim.2 y hy v]
      exact (hα y (hWV hy) v).symm
    exact ⟨hformula, (differential_quotient_data U t y (e.sectionValue y) hσ hformula).1,
      mfderiv_surjective_of_quotient_formula U t y (e.sectionValue y) hσ hformula⟩
  have hframe
      {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
      [IsManifold (complexModel d) ∞ X]
      {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
      (nabla : QuotientLineConnection.Connection U)
      (hflat : QuotientLineConnection.IsFlat nabla)
      (hhol : QuotientLineConnection.IsHolomorphic nabla)
      (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
      (x : X) (hx : x ∈ V) :
      ∃ W : Opens X, x ∈ W ∧ (W : Set X) ⊆ V ∧
        ∃ eW : QuotientLineConnection.HolomorphicFrame U W,
          (∀ y ∈ W, nabla.form W eW y = 0) ∧
          (∀ y ∈ W, eW.sectionValue y ≠ 0) ∧
          QuotientLineConnection.IsParallelOn nabla W eW.sectionValue := by
    have hfactor :
      ∃ W : Opens X, x ∈ W ∧ (W : Set X) ⊆ V ∧ ∃ g : X → ℂ,
        ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ g W ∧
        (∀ y ∈ W, g y ≠ 0) ∧
        ∀ y ∈ W, QuotientLineConnection.realDifferential (d := d) g y =
          -(g y) • nabla.form V e y := by
      let c := chartAt (ComplexModel d) x
      have hc : c ∈ atlas (ComplexModel d) X := chart_mem_atlas _ _
      have hxc : x ∈ c.source := mem_chart_source _ _
      obtain ⟨r, hr, hball, hP⟩ := flat_coordinate_integrating_factor nabla hflat V e c
        (IsManifold.subset_maximalAtlas hc) x hxc hx
      let W : Opens X := ⟨c.source ∩ c ⁻¹' Metric.ball (c x) r,
        c.isOpen_inter_preimage Metric.isOpen_ball⟩
      let P := fun z ↦ curveIntegral (QuotientLineConnection.coordinateForm nabla e c)
        (Path.segment (c x) z)
      let g := fun z ↦ Complex.exp (-P z)
      refine ⟨W, ⟨hxc, Metric.mem_ball_self hr⟩, ?_, g ∘ c, ?_, ?_, ?_⟩
      · intro y hy
        have hv := (hball hy.2).2
        change c.symm (c y) ∈ V at hv
        rwa [c.left_inv hy.1] at hv
      · have hgd : DifferentiableOn ℂ g (Metric.ball (c x) r) := by
          intro z hz
          exact (coordinate_integrating_factor_differentiable nabla hhol V e c hc g z
            (hball hz).1 (hball hz).2 (hP z hz).2.2).differentiableWithinAt
        have hGd : DifferentiableOn ℂ (fun z : ComplexModel d ↦ (fun _ : Fin 1 ↦ g z))
            (Metric.ball (c x) r) := by
          exact differentiableOn_pi.2 (fun _ ↦ hgd)
        have hGs := (complex_contDiffOn_iff_differentiableOn Metric.isOpen_ball).2 hGd
        have hgs : ContDiffOn ℂ ∞ g (Metric.ball (c x) r) := (contDiffOn_pi.1 hGs) 0
        exact hgs.contMDiffOn.comp
          ((contMDiffOn_of_mem_maximalAtlas
            (IsManifold.subset_maximalAtlas (I := complexModel d) (n := ∞) hc)).mono
              (fun y hy ↦ hy.1)) (fun y hy ↦ hy.2)
      · intro y hy
        exact (hP (c y) hy.2).2.1
      · intro y hy
        exact coordinate_integrating_factor_pullback nabla V e c hc g y hy.1
          (hP (c y) hy.2).2.2
    obtain ⟨W, hxW, hWV, g, hg, hgnz, hdg⟩ := hfactor
    obtain ⟨eR, heR, hform⟩ := holomorphic_frame_restriction nabla e hWV
    obtain ⟨eW, heW, hzero, hparallel⟩ :=
      exists_parallel_frame_of_integrating_factor nabla eR g hg hgnz (by
        intro y hy
        rw [hform y hy]
        exact hdg y hy)
    refine ⟨W, hxW, hWV, eW, hzero, ?_, hparallel⟩
    intro y hy hzero
    have h := eW.normalized y hy
    rw [hzero, map_zero] at h
    exact zero_ne_one h
  
  
  
  obtain ⟨hUh, hconnection⟩ := lemma_2_3_connection_holomorphic_flat hd f a hstable U hunstable
  obtain ⟨hhol, hflat⟩ := hconnection hU nabla hcontinuous hcompatible hinvariant
  have hline : IsQuotientTangentLine U := by
    intro x
    obtain ⟨O, s, hxO, hs, hspan⟩ := hUh x
    have hr : Module.finrank ℂ (U x) = d - 1 := by
      rw [← hspan x hxO, finrank_span_eq_card (hs.2.2 x hxO)]
      simp
    have hdim := (U x).finrank_quotient_add_finrank
    rw [hr] at hdim
    have hdX : Module.finrank ℂ (TangentSpace (complexModel d) x) = d :=
      (Module.finrank_pi ℂ).trans (Fintype.card_fin d)
    rw [hdX] at hdim
    change Module.finrank ℂ (TangentSpace (complexModel d) x ⧸ U x) = 1
    omega
  intro x
  obtain ⟨V, hxV, ⟨e⟩⟩ := ConnectionCalculus.holomorphic_frame_cover U hUh hline x
  obtain ⟨O, hxO, hOV, eO, hzero, hnz, hparallel⟩ :=
    hframe nabla hflat hhol V e x hxV
  obtain ⟨W, hxW, hWO, t, ht, hformula⟩ :=
    hprimitive U hUh hline nabla hcompatible O eO hzero x hxO
  refine ⟨W, hxW, eO.sectionValue, t, ?_, (fun y hy ↦ hnz y (hWO hy)), ?_, ht,
    (fun y hy ↦ holomorphic_scalar_submersion_of_surjective t W ht y hy
      (hformula y hy).2.2), fun y hy ↦ ⟨(hformula y hy).1, (hformula y hy).2.1⟩⟩
  · intro y hy
    obtain ⟨S, Z, hSo, hyS, hSO, hZ, hZeq⟩ := eO.holomorphic y (hWO hy)
    exact ⟨S ∩ W, Z, hSo.inter W.isOpen, ⟨hyS, hy⟩, inter_subset_right,
      hZ.mono inter_subset_left, fun z hz ↦ hZeq z hz.1⟩
  · intro Q eQ y hyQ hyW v
    exact hparallel Q eQ y hyQ (hWO hyW) v
end HolomorphicAnosov.Paper.Zhang

