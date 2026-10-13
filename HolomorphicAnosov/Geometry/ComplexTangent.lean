import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv


/-!
# Complex tangent fibres as real tangent fibres

This file identifies complex and real tangent fibres by restricting scalars and proves continuity of the induced total-space maps. (Demailly, §3.C; Ghys, §2)
-/

universe u

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology
open Bundle


noncomputable section

/-- Restricting scalars gives the canonical real module underlying a complex tangent fibre. (Demailly, §3.C; Ghys, §2) -/
instance complexTangentRealModule (d : ℕ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X) :
    Module ℝ (TangentSpace (complexModel d) x) :=
  Module.restrictScalars ℝ ℂ (TangentSpace (complexModel d) x)

/-- The restricted real action agrees with the complex tangent action. (Demailly, §3.C) -/
instance complexTangentScalarTower (d : ℕ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X) :
    IsScalarTower ℝ ℂ (TangentSpace (complexModel d) x) :=
  IsScalarTower.restrictScalars ℝ ℂ (TangentSpace (complexModel d) x)

/-- The complex and real tangent fibres are identified in their common preferred chart. (Demailly, §3.C; Ghys, §2) -/
def complexTangentToReal (d : ℕ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X] (x : X) :
    TangentSpace (complexModel d) x ≃L[ℝ] TangentSpace (realModel d) x :=
  let e := tangentSpaceCastModel (complexModel d) x
  let eReal : TangentSpace (complexModel d) x ≃L[ℝ] ComplexModel d :=
    { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  eReal.trans (tangentSpaceCastModel (realModel d) x).symm

section BundleRealification
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
attribute [local instance] complex_isManifold_real

/-- The tangent transition derivative commutes with scalar restriction. (Demailly, §3.C) -/
theorem complexTangentCoordChange_restrictScalars (x y z : X)
    (h : z ∈ (extChartAt (complexModel d) x).source ∩
      (extChartAt (complexModel d) y).source) :
    tangentCoordChange (realModel d) x y z =
      (tangentCoordChange (complexModel d) x y z).restrictScalars ℝ := by
  have hf := hasFDerivWithinAt_tangentCoordChange (I := complexModel d) h
  have he := (hf.restrictScalars ℝ).fderivWithin
    (show UniqueDiffWithinAt ℝ (Set.range (complexModel d))
      (extChartAt (complexModel d) x z) by simp)
  exact he

/-- Realification preserves the local tangent coordinates of the original bundle. (Demailly, §3.C) -/
theorem complexTangentToReal_coordinates (x : X) (z : TangentBundle (complexModel d) X)
    (h : z.proj ∈ (chartAt (ComplexModel d) x).source) :
    (trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
      ⟨z.proj, complexTangentToReal d z.proj z.snd⟩).2 =
    (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x z).2 := by
  change tangentCoordChange (realModel d) z.proj x z.proj z.snd =
    tangentCoordChange (complexModel d) z.proj x z.proj z.snd
  rw [complexTangentCoordChange_restrictScalars z.proj x z.proj
    ⟨mem_extChartAt_source (I := complexModel d) z.proj,
      by simpa only [extChartAt_source] using h⟩]
  rfl

/-- The forward realification is continuous on the native tangent total spaces. (Demailly, §3.C) -/
theorem continuous_complexTangentToReal :
    Continuous (fun z : TangentBundle (complexModel d) X ↦
      (⟨z.proj, complexTangentToReal d z.proj z.snd⟩ : TangentBundle (realModel d) X)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply (FiberBundle.continuousAt_totalSpace (ComplexModel d) _).mpr
  refine ⟨(FiberBundle.continuous_proj (ComplexModel d)
    (TangentSpace (complexModel d))).continuousAt, ?_⟩
  have hc := ((FiberBundle.continuousAt_totalSpace (ComplexModel d)
    (fun z : TangentBundle (complexModel d) X ↦ z) (x₀ := z)).mp continuousAt_id).2
  apply hc.congr_of_eventuallyEq
  filter_upwards [(FiberBundle.continuous_proj (ComplexModel d)
    (TangentSpace (complexModel d))).continuousAt.eventually
    (((chartAt (ComplexModel d) z.proj).open_source).mem_nhds
      (mem_chart_source _ _))] with t ht
  exact complexTangentToReal_coordinates z.proj t ht

/-- The inverse realification has the same tangent coordinates. (Demailly, §3.C) -/
theorem complexTangentToReal_symm_coordinates (x : X) (z : TangentBundle (realModel d) X)
    (h : z.proj ∈ (chartAt (ComplexModel d) x).source) :
    (trivializationAt (ComplexModel d) (TangentSpace (complexModel d)) x
      ⟨z.proj, (complexTangentToReal d z.proj).symm z.snd⟩).2 =
    (trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x z).2 := by
  change tangentCoordChange (complexModel d) z.proj x z.proj z.snd =
    tangentCoordChange (realModel d) z.proj x z.proj z.snd
  rw [complexTangentCoordChange_restrictScalars z.proj x z.proj
    ⟨mem_extChartAt_source (I := complexModel d) z.proj,
      by simpa only [extChartAt_source] using h⟩]
  rfl

/-- The inverse total-space realification is continuous. (Demailly, §3.C) -/
theorem continuous_complexTangentToReal_symm :
    Continuous (fun z : TangentBundle (realModel d) X ↦
      (⟨z.proj, (complexTangentToReal d z.proj).symm z.snd⟩ :
        TangentBundle (complexModel d) X)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply (FiberBundle.continuousAt_totalSpace (ComplexModel d) _).mpr
  refine ⟨(FiberBundle.continuous_proj (ComplexModel d)
    (TangentSpace (realModel d))).continuousAt, ?_⟩
  have hc := ((FiberBundle.continuousAt_totalSpace (ComplexModel d)
    (fun z : TangentBundle (realModel d) X ↦ z) (x₀ := z)).mp continuousAt_id).2
  apply hc.congr_of_eventuallyEq
  filter_upwards [(FiberBundle.continuous_proj (ComplexModel d)
    (TangentSpace (realModel d))).continuousAt.eventually
    (((chartAt (ComplexModel d) z.proj).open_source).mem_nhds
      (mem_chart_source _ _))] with t ht
  exact complexTangentToReal_symm_coordinates z.proj t ht

end BundleRealification

end

end HolomorphicAnosov
