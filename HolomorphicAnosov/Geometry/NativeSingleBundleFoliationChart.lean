import HolomorphicAnosov.Geometry.SingleBundleNativeHolomorphicBox
import HolomorphicAnosov.Geometry.FoliationChartOfHolomorphicBox

open Set Filter
open scoped ContDiff Manifold
namespace HolomorphicAnosov.SingleBundleHolomorphicBox
noncomputable section
attribute [local instance] complex_isManifold_real

theorem foliation_chart_of_box_eq {d r : ℕ} (hdim : d = r + 1) {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (b : OpenPartialHomeomorph X (ComplexModel r × ComplexModel 1))
    (hb : ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel 1)
      ∞ b b.source)
    (hbi : ContMDiffOn 𝓘(ℂ, ComplexModel r × ComplexModel 1)
      (complexModel d) ∞ b.symm b.target)
    (hflat : ∀ y ∈ b.source, (P y).map
      (mfderiv (complexModel d) 𝓘(ℂ, ComplexModel r × ComplexModel 1) b y).toLinearMap =
        LinearMap.range (ContinuousLinearMap.inl ℂ (ComplexModel r) (ComplexModel 1)).toLinearMap) :
    ∃ c : OpenPartialHomeomorph X (ComplexModel d),
      c.source = b.source ∧ c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X ∧
      ∀ x ∈ c.source, P x = LinearMap.ker
        (((ContinuousLinearMap.proj (⟨0, by omega⟩ : Fin d)).comp
          ((tangentSpaceCastModel (complexModel d) (c x)).toContinuousLinearMap.comp
            (mfderiv (complexModel d) (complexModel d) c x))).toLinearMap) := by
  subst d
  simpa using foliation_chart_of_box P b hb hbi hflat

/-- A rank `d − 1` holomorphic tangent bundle with native real leaves admits a foliation chart in
the maximal atlas with a one-dimensional transverse frame. -/
theorem exists_native_single_bundle_foliation_chart
    {d : ℕ} {X : Type*} [MetricSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (hd : 1 ≤ d)
    (f : X ≃ₜ X)
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle (d - 1) P)
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (D : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b) (x : X) :
    ∃ b : OpenPartialHomeomorph X (ComplexModel (d - 1) × ComplexModel 1),
      ∃ c : OpenPartialHomeomorph X (ComplexModel d),
        x ∈ b.source ∧ c.source = b.source ∧
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X ∧
        (∀ y ∈ c.source, P y = LinearMap.ker
          (((ContinuousLinearMap.proj (⟨0, by omega⟩ : Fin d)).comp
            ((tangentSpaceCastModel (complexModel d) (c y)).toContinuousLinearMap.comp
              (mfderiv (complexModel d) (complexModel d) c y))).toLinearMap)) := by
  obtain ⟨b, hxb, htarget, hb, hbi, hflat⟩ :=
    Theorem12NativeHolomorphicBoxes.exists_native_single_bundle_holomorphic_unit_box
      hd f P hP Q hReal D x
  obtain ⟨c, hcsource, hcatlas, hker⟩ :=
    foliation_chart_of_box_eq (Nat.sub_add_cancel hd).symm P b hb hbi hflat
  exact ⟨b, c, hxb, hcsource, hcatlas, hker⟩

end
end HolomorphicAnosov.SingleBundleHolomorphicBox

