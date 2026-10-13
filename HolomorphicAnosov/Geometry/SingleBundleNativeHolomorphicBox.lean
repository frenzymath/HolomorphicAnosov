import HolomorphicAnosov.Geometry.OriginalNativeLiftedHolomorphicFoliations
import HolomorphicAnosov.Geometry.ComplementaryComplexFrame

namespace HolomorphicAnosov.Theorem12NativeHolomorphicBoxes

open Set Filter
open scoped Topology _root_.Topology ContDiff Manifold
open Theorem12FrobeniusLocalAssembly
attribute [local instance] complex_isManifold_real

variable {d : ℕ} {X : Type*} [MetricSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- A single holomorphic bundle together with its native real leaves supplies a codimension-one holomorphic unit box. The transverse direction is selected by finite-dimensional complement at the base point; no holomorphic complementary bundle or transverse native leaf is assumed. -/
theorem exists_native_single_bundle_holomorphic_unit_box
    (hd : 1 ≤ d)
    (f : X ≃ₜ X)
    (P : (q : X) → Submodule ℂ (TangentSpace (complexModel d) q))
    (hP : IsHolomorphicTangentSubbundle (d - 1) P)
    (Q : RealTangentDistribution (realModel d) X)
    (hReal : ∀ q, ((P q).restrictScalars ℝ).map
      (complexTangentToReal d q).toLinearEquiv.toLinearMap = Q q)
    (D : ∀ b, NativeAsymptoticLeafDatum (realModel d) f Q b) (x : X) :
    ∃ b : OpenPartialHomeomorph X (ComplexModel (d - 1) × ComplexModel 1),
      x ∈ b.source ∧
      b.target = (complexFoliationDisk (d - 1) : Set (ComplexModel (d - 1))) ×ˢ
        (complexFoliationDisk 1 : Set (ComplexModel 1)) ∧
      ContMDiffOn (complexModel d) 𝓘(ℂ, ComplexModel (d - 1) × ComplexModel 1) ∞
        b b.source ∧
      ContMDiffOn 𝓘(ℂ, ComplexModel (d - 1) × ComplexModel 1) (complexModel d) ∞
        b.symm b.target ∧
      (∀ q ∈ b.source,
        (P q).map (mfderiv (complexModel d)
          𝓘(ℂ, ComplexModel (d - 1) × ComplexModel 1) b q).toLinearMap =
          LinearMap.range
            (ContinuousLinearMap.inl ℂ (ComplexModel (d - 1)) (ComplexModel 1)).toLinearMap) := by
  obtain ⟨V, p, N, hV, hxV, hVt, hN, hrange, hproj, hinj, hcommute⟩ :=
    Theorem12FrobeniusLocalAssembly.exists_native_commuting_frame f P hP Q hReal D x
  let k := chartAt (ComplexModel d) x
  let N₀ := N (k x)
  obtain ⟨A, hAinj, hAcompl⟩ :=
    SingleBundleHolomorphicBox.exists_complementary_frame (d := d) (r := d - 1) (c := 1)
      (Nat.sub_add_cancel hd).symm N₀ (hinj _ hxV)
  obtain ⟨flow, domain, hopen, hmem, hsmooth, hzero, hrangeFlow, hODE, hpreserve⟩ :=
    Theorem12NativeHolomorphicBoxes.exists_preserving_complex_frame_flows
      V hV (k x) hxV N hN hcommute
  obtain ⟨b, hxb, hsource, htarget, hb, hbi, hflat⟩ :=
    Theorem12FrobeniusLocalAssembly.exists_unit_box_from_native_flow_data P k
      (contMDiffOn_chart (n := ∞) (I := complexModel d))
      (contMDiffOn_chart_symm (n := ∞) (I := complexModel d) (x := x))
      x (mem_chart_source (ComplexModel d) x) V hV hxV N hrange A
      (hinj _ hxV) hAinj hAcompl flow domain hopen hmem hsmooth hzero hODE hpreserve
  exact ⟨b, hxb, htarget, hb, hbi, hflat⟩

end HolomorphicAnosov.Theorem12NativeHolomorphicBoxes
