import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Paper.Zhang.HolomorphicTangentFieldSmooth
import HolomorphicAnosov.Geometry.Manifold.VectorField.ImmersionMLieBracketTangent

open Set TopologicalSpace Filter
open scoped Topology _root_.Topology Bundle
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov

/-- The unstable distribution of a holomorphic Anosov diffeomorphism is involutive for the complex
Bott bracket. (Zhang, §2.1, p.4, equation (2) and Definition 2.1; Lee, Prop. 4.16, p.92, Prop.
8.27 and Cor. 8.28, pp.192–193, and Prop. 19.3, p.497) -/
theorem unstable_bott_involutive
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hUreal : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (V : Opens X) (Y Z : (x : X) → TangentSpace (complexModel d) x)
    (hY : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun x ↦ (⟨x, Y x⟩ : TangentBundle (complexModel d) X)) V)
    (hZ : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
      (fun x ↦ (⟨x, Z x⟩ : TangentBundle (complexModel d) X)) V)
    (hYU : ∀ x ∈ V, Y x ∈ U x) (hZU : ∀ x ∈ V, Z x ∈ U x) :
    ∀ x ∈ V, QuotientLineConnection.bottBracket Y Z x ∈ U x := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C, rate, hC, hr, hr1, hs, hu⟩ := fixed_block_uniform_anosov_estimates f a
  have hi (x : X) (v w : TangentSpace (realModel d) x) :
      inner ℝ v w = a.metric.inner x v w := rfl
  have hb : Nonempty (TensorAnosovBounds f.toReal a.splitting a.metric) := by
    refine ⟨⟨C, rate, hC, hr, hr1, ?_, ?_⟩⟩
    · intro n x v hv
      have he : (realIterate (realModel d) f.toReal n : X → X) = (f : X → X)^[n] := rfl
      rw [he]
      simpa only [norm_eq_sqrt_real_inner, hi] using hs n x v hv
    · intro n x v hv
      have he : (realIterate (realModel d) f.toReal.symm n : X → X) =
          (f.symm : X → X)^[n] := rfl
      rw [he]
      simpa only [norm_eq_sqrt_real_inner, hi] using hu n x v hv
  obtain ⟨_, hlu⟩ := HPS.anosov_global_lamination_tensor f.toReal a.splitting a.metric hb
  obtain ⟨ι, L, rank, top, charts, smooth, F, _⟩ := hlu
  let := top
  let := charts
  let := smooth
  have hbr (Y' Z' : (x : X) → TangentSpace (complexModel d) x)
      (hy : QuotientLineConnection.IsSmoothTangentField V Y')
      (hz : QuotientLineConnection.IsSmoothTangentField V Z')
      (hyU : ∀ x ∈ V, Y' x ∈ U x) (hzU : ∀ x ∈ V, Z' x ∈ U x)
      (x : X) (hx : x ∈ V) :
      VectorField.mlieBracket (realModel d)
        (fun y ↦ complexTangentToReal d y (Y' y))
        (fun y ↦ complexTangentToReal d y (Z' y)) x ∈
          a.splitting.unstable.toDistribution x := by
    obtain ⟨j, z, hzval⟩ := F.cover x
    subst x
    apply Theorem12NativePlaque.immersion_mlieBracket_tangent
      ((F.leaf j).immersion.isImmersionAt z) a.splitting.unstable.toDistribution (F.leaf j).tangent
    · exact ((hy _ hx).contMDiffAt (V.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
    · exact ((hz _ hx).contMDiffAt (V.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
    · have hopen := ((F.leaf j).immersion.contMDiff.continuous.tendsto z).eventually
        (V.isOpen.mem_nhds hx)
      filter_upwards [hopen] with y hy
      rw [← hUreal]
      exact ⟨Y' _, hyU _ hy, rfl⟩
    · have hopen := ((F.leaf j).immersion.contMDiff.continuous.tendsto z).eventually
        (V.isOpen.mem_nhds hx)
      filter_upwards [hopen] with y hy
      rw [← hUreal]
      exact ⟨Z' _, hzU _ hy, rfl⟩
  intro x hx
  have hb1 := hbr Y Z (holomorphic_tangent_field_smooth hY)
    (holomorphic_tangent_field_smooth hZ) hYU hZU x hx
  have hb2 := hbr (fun y ↦ Complex.I • Y y) (fun y ↦ Complex.I • Z y)
    (holomorphic_tangent_field_smooth (hY.const_smul_section (a := Complex.I)))
    (holomorphic_tangent_field_smooth (hZ.const_smul_section (a := Complex.I)))
    (fun y hy ↦ (U y).smul_mem _ (hYU y hy))
    (fun y hy ↦ (U y).smul_mem _ (hZU y hy)) x hx
  have hdiff := (a.splitting.unstable.toDistribution x).sub_mem hb1 hb2
  rw [← hUreal] at hdiff
  obtain ⟨w, hw, he⟩ := hdiff
  unfold QuotientLineConnection.bottBracket
  rw [← he]
  change (1 / 2 : ℂ) • (complexTangentToReal d x).symm (complexTangentToReal d x w) ∈ U x
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact (U x).smul_mem _ hw

end HolomorphicAnosov

