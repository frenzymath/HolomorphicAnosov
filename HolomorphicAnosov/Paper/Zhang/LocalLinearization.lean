import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine
import HolomorphicAnosov.Paper.Zhang.InvariantConnection
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import HolomorphicAnosov.Paper.Zhang.UniformLocalStableCoordinates
import HolomorphicAnosov.Paper.Zhang.TranslationInvariantComplexTorusDescent
import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinate
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.InvariantParallelScaleDerivativeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.QuotientDerivativeSurjective
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ImageFrameCoefficientNeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ParallelImageCoefficientDerivativeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ImageCoefficientLocallyHolomorphic
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.TransverseDifferentialTransport
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ExistsFrameOfTransversePair
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ComplexScalarRealSmooth
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.FrameSelfCoefficientDerivativeZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ScalarLocallyConstantOfRealDifferentialZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ScalarLocallyConstantOfComplexDifferentialZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.StableCoordinateDerivativeInvertible
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ComplexStableDerivativeImage
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.ParallelFrameFormZero
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.OriginalMapLocallyAffine

/-! Normalized stable coordinates locally conjugate the Anosov map to its derivative on the stable
tangent line. (Zhang, Lemma 2.6, p.8, equations (16)–(17)) -/

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

set_option linter.unusedVariables false in
/-- For a compatible continuous invariant quotient-line connection, normalized stable coordinates
intertwine the Anosov map with its stable derivative near each leaf point. (Zhang, Lemma 2.6,
p.8, equations (16)–(17)) -/
theorem local_linearization
    {d : ℕ} (hd : 3 ≤ d) (X : Type u)
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (S : ContinuousComplexTangentSubbundle (complexModel d) X)
    (hS : ∀ x, ((S.toDistribution x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.stable.toDistribution x)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hunstable : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (nabla : QuotientLineConnection.Connection U)
    (hcontinuous : QuotientLineConnection.IsContinuous nabla)
    (hcompatible : QuotientLineConnection.IsCompatible nabla)
    (hinvariant : QuotientLineConnection.IsInvariant nabla f hU)
    (ι : Type u) (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    (F : HPS.LeafPartition a.splitting.stable.toDistribution ι L (fun _ ↦ 2))
    (V W : TopologicalSpace.Opens X)
    (σ σ' : (x : X) → QuotientLineConnection.Fibre U x) (t t' : X → ℂ)
    (hσhol : QuotientLineConnection.IsHolomorphicSection U V σ)
    (hσ'hol : QuotientLineConnection.IsHolomorphicSection U W σ')
    (hσnonzero : ∀ x ∈ V, σ x ≠ 0) (hσ'nonzero : ∀ x ∈ W, σ' x ≠ 0)
    (hσparallel : QuotientLineConnection.IsParallelOn nabla V σ)
    (hσ'parallel : QuotientLineConnection.IsParallelOn nabla W σ')
    (hthol : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (ht'hol : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t' W)
    (htsub : ∀ x ∈ V, Manifold.IsSubmersionAt (complexModel d) 𝓘(ℂ, ℂ) ∞ t x)
    (ht'sub : ∀ x ∈ W, Manifold.IsSubmersionAt (complexModel d) 𝓘(ℂ, ℂ) ∞ t' x)
    (htker : ∀ x ∈ V, ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t x)).toContinuousLinearMap.comp
      (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t x)).ker = U x)
    (ht'ker : ∀ x ∈ W, ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t' x)).toContinuousLinearMap.comp
      (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t' x)).ker = U x)
    (hπ : ∀ x ∈ V, ∀ v : TangentSpace (complexModel d) x,
      QuotientLineConnection.projection U x v =
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t x)).toContinuousLinearMap.comp
          (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t x)) v • σ x)
    (hπ' : ∀ x ∈ W, ∀ v : TangentSpace (complexModel d) x,
      QuotientLineConnection.projection U x v =
        ((tangentSpaceCastModel 𝓘(ℂ, ℂ) (t' x)).toContinuousLinearMap.comp
          (mfderiv (complexModel d) 𝓘(ℂ, ℂ) t' x)) v • σ' x) :
    ∀ (i : ι) (z : L i),
      let x := (F.leaf i).inclusion z
      x ∈ V → f x ∈ W → ∀ᶠ p in 𝓝 z,
        (F.leaf i).inclusion p ∈ V ∧
        f ((F.leaf i).inclusion p) ∈ W ∧
        (normalizedLocalStableCoordinate S.toDistribution t' (f x)
          (f ((F.leaf i).inclusion p))).val =
          mfderiv (complexModel d) (complexModel d) f x
            (normalizedLocalStableCoordinate S.toDistribution t x
              ((F.leaf i).inclusion p)).val := by
  intro i z
  dsimp only
  intro hx hfx
  let x := (F.leaf i).inclusion z
  obtain ⟨c, b, N, hN, hxN, hNVW, haff, hdt⟩ :=
    localLinearization_original_map_locally_affine U f hU nabla hinvariant V W
      σ σ' t t' hσhol hσ'hol hσnonzero hσ'nonzero hσparallel hσ'parallel
      hthol ht'hol hπ hπ' x hx hfx
  have hfinrank : ∀ y : X, Module.finrank ℂ (S.toDistribution y) = 1 := by
    intro y
    obtain ⟨E, hE, hEr⟩ := hstable y
    have heq : S.toDistribution y = E := by
      apply Submodule.restrictScalars_injective ℝ ℂ _
      apply Submodule.map_injective_of_injective (complexTangentToReal d y).injective
      exact (hS y).trans hEr.symm
    rw [heq]
    exact hE
  have hB := localLinearization_stable_coordinate_derivative_invertible
    f a S hS U hunstable t x (hfinrank x) (htker x hx)
  have hB' := localLinearization_stable_coordinate_derivative_invertible
    f a S hS U hunstable t' (f x) (hfinrank (f x)) (ht'ker (f x) hfx)
  have hi : Continuous (F.leaf i).inclusion := (F.leaf i).immersion.contMDiff.continuous
  filter_upwards [hi.continuousAt.eventually (hN.mem_nhds hxN)] with p hp
  refine ⟨(hNVW hp).1, (hNVW hp).2, ?_⟩
  let v : S.toDistribution x := normalizedLocalStableCoordinate S.toDistribution t x
    ((F.leaf i).inclusion p)
  have hsv : mfderiv (complexModel d) (complexModel d) f x v.val ∈
      S.toDistribution (f x) := by
    rw [← localLinearization_complex_stable_derivative_image f a S hS x]
    exact Submodule.mem_map.mpr ⟨v.val, v.property, rfl⟩
  let w : S.toDistribution (f x) :=
    ⟨mfderiv (complexModel d) (complexModel d) f x v.val, hsv⟩
  have hv : localStableCoordinateDerivative S.toDistribution t x v =
      t ((F.leaf i).inclusion p) - t x := by
    exact hB.self_apply_inverse _
  have hw : localStableCoordinateDerivative S.toDistribution t' (f x) w =
      t' (f ((F.leaf i).inclusion p)) - t' (f x) := by
    change transverseScalarDifferential t' (f x)
      (mfderiv (complexModel d) (complexModel d) f x v.val) = _
    rw [hdt]
    change (c : ℂ) * localStableCoordinateDerivative S.toDistribution t x v = _
    rw [hv, haff _ hp, haff x hxN]
    ring
  have heq : normalizedLocalStableCoordinate S.toDistribution t' (f x)
      (f ((F.leaf i).inclusion p)) = w := by
    unfold normalizedLocalStableCoordinate
    rw [← hw]
    exact hB'.inverse_apply_self w
  exact congrArg Subtype.val heq


end

end HolomorphicAnosov.Paper.Zhang
