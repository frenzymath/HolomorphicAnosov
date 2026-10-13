import HolomorphicAnosov.Geometry.NormalizedLocalStableCoordinateAffineGerm
import HolomorphicAnosov.Paper.Zhang.LocalLinearization.OriginalMapLocallyAffine

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u
variable {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
private theorem connection_invariant_identity (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U) :
    ∃ hU, QuotientLineConnection.IsInvariant nabla (Diffeomorph.refl (complexModel d) M ∞) hU := by
  let f : Biholomorph d d M M := Diffeomorph.refl (complexModel d) M ∞
  have hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x) := by
    intro x v hv
    change mfderiv (complexModel d) (complexModel d) id x v ∈ U x
    rw [mfderiv_id]
    exact hv
  refine ⟨hU, ?_⟩
  have hq (x : M) : QuotientLineConnection.quotientDerivative f hU x = LinearMap.id := by
    ext v
    simp [QuotientLineConnection.quotientDerivative, f, mfderiv_id]
  have hg {V W : TopologicalSpace.Opens M}
      (e : QuotientLineConnection.HolomorphicFrame U V)
      (e' : QuotientLineConnection.HolomorphicFrame U W) :
      QuotientLineConnection.imageFrameCoefficient f hU e e' = e'.coefficient e.sectionValue := by
    funext x
    simp only [QuotientLineConnection.imageFrameCoefficient,
      QuotientLineConnection.HolomorphicFrame.coefficient, hq]
    rfl
  intro V W e e' x hx hx'
  rw [hg]
  have hh := nabla.gauge W V e' e x hx' hx
  change nabla.form V e x = _ + (nabla.form W e' x).comp
    (mfderiv (realModel d) (realModel d) id x)
  rw [mfderiv_id]
  change nabla.form V e x = _ + nabla.form W e' x
  simpa only [add_comm] using hh
end
end HolomorphicAnosov.Paper.Zhang

namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u
/-- Two parallel transverse coordinate pairs differ locally by an affine change with nonzero slope.
(Zhang, Lemma 2.5, eq. (15), p. 8) -/
theorem parallel_coordinate_pairs_affine_germ
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U)
    (V W : TopologicalSpace.Opens M)
    (σ σ' : ∀ x : M, QuotientLineConnection.Fibre U x) (t t' : M → ℂ)
    (hσ : QuotientLineConnection.IsHolomorphicSection U V σ)
    (hσ' : QuotientLineConnection.IsHolomorphicSection U W σ')
    (hnσ : ∀ x ∈ V, σ x ≠ 0) (hnσ' : ∀ x ∈ W, σ' x ≠ 0)
    (hpσ : QuotientLineConnection.IsParallelOn nabla V σ)
    (hpσ' : QuotientLineConnection.IsParallelOn nabla W σ')
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (ht' : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t' W)
    (hformula : ∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t y v • σ y)
    (hformula' : ∀ y ∈ W, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t' y v • σ' y)
    (x : M) (hx : x ∈ V) (hxW : x ∈ W) :
    ∃ (c : ℂˣ) (b : ℂ) (N : Set M), IsOpen N ∧ x ∈ N ∧
      N ⊆ (V : Set M) ∩ (W : Set M) ∧
      (∀ y ∈ N, t' y = (c : ℂ) * t y + b) := by
  obtain ⟨hU, hi⟩ := connection_invariant_identity U nabla
  obtain ⟨c, b, N, hN, hxN, hsub, heq, hd⟩ :=
    localLinearization_original_map_locally_affine U
      (Diffeomorph.refl (complexModel d) M ∞) hU nabla hi V W σ σ' t t'
      hσ hσ' hnσ hnσ' hpσ hpσ' ht ht' hformula hformula' x hx hxW
  exact ⟨c, b, N, hN, hxN, hsub, heq⟩
end
end HolomorphicAnosov.Paper.Zhang

namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u
/-- Affine transition factors cancel in the normalized coordinate germ. (Zhang, eq. (15)) -/
private theorem normalized_parallel_coordinate_pairs_germ
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (U : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (nabla : QuotientLineConnection.Connection U)
    (V W : TopologicalSpace.Opens M)
    (σ σ' : ∀ x : M, QuotientLineConnection.Fibre U x) (t t' : M → ℂ)
    (hσ : QuotientLineConnection.IsHolomorphicSection U V σ)
    (hσ' : QuotientLineConnection.IsHolomorphicSection U W σ')
    (hnσ : ∀ x ∈ V, σ x ≠ 0) (hnσ' : ∀ x ∈ W, σ' x ≠ 0)
    (hpσ : QuotientLineConnection.IsParallelOn nabla V σ)
    (hpσ' : QuotientLineConnection.IsParallelOn nabla W σ')
    (ht : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t V)
    (ht' : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ t' W)
    (hformula : ∀ y ∈ V, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t y v • σ y)
    (hformula' : ∀ y ∈ W, ∀ v : TangentSpace (complexModel d) y,
      QuotientLineConnection.projection U y v = transverseScalarDifferential t' y v • σ' y)
    (S : ∀ x : M, Submodule ℂ (TangentSpace (complexModel d) x))
    (x : M) (hx : x ∈ V) (hxW : x ∈ W) :
    normalizedLocalStableCoordinate S t' x =ᶠ[nhds x]
      normalizedLocalStableCoordinate S t x := by
  obtain ⟨c, b, N, hN, hxN, hsub, heq⟩ := parallel_coordinate_pairs_affine_germ
    U nabla V W σ σ' t t' hσ hσ' hnσ hnσ' hpσ hpσ' ht ht'
    hformula hformula' x hx hxW
  exact normalizedLocalStableCoordinate_affine_germ S t t' x c b
    (((ht x hx).contMDiffAt (V.isOpen.mem_nhds hx)).mdifferentiableAt (by simp))
    (Filter.eventually_of_mem (hN.mem_nhds hxN) heq)
end
end HolomorphicAnosov.Paper.Zhang
