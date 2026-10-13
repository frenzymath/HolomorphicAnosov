import HolomorphicAnosov.Ghys.AffineDevelopingExistence
import HolomorphicAnosov.Ghys.AffineDevelopingLocalDiffeomorph
import HolomorphicAnosov.Ghys.AffineDevelopingUniqueness

/-!
This file gives existence, uniqueness up to affine postcomposition, and naturality of developing
maps on simply connected complex affine curves, together with the empty-curve case. (Thurston,
Ch. 3 §3.5, pp. 34–35; Ghys, Lemma 3.3) -/

open Set Filter _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov.Ghys

universe u v

/-- A simply connected complex affine curve admits a holomorphic developing map that is a local
diffeomorphism and induces its affine atlas. Any two developing maps differ by an invertible
affine postcomposition. (Thurston, Ch. 3 §3.5, pp. 34–35; Ghys, Lemma 3.3, p. 593) -/
theorem affine_complete_developing_continuation
    (L : Type u) [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [IsManifold (complexModel 1) ∞ L] [T2Space L] [SecondCountableTopology L]
    [ConnectedSpace L] [SimplyConnectedSpace L] (A : ComplexAffineAtlas L) :
    let Develops := fun D : L → ℂ ↦
      ∀ c ∈ A.charts, ∀ x ∈ c.source,
        ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = a.apply (c y)
    (∃ D : L → ℂ, Develops D ∧ ContMDiff (complexModel 1) 𝓘(ℂ) ∞ D ∧
      IsLocalDiffeomorph (complexModel 1) 𝓘(ℂ) ∞ D) ∧
    ∀ D₁ D₂ : L → ℂ, Develops D₁ → Develops D₂ →
      ∃ a : ComplexAffineTransformation, ∀ x : L, D₂ x = a.apply (D₁ x) := by
  constructor
  · obtain ⟨D, hD⟩ := affine_developing_exists L A
    have hlocal := affine_developing_isLocalDiffeomorph A D hD
    exact ⟨D, hD, hlocal.contMDiff, hlocal⟩
  · exact affine_developing_uniqueness L A

/-- Under an affine biholomorphism `F`, the composite `D ∘ F` differs from a developing map of the
source curve by one invertible affine postcomposition. (Thurston, Ch. 3 §3.5, p. 35; Ghys, Lemma
3.3, p. 593) -/
theorem affine_complete_developing_naturality
    (L : Type u) (L' : Type v)
    [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [IsManifold (complexModel 1) ∞ L] [T2Space L] [SecondCountableTopology L]
    [ConnectedSpace L] [SimplyConnectedSpace L]
    [TopologicalSpace L'] [ChartedSpace (ComplexModel 1) L']
    [IsManifold (complexModel 1) ∞ L'] [T2Space L'] [SecondCountableTopology L']
    [ConnectedSpace L'] [SimplyConnectedSpace L']
    (A : ComplexAffineAtlas L) (A' : ComplexAffineAtlas L')
    (F : Diffeomorph (complexModel 1) (complexModel 1) L' L ∞)
    (hF : ∀ c' ∈ A'.charts, ∀ c ∈ A.charts, ∀ x ∈ c'.source, F x ∈ c.source →
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, c (F y) = a.apply (c' y))
    (D : L → ℂ) (D' : L' → ℂ)
    (hD : ∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = a.apply (c y))
    (hD' : ∀ c ∈ A'.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D' y = a.apply (c y)) :
    ∃ a : ComplexAffineTransformation, ∀ x : L', D (F x) = a.apply (D' x) := by
  apply affine_developing_uniqueness L' A' D' (fun x ↦ D (F x)) hD'
  intro c' hc' x hxc'
  obtain ⟨c, hc, hxc⟩ := A.cover (F x)
  obtain ⟨a, ha⟩ := hD c hc (F x) hxc
  obtain ⟨b, hb⟩ := hF c' hc' c hc x hxc' hxc
  refine ⟨{ slope := a.slope * b.slope
            slope_ne_zero := mul_ne_zero a.slope_ne_zero b.slope_ne_zero
            translation := a.slope * b.translation + a.translation }, ?_⟩
  have ha' := F.continuous.continuousAt.eventually ha
  filter_upwards [ha', hb] with y hay hby
  rw [hay, hby]
  dsimp [ComplexAffineTransformation.apply]
  ring

/-- An empty affine curve has a unique developing map, which is holomorphic and a local
diffeomorphism. Any two maps from it to `ℂ` differ by an invertible affine postcomposition.
(Thurston, Ch. 3 §3.5, pp. 34–35; Ghys, Lemma 3.3, p. 593) -/
theorem affine_complete_developing_empty
    (L : Type u) [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    [IsEmpty L] (A : ComplexAffineAtlas L) :
    let D : L → ℂ := fun x ↦ isEmptyElim x
    (∀ c ∈ A.charts, ∀ x ∈ c.source,
      ∃ a : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = a.apply (c y)) ∧
    ContMDiff (complexModel 1) 𝓘(ℂ) ∞ D ∧
    IsLocalDiffeomorph (complexModel 1) 𝓘(ℂ) ∞ D ∧
    (∀ E : L → ℂ, E = D) ∧
    ∀ D₁ D₂ : L → ℂ,
      ∃ a : ComplexAffineTransformation, ∀ x : L, D₂ x = a.apply (D₁ x) := by
  dsimp
  let idAffine : ComplexAffineTransformation :=
    { slope := 1
      slope_ne_zero := one_ne_zero
      translation := 0 }
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc x hx
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x
  · intro E
    funext x
    exact isEmptyElim x
  · intro D₁ D₂
    refine ⟨idAffine, ?_⟩
    intro x
    exact isEmptyElim x

end HolomorphicAnosov.Ghys
