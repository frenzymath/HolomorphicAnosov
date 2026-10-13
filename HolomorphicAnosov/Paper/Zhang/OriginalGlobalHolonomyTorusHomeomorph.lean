import HolomorphicAnosov.Paper.Zhang.OriginalGlobalHolonomyEuclideanCover
import HolomorphicAnosov.Topology.RealTorusHomeomorphOfAffineCover
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.coordinates
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copied_isManifold

/-!
Global unstable holonomy yields a homeomorphism to a real torus in complex
dimension at least three, assuming homotopy-torus rigidity. (Zhang, Prop. 2.9, p.10;
Ghys, proof of Thm B, p.598)
-/

noncomputable section
open Set
open scoped ContDiff Manifold Topology _root_.Topology
namespace HolomorphicAnosov
universe u
attribute [local instance] complex_isManifold_real

/-- A compact holomorphic Anosov manifold of complex dimension `d ≥ 3` with a
rank-one stable bundle and global unstable holonomy is homeomorphic to the real `2 * d`-torus,
assuming homotopy-torus rigidity. (Zhang, Prop. 2.9, p.10; Ghys, proof of Thm B, p.598) -/
theorem original_global_holonomy_torus_homeomorph
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (hd : 3 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (hholonomy : HasOriginalAnosovGlobalUnstableHolonomy a)
    (HS : HomotopyTorusRigidity.{u}) :
    Nonempty (X ≃ₜ UnitAddTorus (Fin (2 * d))) := by
  classical
  let b : X := Classical.choice (inferInstance : Nonempty X)
  let E := Σ x : X, Path.Homotopic.Quotient b x
  obtain ⟨t, ht⟩ := original_global_holonomy_euclidean_cover f a hstable hholonomy b
  let : TopologicalSpace E := t
  obtain ⟨hSimply, hp, hsurj, e, tau, htau⟩ := ht
  let : SimplyConnectedSpace E := hSimply
  let p : E → X := fun e ↦ e.1
  let e0 : E := ⟨b, Path.Homotopic.Quotient.mk (Path.refl b)⟩
  let coords := Theorem12SupportW2.coordinates d
  let : ChartedSpace (EuclideanSpace ℝ (Fin (2 * d))) X :=
    Theorem12SupportW2.rechart X coords
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) ∞ X :=
    Theorem12SupportW2.copied_isManifold (X := X) coords
  exact Proposition29Cover.real_torus_homeomorph_of_affine_cover
    hd X p hp hsurj e0 e tau htau HS

end HolomorphicAnosov
