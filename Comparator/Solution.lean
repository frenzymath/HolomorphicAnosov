import Mathlib
import HolomorphicAnosov.Targets.TheoremA
import HolomorphicAnosov.Targets.Theorem11
import HolomorphicAnosov.Targets.Theorem12
import HolomorphicAnosov.Targets.Theorem13

/-!
# Solution

The four statements of `Comparator/Challenge.lean`, word for word, proved by the theorems
`theorem_A`, `theorem_1_1`, `theorem_1_2` and `theorem_1_3` of the library.
-/

universe u

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- Theorem A. A holomorphic Anosov diffeomorphism of a compact connected complex manifold
whose stable or unstable bundle has complex rank one is biholomorphically conjugate to a
hyperbolic linear automorphism of a complex torus (assuming homotopy-torus rigidity). -/
theorem zhang_theorem_A {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hcodim : HasComplexRankOne a.splitting.stable.toDistribution ∨
      HasComplexRankOne a.splitting.unstable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    HasHyperbolicComplexTorusModel (d := d) (fun x ↦ f x) :=
  theorem_A f a hcodim HS

/-- Theorem 1.1. If `d ≥ 2` and the stable bundle has complex rank one, then `f` is
topologically conjugate to a hyperbolic automorphism of the real torus `T^{2d}`
(assuming homotopy-torus rigidity). -/
theorem zhang_theorem_1_1 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (hd : 2 ≤ d) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    HyperbolicRealToralConjugacy (2 * d) X (fun x ↦ f x) :=
  theorem_1_1 hd f a hstable HS

/-- Theorem 1.2. If `X` is homeomorphic to a torus and both `E^s` and `E^u` are holomorphic
subbundles of the tangent bundle, then `f` is biholomorphically conjugate to a linear
automorphism of a complex torus. -/
theorem zhang_theorem_1_2 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hStable : ∃ (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)),
      IsHolomorphicTangentSubbundle r P ∧ ∀ x : X,
        ((P x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap =
            a.splitting.stable.toDistribution x)
    (hUnstable : ∃ (r : ℕ) (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)),
      IsHolomorphicTangentSubbundle r P ∧ ∀ x : X,
        ((P x).restrictScalars ℝ).map
          (complexTangentToReal d x).toLinearEquiv.toLinearMap =
            a.splitting.unstable.toDistribution x)
    (hT : ∃ n : ℕ, Nonempty (X ≃ₜ UnitAddTorus (Fin n))) :
    ∃ (L : FullComplexLattice d) (A : LatticeLinearEquiv L)
      (h : Biholomorph d d X (ComplexTorus L)),
      Function.Semiconj (fun x ↦ h x) (fun x ↦ f x)
        (fun t ↦ quotientLinearEquiv A t) :=
  theorem_1_2 f a hStable hUnstable hT

/-- Theorem 1.3. If the stable bundle has complex rank one, then `E^s` and `E^u` are holomorphic
subbundles of the tangent bundle, of ranks `1` and `d - 1` (assuming homotopy-torus
rigidity). -/
theorem zhang_theorem_1_3 {d : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hstable : HasComplexRankOne a.splitting.stable.toDistribution)
    (HS : HomotopyTorusRigidity.{u}) :
    ∃ S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x),
      (∀ x, ((S x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
          a.splitting.stable.toDistribution x) ∧
      (∀ x, ((U x).restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap =
          a.splitting.unstable.toDistribution x) ∧
      IsHolomorphicTangentSubbundle 1 S ∧ IsHolomorphicTangentSubbundle (d - 1) U :=
  theorem_1_3 f a hstable HS

end HolomorphicAnosov
