import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexTangent

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
/-- The complex unstable subbundle is invariant under the complex derivative when its realification
is the unstable subbundle of the Anosov datum. (Zhang, §2, eq. (1), p. 4; Demailly, I §3.C, p.
23) -/
theorem complex_unstable_invariant
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hU_real : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x) :
    ∀ x v, v ∈ U x → mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x) := by
  intro x v hv
  have hr : complexTangentToReal d x v ∈ a.splitting.unstable.toDistribution x := by
    rw [← hU_real x]
    exact ⟨v, hv, rfl⟩
  have him : mfderiv (realModel d) (realModel d) f.toReal x
      (complexTangentToReal d x v) ∈ a.splitting.unstable.toDistribution (f x) := by
    change _ ∈ a.splitting.unstable.toDistribution (f.toReal x)
    rw [← a.splitting.unstable_map x]
    exact ⟨_, hr, rfl⟩
  rw [f.real_mfderiv_realification, ← hU_real (f x)] at him
  obtain ⟨w, hw, heq⟩ := him
  have hsame : w = mfderiv (complexModel d) (complexModel d) f x v :=
    (complexTangentToReal d (f x)).injective heq
  rwa [← hsame]


end HolomorphicAnosov
