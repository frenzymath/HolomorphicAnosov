import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth
import HolomorphicAnosov.Paper.Zhang.VectorOrbitBijective
import HolomorphicAnosov.Paper.Zhang.VectorOrbitDerivativeInjective
import HolomorphicAnosov.Geometry.RealEquivInverseContMDiff
import Mathlib.Geometry.Manifold.Diffeomorph

/-! This file proves smoothness of the orbit map for a free transitive vector action by biholomorphisms. (Zhang, p. 13) -/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

/-- The orbit map of a free transitive continuous vector action by biholomorphisms is a real smooth diffeomorphism on the original manifold. -/
theorem free_transitive_vector_orbit_diffeomorphism
    (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (d : ℕ) (M : Type v) [TopologicalSpace M] [T2Space M] [Nonempty M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ (ComplexModel d))
    (A : V → Biholomorph d d M M)
    (hcontinuous : Continuous (fun p : V × M ↦ A p.1 p.2))
    (hzero : ∀ x : M, A 0 x = x)
    (hadd : ∀ (a b : V) (x : M), A (a + b) x = A a (A b x))
    (hfree : ∀ (a : V) (x : M), A a x = x → a = 0)
    (htransitive : ∀ x y : M, ∃ a : V, A a x = y) :
    ∀ x0 : M, ∃ Θ : Diffeomorph (modelWithCornersSelf ℝ V) (realModel d) V M ∞,
      ∀ a : V, Θ a = A a x0 := by
  classical
  have ho := Paper.Zhang.vector_action_orbit_smooth A hzero hadd hcontinuous
  intro x0
  let o : V → M := fun a ↦ A a x0
  have hbij : Function.Bijective o :=
    vector_orbit_bijective A hzero hadd hfree htransitive x0
  let e : V ≃ M := Equiv.ofBijective o hbij
  have hs : ContMDiff (modelWithCornersSelf ℝ V) (realModel d) ∞ o := ho x0
  have hi : ∀ a, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ V) (realModel d) o a) :=
    vector_orbit_derivative_injective A hzero hadd hfree ho x0
  have hinv : ContMDiff (realModel d) (modelWithCornersSelf ℝ V) ∞ e.symm :=
    real_equiv_inverse_contMDiff hdim e hs hi
  refine ⟨{ toEquiv := e, contMDiff_toFun := hs, contMDiff_invFun := hinv }, ?_⟩
  intro a
  rfl

end HolomorphicAnosov
