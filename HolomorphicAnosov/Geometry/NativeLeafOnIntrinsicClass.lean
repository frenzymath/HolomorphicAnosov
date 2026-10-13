import HolomorphicAnosov.Geometry.RealImmersionOfPointwiseIntoComplexModelG1
import HolomorphicAnosov.Geometry.TransverseFoliationsIntrinsicComplexLeaves
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.ImmersionPrecomposeDiffeomorph

noncomputable section
open scoped ContDiff Manifold Topology
open Set
namespace HolomorphicAnosov
universe u

/-- A point-preserving diffeomorphism identifies a smooth immersed leaf with its intrinsic partition
class, preserving the inclusion and its tangent image. -/
theorem native_leaf_on_intrinsic_class {d r : ℕ} {M L : Type u}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (realModel d) ∞ M]
    [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (P : RealTangentDistribution (realModel d) M) (N : HPS.NativeLeaf (r := r) P L)
    (R : Setoid M) (q : Quotient R)
    [TopologicalSpace (IntrinsicFoliationLeaf R q)]
    [ChartedSpace (Fin r → ℝ) (IntrinsicFoliationLeaf R q)]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ (IntrinsicFoliationLeaf R q)]
    (e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ)
      L (IntrinsicFoliationLeaf R q) ∞)
    (he : ∀ z, (e z).val = N.inclusion z)
    (ht : ∀ z : IntrinsicFoliationLeaf R q,
      LinearMap.range (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d)
        Subtype.val z).toLinearMap = P z.val) :
    ∃ N' : HPS.NativeLeaf (r := r) P (IntrinsicFoliationLeaf R q),
      N'.inclusion = Subtype.val := by
  let := N.connected
  let := N.hausdorff
  let := N.countable
  have hval : (Subtype.val : IntrinsicFoliationLeaf R q → M) =
      N.inclusion ∘ e.symm := by
    funext z
    simpa using he (e.symm z)
  refine ⟨{ inclusion := Subtype.val
            injective := Subtype.val_injective
            immersion := ?_
            connected := e.toHomeomorph.connectedSpace_iff.mp N.connected
            hausdorff := e.toHomeomorph.t2Space
            countable := e.symm.toHomeomorph.secondCountableTopology
            tangent := ht }, rfl⟩
  apply real_immersion_of_pointwise_into_complex_model_g1
  intro z
  rw [hval]
  exact immersion_precompose_diffeomorph_g15 (realModel d) N.inclusion e.symm z
    (N.immersion.isImmersionAt (e.symm z))

end HolomorphicAnosov
