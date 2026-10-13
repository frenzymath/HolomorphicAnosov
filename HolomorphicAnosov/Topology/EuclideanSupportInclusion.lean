import HolomorphicAnosov.Topology.EuclideanFixedPointIndexDefinition
import HolomorphicAnosov.Topology.EuclideanSupportOrientationNaturality

noncomputable section
open CategoryTheory TopologicalSpace
namespace HolomorphicAnosov

/-- Source: Dold (1965), §§1.1–1.3, p.1.
For open Euclidean domains V contained in U and equal supports K prime and K, the support inclusion is the relative singular pair map induced by inclusion of V into U. Its complement map is inclusion, using equality of the supports.
Proof:  -/
def supportInclusion (n : ℕ) (V U K' K : Set (EuclideanSpace ℝ (Fin n)))
    (hVU : V ⊆ U) (hKK : K' = K) :
    euclideanSupportPair n V K' ⟶ euclideanSupportPair n U K :=
  singularSubspacePairMap
    (TopCat.ofHom ⟨fun x : V ↦ (⟨x.1, hVU x.2⟩ : U),
      continuous_subtype_val.subtype_mk _⟩)
    {x : V | x.val ∉ K'} {x : U | x.val ∉ K} (by
      intro x hx hk
      exact hx (hKK.symm ▸ hk))

end HolomorphicAnosov
