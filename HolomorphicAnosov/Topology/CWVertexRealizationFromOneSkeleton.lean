import HolomorphicAnosov.Topology.CWOneSkeletonPiOneSurjective
import HolomorphicAnosov.Topology.Franks.PointedMapComposition

/-!
# Realization after extension from the original one-skeleton

Source: Hatcher, *Algebraic Topology*, Proposition 1B.9, pp.90–91, together
with Proposition 1.26, pp.50–51. This is the final fundamental-group argument
after constructing the continuous extension over the cells.
-/

namespace HolomorphicAnosov

open _root_.Topology

/-- A continuous extension of the prescribed based one-skeleton map realizes
the given homomorphism on the whole CW complex.

Proof: the original one-skeleton inclusion is surjective on fundamental groups
by Hatcher Proposition 1.26. The extension has the required basepoint value
because its restriction equals the prescribed map. Functoriality of the actual
pointed fundamental-group maps identifies its composite with the inclusion map
with the prescribed one-skeleton homomorphism. For an arbitrary class, choose
a preimage under the surjective inclusion map and apply this identity. This
uses the original subspace topology and involves no change of basepoint path
or group convention. It also applies when there are no one-cells.

DAG node: `topo.cw_vertex_realization_from_one_skeleton_g1`.
-/
theorem cw_vertex_realization_from_one_skeleton
    {K : Type*} {Y : Type*} [TopologicalSpace K] [TopologicalSpace Y]
    [T2Space K] [ConnectedSpace K] [CWComplex (Set.univ : Set K)]
    (k₀ : K) (hk₀ : k₀ ∈ (CWComplex.skeleton (Set.univ : Set K) 0 : Set K))
    (y₀ : Y) (φ : FundamentalGroup K k₀ →* FundamentalGroup Y y₀) :
    let K₁ := ↥(CWComplex.skeletonLT (Set.univ : Set K) 2 : Set K)
    let k₁ : K₁ :=
      ⟨k₀, CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hk₀⟩
    let inclusion : C(K₁, K) := ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (f₁ : C(K₁, Y)) (hf₁ : f₁ k₁ = y₀) (f : C(K, Y)),
      f.comp inclusion = f₁ →
      FundamentalGroup.mapOfEq f₁ hf₁ = φ.comp (FundamentalGroup.map inclusion k₁) →
      ∃ hf : f k₀ = y₀, FundamentalGroup.mapOfEq f hf = φ := by
  dsimp only
  intro f₁ hf₁ f hext hφ
  subst f₁
  have hf : f k₀ = y₀ := hf₁
  refine ⟨hf, ?_⟩
  let K₁ := ↥(CWComplex.skeletonLT (Set.univ : Set K) 2 : Set K)
  let k₁ : K₁ :=
    ⟨k₀, CWComplex.skeletonLT_mono (show (1 : ℕ∞) ≤ 2 by decide) hk₀⟩
  let inclusion : C(K₁, K) := ⟨Subtype.val, continuous_subtype_val⟩
  have hsurj := (cw_one_skeleton_pi1_surjective k₀ hk₀).2.1
  have hinc : FundamentalGroup.mapOfEq inclusion (show inclusion k₁ = k₀ from rfl) =
      FundamentalGroup.map inclusion k₁ := by
    ext z
    simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  have hcomp : (FundamentalGroup.mapOfEq f hf).comp
      (FundamentalGroup.map inclusion k₁) =
      FundamentalGroup.mapOfEq (f.comp inclusion) hf₁ := by
    have h := FranksPointedTransport.mapOfEq_comp inclusion f
      (show inclusion k₁ = k₀ from rfl) hf
    simpa only [hinc] using h
  ext a
  obtain ⟨b, rfl⟩ := hsurj a
  change ((FundamentalGroup.mapOfEq f hf).comp
    (FundamentalGroup.map inclusion k₁)) b = _
  rw [hcomp, hφ]
  rfl


end HolomorphicAnosov
