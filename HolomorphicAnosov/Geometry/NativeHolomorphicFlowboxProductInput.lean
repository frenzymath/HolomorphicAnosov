import HolomorphicAnosov.Geometry.NativeActualInvariantFlowboxInput

/-! This file specifies finite holomorphic flowboxes and local products on intrinsic stable and
unstable leaf carriers and proves their existence. (Ghys, §2, pp. 588–590; Prop. 2.2;
Hirsch–Pugh–Shub, pp. 115–116; Shub, Prop. 10.10, pp. 126–127) -/

namespace HolomorphicAnosov
universe u
open Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold Bundle
variable {d : ℕ} {M : Type u}
variable [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
variable [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real

/-- Finite scalar flowboxes and local products covering the manifold, with inclusion-preserving leaf
parameters, biholomorphic unstable receiving maps, and homeomorphic stable receiving maps.
(Ghys, §2, Prop. 2.2; Hirsch–Pugh–Shub, pp. 115–116; Shub, Prop. 10.10) -/
abbrev NativeHolomorphicFlowboxProductInput
    (f : Biholomorph d d M M) (a : AnosovDatum f) : Prop :=
    let scalarSlice := fun (c : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (t : Fin (2 * d - 2) → ℝ) ↦
      (⟨{z | (z, t) ∈ c.target},
        c.open_target.preimage (continuous_id.prodMk continuous_const)⟩ : Opens ℂ)
    let overlapDomain := fun (c c' : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) ↦ c.target ∩ c.symm ⁻¹' c'.source
    let overlapScalar := fun (c c' : OpenPartialHomeomorph M
        (ℂ × (Fin (2 * d - 2) → ℝ))) (p : ℂ × (Fin (2 * d - 2) → ℝ)) ↦
      (c' (c.symm p)).1
    ∃ (ιs ιu : Type u) (Ls : ιs → Type u) (Lu : ιu → Type u)
      (topS : ∀ i, TopologicalSpace (Ls i)) (topU : ∀ i, TopologicalSpace (Lu i)),
    let := topS
    let := topU
    ∃ (chartS : ∀ i, ChartedSpace (Fin (2 * d - 2) → ℝ) (Ls i))
      (chartU : ∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i)),
    let := chartS
    let := chartU
    ∃ (smoothS : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * d - 2) → ℝ) ∞ (Ls i))
      (smoothU : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i)),
    let := smoothS
    let := smoothU
    ∃ (S : HPS.LeafPartition a.splitting.stable.toDistribution ιs Ls (fun _ ↦ 2 * d - 2))
      (U : HPS.LeafPartition a.splitting.unstable.toDistribution ιu Lu (fun _ ↦ 2))
      (complexChart : ∀ i, ChartedSpace ℂ (Lu i)),
      (∀ i, letI := complexChart i
        IsManifold 𝓘(ℂ) ∞ (Lu i)) ∧
      (∀ i, letI := complexChart i
        ContMDiff 𝓘(ℂ) (complexModel d) ∞ (U.leaf i).inclusion ∧
        ∀ z, Function.Injective (mfderiv 𝓘(ℂ) (complexModel d) (U.leaf i).inclusion z)) ∧
      (∃ m : MetricSpace M,
        m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
          (inferInstance : TopologicalSpace M) ∧
        (∀ i (x : Ls i) y,
          (∃ z, (S.leaf i).inclusion z = y) ↔
            @ForwardAsymptotic M m (f : M → M) ((S.leaf i).inclusion x) y) ∧
        (∀ i (x : Lu i) y,
          (∃ z, (U.leaf i).inclusion z = y) ↔
            @ForwardAsymptotic M m (f.symm : M → M) ((U.leaf i).inclusion x) y)) ∧
      Nonempty (HPS.LeafDynamicalInvariance S f.toReal) ∧
      Nonempty (HPS.LeafDynamicalInvariance U f.toReal) ∧
      (∃ (βs βu : Type u) (Ts : βs → Type u) (Tu : βu → Type u)
        (topTs : ∀ b, TopologicalSpace (Ts b)) (topTu : ∀ b, TopologicalSpace (Tu b)),
        let := topTs
        let := topTu
        Nonempty (HPS.LaminationBoxes S βs (fun _ ↦ 2 * d - 2) Ts) ∧
        Nonempty (HPS.LaminationBoxes U βu (fun _ ↦ 2) Tu)) ∧
      (∃ (n : ℕ) (T : Fin n → Opens (Fin (2 * d - 2) → ℝ))
        (c : Fin n → OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ)))
        (label : ∀ i, T i → ιu) (branch : ∀ i t, Opens (Lu (label i t)))
        (parametrization : ∀ i t, letI := complexChart (label i t)
          Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (scalarSlice (c i) t.val) (branch i t) ∞),
        (∀ x : M, ∃ i, x ∈ (c i).source) ∧
        (∀ i p, p ∈ (c i).target → p.2 ∈ T i) ∧
        (∀ i t (z : scalarSlice (c i) t.val),
          (c i).symm (z.val, t.val) =
            (U.leaf (label i t)).inclusion ((parametrization i t z).val)) ∧
        (∀ i j, let Ω := overlapDomain (c i) (c j)
          let h := overlapScalar (c i) (c j)
          ∀ p ∈ Ω, ∃ (A B : Opens ℂ), p.1 ∈ A ∧
            (∀ z ∈ A, (z, p.2) ∈ Ω) ∧
            ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) A B ∞,
              ∀ z : A, (e z : ℂ) = h (z.val, p.2))) ∧
      (∀ x : M,
        ∃ (qu : ιu) (qs : ιs),
        let := complexChart qu
        ∃ (Pu : Opens (Lu qu)) (Ps : Opens (Ls qs)),
          IsConnected (Pu : Set (Lu qu)) ∧ IsConnected (Ps : Set (Ls qs)) ∧
          ∃ (u₀ : Pu) (s₀ : Ps) (O : Opens M) (Ψ : (Pu × Ps) ≃ₜ O),
            (U.leaf qu).inclusion u₀.val = x ∧
            (S.leaf qs).inclusion s₀.val = x ∧
            (Ψ (u₀, s₀)).val = x ∧
            (∀ u : Pu, (Ψ (u, s₀)).val = (U.leaf qu).inclusion u.val) ∧
            (∀ t : Ps, (Ψ (u₀, t)).val = (S.leaf qs).inclusion t.val) ∧
              (∀ t : Ps, ∃ q : ιu,
                let := complexChart q
                ∃ (V : Opens (Lu q)) (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞),
                  ∀ u : Pu, (U.leaf q).inclusion (b u).val = (Ψ (u, t)).val) ∧
              (∀ u : Pu, ∃ q : ιs,
                ∃ (V : Opens (Ls q)) (b : Ps ≃ₜ V),
                  ∀ t : Ps, (S.leaf q).inclusion (b t).val = (Ψ (u, t)).val) ∧
              (d = 1 → (∀ t : Ps, t.val = s₀.val) ∧
                ∃ j : Pu ≃ₜ O,
                  (∀ u : Pu, (j u).val = (U.leaf qu).inclusion u.val) ∧
                  (∀ w : O, Ψ.symm w = (j.symm w, s₀))))

/-- A compact holomorphic Anosov manifold with complex rank-one unstable distribution admits finite
holomorphic flowboxes and intrinsic stable–unstable local products. (Ghys, Prop. 2.2; Shub,
Prop. 10.10) -/
theorem native_holomorphic_flowbox_product_input_exists
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    NativeHolomorphicFlowboxProductInput f a :=
  Ghys.native_actual_invariant_flowbox_input f a hRank

end HolomorphicAnosov
