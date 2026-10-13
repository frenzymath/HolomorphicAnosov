import HolomorphicAnosov.Geometry.NativeHolomorphicFlowboxProductInput
import HolomorphicAnosov.Dynamics.Anosov.NativeLeafRank
import HolomorphicAnosov.Dynamics.Anosov.NativeProductBoxDimension
import HolomorphicAnosov.Dynamics.Anosov.GlobalLaminationTensorMetric
import HolomorphicAnosov.Dynamics.Anosov.DistanceLeafRange
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.original_real_tangent_finrank
import HolomorphicAnosov.Geometry.Manifold.TheoremASupport.HasComplexRankOne_real_finrank_eq_two
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Topology.EuclideanOpenDimensionInvariance
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.HolomorphicSliceTwoDerivativesContinuous
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Holomorphic Anosov systems with complex rank-one unstable distribution admit intrinsic
holomorphic unstable leaves, local products with stable leaves, and a finite holomorphic
flowbox cover. (Ghys, §2, pp. 588–590 and Lemma 3.3; HPS, (5.5), §6B and (7.5)–(7.6);
Demailly, I§7, Lemma 7.15; Glöckner, Thm 5.3, Remark 5.6 and Thm 5.10;
Fisher–Hasselblatt, Prop. 12.1.3 and Lemma 12.5.18; Shub, Prop. 10.10) -/

noncomputable section
namespace HolomorphicAnosov.Ghys.ActualInvariantSectionFlowboxCoverG5
open Set _root_.Topology TopologicalSpace
open scoped ContDiff Manifold Bundle
universe u
set_option autoImplicit false
variable {d : ℕ} {M : Type u}
variable [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
variable [IsManifold (complexModel d) ∞ M]
attribute [local instance] complex_isManifold_real

/-- A compact holomorphic Anosov system with complex rank-one unstable distribution admits
a finite holomorphic flowbox cover and intrinsic leaf products with holomorphic stable
holonomy. (Ghys, §2, pp. 588–590, Prop. 2.2 and Lemma 3.3; HPS, (5.5), §6B and
(7.5)–(7.6); Demailly, I§7, Lemma 7.15; Glöckner, Thm 5.3, Remark 5.6 and Thm 5.10;
Fisher–Hasselblatt, Prop. 12.1.3 and Lemma 12.5.18; Shub, Prop. 10.10) -/
theorem actual_invariant_section_flowbox_geometry [T2Space M] [SecondCountableTopology M]
    [CompactSpace M] (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
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
    letI := topS
    letI := topU
    ∃ (chartS : ∀ i, ChartedSpace (Fin (2 * d - 2) → ℝ) (Ls i))
      (chartU : ∀ i, ChartedSpace (Fin 2 → ℝ) (Lu i)),
    letI := chartS
    letI := chartU
    ∃ (smoothS : ∀ i, IsManifold 𝓘(ℝ, Fin (2 * d - 2) → ℝ) ∞ (Ls i))
      (smoothU : ∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (Lu i)),
    letI := smoothS
    letI := smoothU
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
        letI := topTs
        letI := topTu
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
        letI := complexChart qu
        ∃ (Pu : Opens (Lu qu)) (Ps : Opens (Ls qs)),
          IsConnected (Pu : Set (Lu qu)) ∧ IsConnected (Ps : Set (Ls qs)) ∧
          ∃ (u₀ : Pu) (s₀ : Ps) (O : Opens M) (Ψ : (Pu × Ps) ≃ₜ O),
            (U.leaf qu).inclusion u₀.val = x ∧
            (S.leaf qs).inclusion s₀.val = x ∧
            (Ψ (u₀, s₀)).val = x ∧
            (∀ u : Pu, (Ψ (u, s₀)).val = (U.leaf qu).inclusion u.val) ∧
            (∀ t : Ps, (Ψ (u₀, t)).val = (S.leaf qs).inclusion t.val) ∧
            ∃ (πu : C(O, Pu)) (πs : C(O, Ps)),
              (∀ u : Pu, ∀ t : Ps, πu (Ψ (u, t)) = u ∧ πs (Ψ (u, t)) = t) ∧
              (∀ y : O, Ψ (πu y, πs y) = y) ∧
              (∀ u : Pu, ∀ t : Ps, ∀ y : M,
                ((∃ b : Ps, (Ψ (u, b)).val = y) ∧
                  (∃ v : Pu, (Ψ (v, t)).val = y)) ↔ y = (Ψ (u, t)).val) ∧
              (∀ t : Ps, ∃ q : ιu,
                letI := complexChart q
                ∃ (V : Opens (Lu q)) (b : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) Pu V ∞),
                  ∀ u : Pu, (U.leaf q).inclusion (b u).val = (Ψ (u, t)).val) ∧
              (∀ u : Pu, ∃ q : ιs,
                ∃ (V : Opens (Ls q)) (b : Ps ≃ₜ V),
                  ∀ t : Ps, (S.leaf q).inclusion (b t).val = (Ψ (u, t)).val) ∧
              (d = 1 → (∀ t : Ps, t.val = s₀.val) ∧
                ∃ j : Pu ≃ₜ O,
                  (∀ u : Pu, (j u).val = (U.leaf qu).inclusion u.val) ∧
                  (∀ w : O, Ψ.symm w = (j.symm w, s₀)))) := by
  classical
  have hgeometry :=
    native_holomorphic_flowbox_product_input_exists f a hRank
  dsimp only [NativeHolomorphicFlowboxProductInput] at hgeometry
  dsimp only at hgeometry ⊢
  obtain ⟨ιs, ιu, Ls, Lu, topS, topU, hgeometry⟩ := hgeometry
  let := topS
  let := topU
  obtain ⟨chartS, chartU, hgeometry⟩ := hgeometry
  let := chartS
  let := chartU
  obtain ⟨smoothS, smoothU, hgeometry⟩ := hgeometry
  let := smoothS
  let := smoothU
  obtain ⟨S, U, complexChart, hcomplex, hinclusion, hmetric, hS, hU, hboxes,
    hfinite, hlocal⟩ := hgeometry
  refine ⟨ιs, ιu, Ls, Lu, topS, topU, chartS, chartU, smoothS, smoothU,
    S, U, complexChart, hcomplex, hinclusion, hmetric, hS, hU, hboxes, hfinite, ?_⟩
  intro x
  obtain ⟨qu, qs, Pu, Ps, hPu, hPs, u₀, s₀, O, Ψ, hu₀, hs₀, hcenter,
    hhorizontal, hvertical, huleaves, hsleaves, hdim⟩ := hlocal x
  refine ⟨qu, qs, Pu, Ps, hPu, hPs, u₀, s₀, O, Ψ, hu₀, hs₀, hcenter,
    hhorizontal, hvertical, ?_⟩
  let πu : C(O, Pu) := ⟨fun y ↦ (Ψ.symm y).1, continuous_fst.comp Ψ.symm.continuous⟩
  let πs : C(O, Ps) := ⟨fun y ↦ (Ψ.symm y).2, continuous_snd.comp Ψ.symm.continuous⟩
  refine ⟨πu, πs, ?_, ?_, ?_, huleaves, hsleaves, hdim⟩
  · intro u t
    exact ⟨congrArg Prod.fst (Ψ.symm_apply_apply (u, t)),
      congrArg Prod.snd (Ψ.symm_apply_apply (u, t))⟩
  · intro y
    exact Ψ.apply_symm_apply y
  · intro u t y
    constructor
    · rintro ⟨⟨b, hb⟩, ⟨v, hv⟩⟩
      have hp : (u, b) = (v, t) := Ψ.injective (Subtype.ext (hb.trans hv.symm))
      have hbt : b = t := congrArg Prod.snd hp
      simpa only [hbt] using hb.symm
    · intro hy
      exact ⟨⟨t, hy.symm⟩, ⟨u, hy.symm⟩⟩


end HolomorphicAnosov.Ghys.ActualInvariantSectionFlowboxCoverG5
