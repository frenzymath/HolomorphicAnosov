import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxGeometryG14
import HolomorphicAnosov.Analysis.LocalBiholomorphicSliceDerivatives
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

/-!
Open scalar slices and continuity of coordinate overlaps for flowboxes, together with a finite
flowbox cover with holomorphic unstable slices. (Ghys, §2, pp. 588–590 and Lemma 3.3, pp. 592–593)
-/

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

omit [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] in
/-- Fixing the transverse coordinate in the target of an open partial homeomorphism gives an open
subset of `ℂ`. (Ghys, §2, pp. 588–590 and Lemma 3.3) -/
theorem scalarSlice_isOpen
    {c : OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ))}
    (t : Fin (2 * d - 2) → ℝ) :
    IsOpen {z : ℂ | (z, t) ∈ c.target} := by
  exact c.open_target.preimage (continuous_id.prodMk continuous_const)

omit [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] in
theorem overlapDomain_isOpen
    {c c' : OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ))} :
    IsOpen (c.target ∩ c.symm ⁻¹' c'.source) := by
  exact c.isOpen_inter_preimage_symm c'.open_source

omit [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] in
theorem overlapScalar_continuousOn
    {c c' : OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ))} :
    ContinuousOn (fun p : ℂ × (Fin (2 * d - 2) → ℝ) ↦ (c' (c.symm p)).1)
      (c.target ∩ c.symm ⁻¹' c'.source) := by
  intro p hp
  have hc : ContinuousOn (fun q ↦ c.symm q)
      (c.target ∩ c.symm ⁻¹' c'.source) :=
    c.symm.continuousOn.mono inter_subset_left
  have hm : MapsTo (fun q ↦ c.symm q)
      (c.target ∩ c.symm ⁻¹' c'.source) c'.source := by
    intro q hq
    exact hq.2
  have hcc : ContinuousOn (fun q ↦ c' (c.symm q))
      (c.target ∩ c.symm ⁻¹' c'.source) := c'.continuousOn.comp hc hm
  exact (continuous_fst.continuousOn.comp hcc (fun _ _ ↦ Set.mem_univ _)) p hp

omit [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] in
theorem overlapScalar_slice_continuousOn
    {c c' : OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ))}
    (t : Fin (2 * d - 2) → ℝ) :
    ContinuousOn (fun z : ℂ ↦ (c' (c.symm (z, t))).1)
      {z : ℂ | (z, t) ∈ c.target ∩ c.symm ⁻¹' c'.source} := by
  let e : ℂ → ℂ × (Fin (2 * d - 2) → ℝ) := fun z ↦ (z, t)
  have he : Continuous e := continuous_id.prodMk continuous_const
  have hΩ := overlapScalar_continuousOn (c := c) (c' := c')
  have hcomp := hΩ.comp he.continuousOn (by
    intro z hz
    exact hz)
  exact hcomp

omit [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] in
/-- Fixing the transverse coordinate in a flowbox overlap gives an open scalar domain. -/
theorem overlapScalar_slice_domain_isOpen
    {c c' : OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ))}
    (t : Fin (2 * d - 2) → ℝ) :
    IsOpen {z : ℂ | (z, t) ∈ c.target ∩ c.symm ⁻¹' c'.source} := by
  let e : ℂ → ℂ × (Fin (2 * d - 2) → ℝ) := fun z ↦ (z, t)
  exact (overlapDomain_isOpen (c := c) (c' := c')).preimage
    (continuous_id.prodMk continuous_const)

omit [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M] in
theorem overlapScalar_slice_chartInverse_continuousOn
    {c c' : OpenPartialHomeomorph M (ℂ × (Fin (2 * d - 2) → ℝ))}
    (t : Fin (2 * d - 2) → ℝ) :
    ContinuousOn (fun z : ℂ ↦ c.symm (z, t))
      {z : ℂ | (z, t) ∈ c.target ∩ c.symm ⁻¹' c'.source} := by
  let e : ℂ → ℂ × (Fin (2 * d - 2) → ℝ) := fun z ↦ (z, t)
  have he : Continuous e := continuous_id.prodMk continuous_const
  exact c.symm.continuousOn.comp he.continuousOn (by
    intro z hz
    exact hz.1)

theorem actual_invariant_section_flowbox_cover [T2Space M] [SecondCountableTopology M]
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
        (∀ i j, IsOpen (overlapDomain (c i) (c j))) ∧
        (∀ i j, ContinuousOn (overlapScalar (c i) (c j)) (overlapDomain (c i) (c j))) ∧
        (∀ i j, let Ω := overlapDomain (c i) (c j)
          let h := overlapScalar (c i) (c j)
          ContinuousOn (fun p : ℂ × (Fin (2 * d - 2) → ℝ) ↦
            derivWithin (fun z ↦ h (z, p.2)) {z | (z, p.2) ∈ Ω} p.1) Ω) ∧
        (∀ i j, let Ω := overlapDomain (c i) (c j)
          let h := overlapScalar (c i) (c j)
          ContinuousOn (fun p : ℂ × (Fin (2 * d - 2) → ℝ) ↦
            derivWithin (derivWithin (fun z ↦ h (z, p.2)) {z | (z, p.2) ∈ Ω})
              {z | (z, p.2) ∈ Ω} p.1) Ω) ∧
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
  dsimp only
  obtain ⟨ιs, ιu, Ls, Lu, topS, topU, rest⟩ :=
    actual_invariant_section_flowbox_geometry f a hRank
  let := topS
  let := topU
  obtain ⟨chartS, chartU, rest⟩ := rest
  let := chartS
  let := chartU
  obtain ⟨smoothS, smoothU, rest⟩ := rest
  let := smoothS
  let := smoothU
  obtain ⟨S, U, complexChart, hcomplex, himm, hmetric, hinvS, hinvU,
    hlam, hboxes, hproducts⟩ := rest
  refine ⟨ιs, ιu, Ls, Lu, topS, topU, chartS, chartU, smoothS, smoothU,
    S, U, complexChart, hcomplex, himm, hmetric, hinvS, hinvU, hlam, ?_, hproducts⟩
  obtain ⟨n, T, c, label, branch, parametrization, hcover, htarget, hslice, hlocal⟩ := hboxes
  refine ⟨n, T, c, label, branch, parametrization, hcover, htarget, hslice,
    ?_, ?_, ?_, ?_, hlocal⟩
  · intro i j
    exact overlapDomain_isOpen
  · intro i j
    exact overlapScalar_continuousOn
  · intro i j
    exact (localBiholomorphicSlice_derivatives _ (overlapDomain_isOpen (c := c i) (c' := c j))
      _ overlapScalar_continuousOn (hlocal i j)).1
  · intro i j
    exact (localBiholomorphicSlice_derivatives _ (overlapDomain_isOpen (c := c i) (c' := c j))
      _ overlapScalar_continuousOn (hlocal i j)).2

end HolomorphicAnosov.Ghys.ActualInvariantSectionFlowboxCoverG5
