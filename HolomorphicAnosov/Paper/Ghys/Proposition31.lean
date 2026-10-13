import HolomorphicAnosov.Analysis.Complex.AnchoredUnivalentContinuity
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.Complex.NormalizedUnivalentCompactness
import HolomorphicAnosov.Ghys.AffineCompleteDevelopingContinuation
import HolomorphicAnosov.Ghys.AffineCompleteness
import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Ghys.JetAffineEquivalence
import HolomorphicAnosov.Paper.Ghys.InvariantJetSection
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.StableFoliations
import HolomorphicAnosov.Paper.Ghys.Proposition31NativePresentation
import HolomorphicAnosov.Paper.Ghys.Proposition31AffineFamily
import HolomorphicAnosov.Ghys.AnosovIntrinsicFoliationPresentation
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne

/-! The unstable curves carry a unique invariant affine family continuous along stable holonomy,
with complete leaf structures. (Ghys, Prop.3.1 and Lemmas 3.2–3.3) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real

/-- A positive iterate of a uniformly continuous map has the same forward asymptotic relation as the
map. -/
theorem forwardAsymptotic_iterate_iff
    {X : Type*} [MetricSpace X] {f : X → X} (hf : UniformContinuous f)
    {N : ℕ} (hN : 0 < N) (x y : X) :
    ForwardAsymptotic (f^[N]) x y ↔ ForwardAsymptotic f x y := by
  constructor
  · intro h
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hres : ∀ r : Fin N, ∀ᶠ n : ℕ in atTop,
        dist ((f^[r.val]) (((f^[N])^[n]) y))
          ((f^[r.val]) (((f^[N])^[n]) x)) < ε := by
      intro r
      obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp
        (UniformContinuous.iterate f r.val hf) ε hε
      have htail := Metric.tendsto_nhds.mp h δ hδ
      filter_upwards [htail] with n hn
      apply hclose
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hn
    obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_all.mpr hres)
    refine ⟨N * K, fun n hn ↦ ?_⟩
    have hbound : K ≤ n / N := (Nat.le_div_iff_mul_le hN).mpr
      (by simpa only [Nat.mul_comm] using hn)
    have hclose := hK (n / N) hbound ⟨n % N, Nat.mod_lt n hN⟩
    simpa only [← Function.iterate_mul, ← Function.iterate_add_apply,
      Nat.mod_add_div, Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hclose
  · intro h
    have hsub : Tendsto (fun n : ℕ ↦ N * n) atTop atTop := by
      refine tendsto_atTop.mpr fun b ↦ eventually_atTop.mpr ⟨b, fun n hn ↦ ?_⟩
      exact hn.trans (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hN)
    simpa only [ForwardAsymptotic, Function.comp_def, Function.iterate_mul] using h.comp hsub

/-- A positive iterate of a continuous map on a compact metric space has the same forward asymptotic
relation as the map. -/
theorem forwardAsymptotic_iterate_iff_of_compact
    {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → X} (hf : Continuous f)
    {N : ℕ} (hN : 0 < N) (x y : X) :
    ForwardAsymptotic (f^[N]) x y ↔ ForwardAsymptotic f x y :=
  forwardAsymptotic_iterate_iff (CompactSpace.uniformContinuous_of_continuous hf) hN x y

/-- Two points are forward asymptotic if and only if their images under the map are forward
asymptotic. -/
theorem forwardAsymptotic_map_iff
    {X : Type*} [MetricSpace X] (f : X → X) (x y : X) :
    ForwardAsymptotic f (f x) (f y) ↔ ForwardAsymptotic f x y := by
  simpa only [ForwardAsymptotic, Function.iterate_succ_apply] using
    (tendsto_add_atTop_iff_nat
      (f := fun n : ℕ ↦ dist ((f^[n]) y) ((f^[n]) x)) (l := 𝓝 0) 1)

/-- The permutation of connected components induced by a homeomorphism. -/
private def proposition31_component_perm
    {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) : Equiv.Perm (ConnectedComponents X) where
  toFun := f.continuous.connectedComponentsMap
  invFun := f.symm.continuous.connectedComponentsMap
  left_inv := by
    intro q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    simp only [Continuous.connectedComponentsMap_mk, f.symm_apply_apply]
  right_inv := by
    intro q
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    simp only [Continuous.connectedComponentsMap_mk, f.apply_symm_apply]

/-- A homeomorphism of a compact locally connected space has a positive iterate preserving every
connected component. (Ghys, Prop.3.1 p.590) -/
theorem proposition31_exists_component_preserving_iterate
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    (f : X ≃ₜ X) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : X,
      connectedComponent (((f : X → X)^[N]) x) = connectedComponent x := by
  let e := proposition31_component_perm f
  obtain ⟨N, hN, hpow⟩ := (isOfFinOrder_of_finite e).exists_pow_eq_one
  refine ⟨N, hN, fun x ↦ ConnectedComponents.coe_eq_coe.mp ?_⟩
  have hsem : Function.Semiconj ConnectedComponents.mk (f : X → X) e := fun _ ↦ rfl
  calc
    ConnectedComponents.mk (((f : X → X)^[N]) x) =
        (e^[N]) (ConnectedComponents.mk x) := hsem.iterate_right N x
    _ = ConnectedComponents.mk x := by rw [← Equiv.Perm.coe_pow, hpow]; rfl

/-- Forward asymptotic points for a homeomorphism of a compact locally connected metric space lie in
the same connected component. -/
theorem proposition31_forwardAsymptotic_same_component
    {X : Type*} [MetricSpace X] [CompactSpace X] [LocallyConnectedSpace X]
    (f : X ≃ₜ X) {x y : X} (h : ForwardAsymptotic (f : X → X) x y) :
    connectedComponent x = connectedComponent y := by
  obtain ⟨z, φ, hφ, hz⟩ := CompactSpace.tendsto_subseq
    (fun n : ℕ ↦ ((f : X → X)^[n]) x)
  have hyz : Tendsto (fun k : ℕ ↦ ((f : X → X)^[φ k]) y) atTop (𝓝 z) :=
    hz.congr_dist (by
      simpa only [ForwardAsymptotic, Function.comp_def, dist_comm] using h.comp hφ.tendsto_atTop)
  have hnhds : connectedComponent z ∈ 𝓝 z :=
    isOpen_connectedComponent.mem_nhds mem_connectedComponent
  obtain ⟨k, hxk, hyk⟩ := (hz.eventually hnhds |>.and (hyz.eventually hnhds)).exists
  have heq : ConnectedComponents.mk (((f : X → X)^[φ k]) x) =
      ConnectedComponents.mk (((f : X → X)^[φ k]) y) :=
    (ConnectedComponents.coe_eq_coe'.mpr hxk).trans
      (ConnectedComponents.coe_eq_coe'.mpr hyk).symm
  let e := proposition31_component_perm f
  have hsem : Function.Semiconj ConnectedComponents.mk (f : X → X) e := fun _ ↦ rfl
  rw [hsem.iterate_right (φ k) x, hsem.iterate_right (φ k) y] at heq
  exact ConnectedComponents.coe_eq_coe.mp ((e.injective.iterate (φ k)) heq)

/-- A biholomorphism of a compact complex manifold has a positive iterate preserving every connected
component. (Ghys, Prop.3.1 p.590) -/
theorem proposition31_complex_component_preserving_iterate
    {d : ℕ} {M : Type u} [TopologicalSpace M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] (f : Biholomorph d d M M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : M,
      connectedComponent (((f : M → M)^[N]) x) = connectedComponent x := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (ComplexModel d) M
  exact proposition31_exists_component_preserving_iterate f.toHomeomorph

namespace AnosovIntrinsicFoliationPresentation

variable {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]
  {f : Biholomorph d d M M} {a : AnosovDatum f}
  (P : AnosovIntrinsicFoliationPresentation f a)

/-- The Anosov map preserves the stable equivalence relation in both directions. (Ghys, §2
pp.588–589) -/
theorem stablePartition_map_iff (x y : M) :
    letI := P.realCharts
    P.foliations.stablePartition (f x) (f y) ↔ P.foliations.stablePartition x y := by
  let := P.realCharts
  rw [P.stable_asymptotic, P.stable_asymptotic]
  exact @forwardAsymptotic_map_iff M P.metric (f : M → M) x y

/-- The Anosov map preserves the unstable equivalence relation in both directions. (Ghys, §2
pp.588–589) -/
theorem unstablePartition_map_iff (x y : M) :
    letI := P.realCharts
    P.foliations.unstablePartition (f x) (f y) ↔ P.foliations.unstablePartition x y := by
  let := P.realCharts
  rw [P.unstable_asymptotic, P.unstable_asymptotic]
  simpa using (@forwardAsymptotic_map_iff M P.metric (f.symm : M → M) (f x) (f y)).symm

/-- The bijection from the unstable leaf through `x` to the unstable leaf through `f x` induced by
`f`. (Ghys, Prop.3.1(i) p.590) -/
def unstableLeafEquiv (x : M) :
    letI := P.realCharts
    P.foliations.ULeaf x ≃ P.foliations.ULeaf (f x) := by
  letI := P.realCharts
  refine Equiv.subtypeEquiv f.toEquiv fun y ↦ ?_
  change Quotient.mk P.foliations.unstablePartition y =
      Quotient.mk P.foliations.unstablePartition x ↔
    Quotient.mk P.foliations.unstablePartition (f y) =
      Quotient.mk P.foliations.unstablePartition (f x)
  rw [Quotient.eq, Quotient.eq]
  exact (P.unstablePartition_map_iff y x).symm

/-- The unstable-leaf bijection sends each ambient point `y` to `f y`. -/
theorem unstableLeafEquiv_apply_val (x : M) :
    letI := P.realCharts
    ∀ y : P.foliations.ULeaf x, (P.unstableLeafEquiv x y).val = f y.val := by
  intro y
  rfl

/-- The inverse unstable-leaf bijection sends each ambient point `y` to `f.symm y`. -/
theorem unstableLeafEquiv_symm_apply_val (x : M) :
    letI := P.realCharts
    ∀ y : P.foliations.ULeaf (f x), ((P.unstableLeafEquiv x).symm y).val = f.symm y.val := by
  intro y
  rfl

end AnosovIntrinsicFoliationPresentation

/-! Affine structures are determined by their maximal compatible scalar atlases. -/

/-- Two affine structures with the same maximal compatible scalar atlas are equal. -/
theorem affine_structure_eq_of_maximalAtlas_eq
    {L : Type u} [TopologicalSpace L] [ChartedSpace (ComplexModel 1) L]
    (A B : ComplexAffineStructure L)
    (hMax : ComplexAffineStructure.maximalAtlas L A =
      ComplexAffineStructure.maximalAtlas L B) :
    A = B := by
  have hAB : AffineAtlasesEquivalent L A.out B.out := by
    intro c hc d hd
    have hcA : c ∈ ComplexAffineStructure.maximalAtlas L A := by
      refine ⟨A.out.holomorphic c hc, ?_⟩
      intro e he
      exact A.out.compatible e he c hc
    have hcB : c ∈ ComplexAffineStructure.maximalAtlas L B := by
      rw [← hMax]
      exact hcA
    obtain ⟨_, hcd⟩ := hcB
    intro x hx
    obtain ⟨a, ha⟩ := hcd d hd x ⟨hx.2, hx.1⟩
    refine ⟨⟨a.slope⁻¹, inv_ne_zero a.slope_ne_zero,
        -a.slope⁻¹ * a.translation⟩, ?_⟩
    filter_upwards [ha] with y hy
    dsimp [ComplexAffineTransformation.apply] at hy ⊢
    rw [hy]
    field_simp [a.slope_ne_zero]
    ring
  exact (Quotient.out_eq A).symm.trans
    ((Quotient.sound hAB).trans (Quotient.out_eq B))

/-- A holomorphic Anosov map with complex unstable rank one admits an intrinsic foliation
presentation and a unique affine family invariant under the map and continuous in affine ratios
along stable paths. Every affine leaf structure in this family is complete. (Ghys, Prop.3.1
pp.590–593) -/
theorem proposition_3_1
    {d : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (hRank : HasComplexRankOne a.splitting.unstable.toDistribution) :
    ∃ P : AnosovIntrinsicFoliationPresentation f a,
      letI := P.realCharts
      ∃ A : AffineUnstableLeafStructures P.foliations P.complexLeaves,
        A.ActsAffinely P.foliations P.complexLeaves f ∧
        A.ContinuousAlongStableHolonomy P.foliations P.complexLeaves ∧
        (∀ B : AffineUnstableLeafStructures P.foliations P.complexLeaves,
          B.ActsAffinely P.foliations P.complexLeaves f →
          B.ContinuousAlongStableHolonomy P.foliations P.complexLeaves → B = A) ∧
        (∀ q : Quotient P.foliations.unstablePartition,
          letI := P.foliations.unstableTopology q
          letI := P.complexLeaves.charts q
          ComplexAffineStructure.Complete
            (IntrinsicFoliationLeaf P.foliations.unstablePartition q) (A.structureAt q)) := by
  classical
  rcases isEmpty_or_nonempty M with hEmpty | hNonempty
  · let := hEmpty
    let realCharts : ChartedSpace (Fin ((2*d-2)+2) → ℝ) M :=
      ChartedSpace.empty _ _
    let F : TransverseContinuousFoliations.{u, u} (2*d-2) 2 M := {
      boxIndex := PEmpty
      box := fun i ↦ isEmptyElim i
      cover := fun x ↦ isEmptyElim x
      stablePartition := ⊥
      unstablePartition := ⊥
      stable_generated := fun x ↦ isEmptyElim x
      unstable_generated := fun x ↦ isEmptyElim x
      stableTopology := fun q ↦ isEmptyElim q
      unstableTopology := fun q ↦ isEmptyElim q
      stableCharts := fun q ↦ isEmptyElim q
      unstableCharts := fun q ↦ isEmptyElim q
      stable_connected := fun q ↦ isEmptyElim q
      unstable_connected := fun q ↦ isEmptyElim q
      stable_inclusion := fun q ↦ isEmptyElim q
      unstable_inclusion := fun q ↦ isEmptyElim q
      stableLabel := fun i ↦ isEmptyElim i
      unstableLabel := fun i ↦ isEmptyElim i
      stable_label := fun i ↦ isEmptyElim i
      unstable_label := fun i ↦ isEmptyElim i
      stable_plaque := fun i ↦ isEmptyElim i
      unstable_plaque := fun i ↦ isEmptyElim i
      stable_topology_generated := fun q ↦ isEmptyElim q
      unstable_topology_generated := fun q ↦ isEmptyElim q }
    let C : IntrinsicComplexUnstableLeaves F := {
      real_dimension := rfl
      charts := fun q ↦ isEmptyElim q
      complex_manifold := fun q ↦ isEmptyElim q }
    let P : AnosovIntrinsicFoliationPresentation f a := {
      realCharts := realCharts
      foliations := F
      complexLeaves := C
      metric := MetricSpace.induced (isEmptyElim : M → Empty) (by
        intro x
        exact isEmptyElim x) inferInstance
      metric_topology := Subsingleton.elim _ _
      stable_asymptotic := fun x ↦ isEmptyElim x
      unstable_asymptotic := fun x ↦ isEmptyElim x
      stableSmooth := fun q ↦ isEmptyElim q
      unstableSmooth := fun q ↦ isEmptyElim q
      stableNative := fun q ↦ isEmptyElim q
      unstableNative := fun q ↦ isEmptyElim q
      stable_inclusion_eq := fun q ↦ isEmptyElim q
      unstable_inclusion_eq := fun q ↦ isEmptyElim q
      unstable_real_complex_compatible := fun q ↦ isEmptyElim q
      unstable_holomorphic := fun q ↦ isEmptyElim q }
    let A : AffineUnstableLeafStructures F C := {
      structureAt := fun q ↦ isEmptyElim q }
    refine ⟨P, A, ?_, ?_, ?_, ?_⟩
    · intro x
      exact isEmptyElim x
    · intro q
      exact isEmptyElim q
    · intro B _ _
      cases B with
      | mk b =>
        have hb : b = A.structureAt := funext fun q ↦ isEmptyElim q
        cases hb
        rfl
    · intro q
      exact isEmptyElim q
  · let := hNonempty
    obtain ⟨N, hN, hcomponent⟩ := proposition31_complex_component_preserving_iterate f
    
    
    
    
    have hNpos : 0 < N := hN
    have hcomponent_fixed : ∀ x : M,
        connectedComponent (((f : M → M)^[N]) x) = connectedComponent x := hcomponent
    clear hNpos hcomponent_fixed
    obtain ⟨P, _hP⟩ := proposition31_native_presentation f a hRank
    refine ⟨P, ?_⟩
    let := P.realCharts
    obtain ⟨A, hAact, hAcont, hAuniq, hAcomplete⟩ :=
      proposition31_affine_family f a hRank P
    exact ⟨A, hAact, hAcont, hAuniq, hAcomplete⟩


end HolomorphicAnosov.Ghys
