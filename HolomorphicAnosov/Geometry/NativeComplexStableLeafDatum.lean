import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Geometry.NativeLeafComplexUpgrade
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousComplexTangentSubbundle

/-! This file defines complex rank-one stable-leaf families with intrinsic real and complex atlases,
asymptotic carriers, and joint continuity of local parametrizations and their first fibre
derivatives. (Zhang, §2.1–2.2, p. 3; Lemma 2.5, p. 8; Hirsch–Pugh–Shub, §6B–7, pp. 114–116;
Ghys, §2, pp. 588–589) -/

open Set Topology _root_.Topology
open scoped ContDiff Manifold

namespace HolomorphicAnosov

universe u

variable {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
  [IsManifold (complexModel d) ∞ M]

/-- The real tangent distribution obtained by realifying the complex stable subbundle. (Ghys, pp.
588–589) -/
noncomputable def complexStableRealDistribution
    (S : ContinuousComplexTangentSubbundle (complexModel d) M) :
    RealTangentDistribution (realModel d) M :=
  fun x ↦ ((S.toDistribution x).restrictScalars ℝ).map
    (complexTangentToReal d x).toLinearEquiv.toLinearMap

/-- A complex rank-one stable foliation whose leaf images are the forward asymptotic sets of their
points and whose complex atlases are compatible with their intrinsic real atlases. Local plaque
parametrizations and their first real fibre derivatives vary jointly continuously. (Zhang, p. 3;
Lemma 2.5, p. 8; Hirsch–Pugh–Shub, §6B–7, pp. 114–116; Ghys, §2, pp. 588–589) -/
structure NativeComplexStableLeafDatum (f : M ≃ₜ M)
    (S : ContinuousComplexTangentSubbundle (complexModel d) M)
    (ι : Type u) (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)] [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)] where
  partition : HPS.LeafPartition (complexStableRealDistribution S) ι L (fun _ ↦ 2)
  complexUpgrade : ∀ i,
    NativeLeafComplexUpgrade (d := d) (r := 2) 1 (partition.leaf i).inclusion
  asymptotic : ∀ i (z : L i), Set.range (partition.leaf i).inclusion =
    {y | ForwardAsymptotic f ((partition.leaf i).inclusion z) y}
  complex_tangent : ∀ i,
    letI := (complexUpgrade i).charts
    ∀ z : L i, (mfderiv (complexModel 1) (complexModel d)
      (partition.leaf i).inclusion z).range = S.toDistribution ((partition.leaf i).inclusion z)
  boxIndex : Type u
  transversal : boxIndex → Type u
  transversalTopology : ∀ b, TopologicalSpace (transversal b)
  boxes : letI := transversalTopology
    HPS.LaminationBoxes partition boxIndex (fun _ ↦ 2) transversal
  local_first_jets : ∀ p : M,
    ∃ (V : Set M) (a : OpenPartialHomeomorph M (ComplexModel d))
      (r : ℝ) (q : M → (Fin 2 → ℝ) → M),
      IsOpen V ∧ p ∈ V ∧ V ⊆ a.source ∧
      a ∈ IsManifold.maximalAtlas (complexModel d) ∞ M ∧ 0 < r ∧
      (∀ x ∈ V, q x 0 = x) ∧
      (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r, q x v ∈ a.source) ∧
      (∀ x ∈ V, ContMDiffOn 𝓘(ℝ, Fin 2 → ℝ) (realModel d) ∞
        (q x) (Metric.ball 0 r)) ∧
      (∀ x ∈ V, IsEmbedding (fun v : ↥(Metric.ball (0 : Fin 2 → ℝ) r) ↦ q x v)) ∧
      (∀ x ∈ V, ∃ (i : ι) (c : OpenPartialHomeomorph (L i) (Fin 2 → ℝ)),
        c ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i) ∧
        Metric.ball (0 : Fin 2 → ℝ) r ⊆ c.target ∧
        ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r,
          q x v = (partition.leaf i).inclusion (c.symm v)) ∧
      (∀ x ∈ V, ∀ v ∈ Metric.ball (0 : Fin 2 → ℝ) r,
        HasFDerivAt (fun w ↦ a (q x w))
          (fderiv ℝ (fun w ↦ a (q x w)) v) v) ∧
      ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦ a (q xv.1 xv.2))
        (V ×ˢ Metric.ball 0 r) ∧
      ContinuousOn (fun xv : M × (Fin 2 → ℝ) ↦
        fderiv ℝ (fun v ↦ a (q xv.1 v)) xv.2) (V ×ˢ Metric.ball 0 r)

end HolomorphicAnosov
