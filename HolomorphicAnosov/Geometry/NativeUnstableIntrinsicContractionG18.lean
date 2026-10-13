import HolomorphicAnosov.Geometry.NativePlaqueIntrinsicPathBoundsLowerG18
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas
import HolomorphicAnosov.Geometry.HermitianLeafPathMap
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.Manifold.Diffeomorph.RealIterate

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter
open scoped Topology
open scoped ContDiff Manifold ENNReal
attribute [local instance] complex_isManifold_real
universe u
/-- Inverse unstable derivative bounds imply contraction of the intrinsic Hermitian path distance on
native unstable leaves. (Ghys, Prop. 2.2, p. 590) -/
theorem native_unstable_intrinsic_contraction
    {d : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (f : Biholomorph d d M M) (Pu : RealTangentDistribution (realModel d) M)
    (x y : M) (N : NativeUnstableAsymptoticLeafDatum (realModel d) f.toHomeomorph Pu x)
    (N' : NativeUnstableAsymptoticLeafDatum (realModel d) f.toHomeomorph Pu y)
    (h : HermitianTangentMetricCore d M) (n : ℕ) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ z (v : TangentSpace (realModel d) z), v ∈ Pu z →
      Real.sqrt (hermitianTangentRealPairing h ((f.symm^[n]) z)
        (mfderiv (realModel d) (realModel d) (f.symm^[n]) z v)
        (mfderiv (realModel d) (realModel d) (f.symm^[n]) z v)) ≤
        c * Real.sqrt (hermitianTangentRealPairing h z v v)) :
    letI := N.topology
    letI := N.charts
    letI := N'.topology
    letI := N'.charts
    ∀ e : Diffeomorph 𝓘(ℝ, Fin N.rank → ℝ) 𝓘(ℝ, Fin N'.rank → ℝ)
      (UnstableAsymptoticLeaf f.toHomeomorph x) (UnstableAsymptoticLeaf f.toHomeomorph y) ∞,
      (∀ z, (e z).val = (f.symm^[n]) z.val) → ∀ z w,
        intrinsicHermitianLeafEDist (r := N'.rank) Subtype.val h (e z) (e w) ≤
          ENNReal.ofReal c * intrinsicHermitianLeafEDist (r := N.rank) Subtype.val h z w := by
  let := N.topology
  let := N.charts
  let := N'.topology
  let := N'.charts
  let := N.smoothAtlas
  let := N'.smoothAtlas
  intro e he z w
  apply IntrinsicPiecewiseC1Path.map_edist_le e (e.contMDiff.of_le (by simp))
    Subtype.val Subtype.val h c hc
  apply IntrinsicPiecewiseC1Path.norm_bound_of_ambient e (e.contMDiff.of_le (by simp))
    Subtype.val Subtype.val (N.inclusion_smooth.of_le (by simp))
    (N'.inclusion_smooth.of_le (by simp)) (f.symm^[n])
    ((f.toReal.symm.contMDiff.iterate n).of_le (by simp)) (funext he) h c
  intro z v
  apply hbound
  rw [← N.tangent_image z]
  exact ⟨v, rfl⟩

/-- Sufficiently small intrinsic distance controls chart-coordinate distance uniformly near a
compact subset of the chart source. -/
theorem compact_chart_error_g18 {X Y : Type*} [EMetricSpace X] [PseudoMetricSpace Y]
    (e : OpenPartialHomeomorph X Y) (K : Set X) (hK : IsCompact K)
    (hKs : K ⊆ e.source) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y, edist x y ≤ ENNReal.ofReal δ →
      y ∈ e.source ∧ dist (e y) (e x) < ε := by
  let U (x : X) (_hx : x ∈ K) := e.source ∩ e ⁻¹' Metric.ball (e x) (ε / 2)
  have hU (x : X) (hx : x ∈ K) : U x hx ∈ 𝓝 x :=
    inter_mem (e.open_source.mem_nhds (hKs hx))
      ((e.continuousAt (hKs hx)).preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε)))
  obtain ⟨δ,hδ,hcover⟩ := uniformity_basis_edist_nnreal.lebesgue_number_lemma_nhds' hK hU
  refine ⟨(δ : ℝ) / 2,half_pos (by exact_mod_cast hδ),?_⟩
  intro x hx y hxy
  obtain ⟨z,hz⟩ := hcover x hx
  have hxx : x ∈ UniformSpace.ball x {p : X × X | edist p.1 p.2 < (δ : ENNReal)} := by
    simpa [UniformSpace.ball] using (show (0 : ENNReal) < δ by exact_mod_cast hδ)
  have hyy : y ∈ UniformSpace.ball x {p : X × X | edist p.1 p.2 < (δ : ENNReal)} := by
    change edist x y < (δ : ENNReal)
    apply hxy.trans_lt
    have hdreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_lt_ofReal_iff hdreal).mpr (half_lt_self hdreal)
  have hxU := hz hxx
  have hyU := hz hyy
  refine ⟨hyU.1,?_⟩
  have hxE : dist (e x) (e z.val) < ε / 2 := hxU.2
  have hyE : dist (e y) (e z.val) < ε / 2 := hyU.2
  calc
    dist (e y) (e x) ≤ dist (e y) (e z.val) + dist (e z.val) (e x) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hyE (by simpa only [dist_comm] using hxE)
    _ = ε := add_halves ε

/-- The intrinsic Hermitian path distance controls chart-coordinate distance uniformly near a
compact subset of the chart source. (Lee, Ch. 11) -/
theorem intrinsic_compact_chart_error_g18
    {r d : ℕ} {Z M : Type*} [TopologicalSpace Z] [T2Space Z]
    [ChartedSpace (Fin r → ℝ) Z] [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ Z]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (inc : Z → M) (hinc : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) ∞ inc)
    (hi : ∀ z, Function.Injective (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) inc z))
    {Y : Type*} [PseudoMetricSpace Y] (e : OpenPartialHomeomorph Z Y)
    (K : Set Z) (hK : IsCompact K) (hKs : K ⊆ e.source) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y,
      intrinsicHermitianLeafEDist (r := r) inc h x y ≤ ENNReal.ofReal δ →
        y ∈ e.source ∧ dist (e y) (e x) < ε := by
  obtain ⟨em,hem,hedist⟩ := hermitian_pullback_emetric h hh inc hinc hi
  let : EMetricSpace Z := em.replaceTopology hem.symm
  obtain ⟨δ,hδ,hbound⟩ := compact_chart_error_g18 e K hK hKs ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx y hxy
  apply hbound x hx y
  change @edist Z em.toEDist x y ≤ _
  rw [hedist]
  exact hxy

end HolomorphicAnosov.Ghys


