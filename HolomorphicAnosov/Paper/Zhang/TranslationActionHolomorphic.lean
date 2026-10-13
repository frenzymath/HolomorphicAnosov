import HolomorphicAnosov.Analysis.HolomorphicMapCompactLimit
import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.ComplexCoverPullbackAtlas
import HolomorphicAnosov.Geometry.HolomorphicGlobalLeafProduct
import HolomorphicAnosov.Paper.Zhang.LatticeProjectionDensity
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle
import HolomorphicAnosov.Geometry.RegularHolomorphicFoliation
import Mathlib.Topology.Covering.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Holomorphicity of real translations transported by a linearizing homeomorphism to the universal
cover. (Zhang, Lemma 3.2, pp. 11–12) -/

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology _root_.Topology TensorProduct

universe u v w

namespace HolomorphicAnosov

attribute [local instance] complex_isManifold_real

namespace TranslationActionSupport

variable {V : Type*} [NormedAddCommGroup V]
  {Y : Type*} [TopologicalSpace Y]

/-- The homeomorphism `x ↦ H.symm (v + H x)` obtained by transporting translation by `v` through
`H`. -/
def transported (H : Y ≃ₜ V) (v : V) : Y ≃ₜ Y :=
  (H.trans (Homeomorph.addLeft v)).trans H.symm

@[simp] theorem transported_apply (H : Y ≃ₜ V) (v : V) (y : Y) :
    transported H v y = H.symm (v + H y) := rfl

@[simp] theorem transported_zero (H : Y ≃ₜ V) (y : Y) :
    transported H 0 y = y := by simp [transported]

theorem transported_add (H : Y ≃ₜ V) (v w : V) (y : Y) :
    transported H (v + w) y = transported H v (transported H w y) := by
  simp [transported_apply, add_assoc]

theorem transported_neg_inverse (H : Y ≃ₜ V) (v : V) (y : Y) :
    transported H (-v) (transported H v y) = y := by
  simp [transported_apply]

/-- The distance between translations of the same point equals the distance between their parameters
in the metric pulled back through `H`. -/
theorem transported_dist (H : Y ≃ₜ V) (v w : V) (y : Y) :
    letI : MetricSpace Y := H.isEmbedding.comapMetricSpace H
    dist (transported H v y) (transported H w y) = dist v w := by
  change dist (H (H.symm (v + H y))) (H (H.symm (w + H y))) = dist v w
  simp

/-- Convergence of translation parameters gives uniform convergence of transported translations on
every subset in the metric pulled back through `H`. -/
theorem transported_compact_convergence (H : Y ≃ₜ V) (vSeq : ℕ → V) (v : V)
    (hv : Tendsto vSeq atTop (𝓝 v)) :
    letI : MetricSpace Y := H.isEmbedding.comapMetricSpace H
    ∀ K : Set Y, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y ∈ K,
        dist (transported H (vSeq j) y) (transported H v y) < ε := by
  let : MetricSpace Y := H.isEmbedding.comapMetricSpace H
  intro K hK ε hε
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hv) ε hε
  exact ⟨J, fun j hj y _ ↦ (transported_dist H _ _ y).trans_lt (hJ j hj)⟩

/-- Every deck homeomorphism is complex smooth in an atlas for which the covering sheets are
biholomorphic. -/
theorem deck_contMDiff {d : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    (p : Y → X)
    (hpullback : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    (δ : Y ≃ₜ Y) (hdeck : ∀ y, p (δ y) = p y) :
    ContMDiff (complexModel d) (complexModel d) ∞ δ := by
  intro y
  obtain ⟨e, hy, hep, he, hei⟩ := hpullback y
  obtain ⟨g, hδy, hgp, hg, hgi⟩ := hpullback (δ y)
  have hyeg : e y ∈ g.target := by
    rw [hep hy, ← hdeck y, ← hgp hδy]
    exact g.map_source hδy
  have hsmooth : ContMDiffAt (complexModel d) (complexModel d) ∞
      (fun z ↦ g.symm (e z)) y :=
    ((hgi _ hyeg).contMDiffAt (g.open_target.mem_nhds hyeg)).comp y
      ((he _ hy).contMDiffAt (e.open_source.mem_nhds hy))
  apply hsmooth.congr_of_eventuallyEq
  have h1 := e.open_source.mem_nhds hy
  have h2 := δ.continuous.continuousAt.preimage_mem_nhds
    (g.open_source.mem_nhds hδy)
  filter_upwards [h1, h2] with z hz hδz
  rw [hep hz, ← hdeck z, ← hgp hδz, g.left_inv hδz]

/-- A complex differentiable map between complex manifolds is complex smooth. -/
theorem contMDiff_of_mdifferentiable {d e : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel e) N]
    [IsManifold (complexModel e) ∞ N]
    {g : M → N} (hg : MDifferentiable (complexModel d) (complexModel e) g) :
    ContMDiff (complexModel d) (complexModel e) ∞ g := by
  intro x
  let k := chartAt (ComplexModel d) x
  let l := chartAt (ComplexModel e) (g x)
  let O := k.source ∩ g ⁻¹' l.source
  have hO : IsOpen O := k.open_source.inter (hg.continuous.isOpen_preimage _ l.open_source)
  have hx : x ∈ O := ⟨mem_chart_source _ _, mem_chart_source _ _⟩
  have hmaps : MapsTo g O l.source := fun _ hy ↦ hy.2
  have hd := (mdifferentiableOn_iff_of_subset_source
    (I := complexModel d) (I' := complexModel e) (x := x) (y := g x)
    (s := O) inter_subset_left hmaps).mp hg.mdifferentiableOn
  have hop : IsOpen (extChartAt (complexModel d) x '' O) := by
    simpa only [extChartAt, OpenPartialHomeomorph.extend, complexModel,
      PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
      modelWithCornersSelf_coe, Function.comp_def, id_eq, k,
      OpenPartialHomeomorph.coe_toPartialEquiv] using
      k.isOpen_image_of_subset_source hO inter_subset_left
  have hc := (complex_contDiffOn_iff_differentiableOn hop).mpr hd.2
  have hs := (contMDiffOn_iff_of_subset_source (I := complexModel d)
    (I' := complexModel e) (n := ∞) (x := x) (y := g x)
    (s := O) inter_subset_left hmaps).mpr ⟨hd.1, hc⟩
  exact (hs x hx).contMDiffAt (hO.mem_nhds hx)

/-- Complex subspaces are complementary if their realifications under a real-linear equivalence are
complementary. -/
theorem complex_isCompl_of_realification {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
    [AddCommGroup F] [Module ℝ F]
    (S U : Submodule ℂ E) (e : E ≃ₗ[ℝ] F)
    (h : IsCompl ((S.restrictScalars ℝ).map e.toLinearMap)
      ((U.restrictScalars ℝ).map e.toLinearMap)) : IsCompl S U := by
  apply (Submodule.isCompl_restrictScalars_iff (S := ℝ)).mp
  exact (Submodule.orderIsoMapComap e).isCompl_iff.mpr h

/-- A projection with biholomorphic local sheets has an invertible complex derivative at every
point. -/
theorem pullback_derivative_isInvertible {d : ℕ} {X Y : Type*}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    (p : Y → X)
    (hpullback : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target) (y : Y) :
    (mfderiv (complexModel d) (complexModel d) p y).IsInvertible := by
  obtain ⟨e, hy, hep, he, hei⟩ := hpullback y
  have hs : e.MDifferentiable (complexModel d) (complexModel d) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hEq : p =ᶠ[𝓝 y] e := by
    filter_upwards [e.open_source.mem_nhds hy] with z hz
    exact (hep hz).symm
  rw [hEq.mfderiv_eq]
  exact ⟨hs.mfderiv hy, rfl⟩

/-- A bijective linear map reflects complementarity of subspaces. -/
theorem isCompl_of_image_isCompl {K E F : Type*} [Field K]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    (L : E →ₗ[K] F) (hL : Function.Bijective L)
    (S U : Submodule K E) (h : IsCompl (S.map L) (U.map L)) :
    IsCompl S U := by
  exact (Submodule.orderIsoMapComap (LinearEquiv.ofBijective L hL)).isCompl_iff.mpr h

/-- In holomorphic product coordinates adapted to complementary real subspaces, projecting a deck
translation onto the first subspace gives a holomorphic transported translation. -/
theorem projected_translation_contMDiff {d a b : ℕ} {M L K : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace L] [ChartedSpace (ComplexModel a) L]
    [TopologicalSpace K] [ChartedSpace (ComplexModel b) K]
    [NormedSpace ℝ V]
    (R : Diffeomorph (complexModel d) ((complexModel a).prod (complexModel b))
      M (L × K) ∞) (H : M ≃ₜ V)
    (Vs Vu : Submodule ℝ V) (hcompl : IsCompl Vs Vu)
    (hs : L → V) (hu : K → V)
    (hs_mem : ∀ z, hs z ∈ Vs) (hu_mem : ∀ z, hu z ∈ Vu)
    (hlinear : ∀ z : L × K, H (R.symm z) = hs z.1 + hu z.2)
    (u0 : K) (hu0 : hu u0 = 0)
    (δ : M ≃ₜ M) (hδ : ContMDiff (complexModel d) (complexModel d) ∞ δ)
    (γ : V) (hδlinear : ∀ y, H (δ y) = γ + H y) :
    ContMDiff (complexModel d) (complexModel d) ∞
      (transported H ((Vs.projectionOnto Vu hcompl γ : Vs) : V)) := by
  let ps := Vs.projectionOnto Vu hcompl
  let ρ : L → L := fun z ↦ (R (δ (R.symm (z, u0)))).1
  have hρ : ContMDiff (complexModel a) (complexModel a) ∞ ρ :=
    (R.contMDiff.comp hδ |>.comp (R.symm.contMDiff.comp
      (contMDiff_id.prodMk contMDiff_const))).fst
  have hproj (y : M) : (ps (H y) : V) = hs (R y).1 := by
    have h := hlinear (R y)
    rw [R.symm_apply_apply] at h
    rw [h, map_add, Submodule.projectionOnto_apply_of_mem_left _ (hs_mem _),
      Submodule.projectionOnto_apply_of_mem_right _ (hu_mem _)]
    simp
  have hrho (z : L) : hs (ρ z) = (ps γ : V) + hs z := by
    rw [← hproj, hδlinear, map_add, hlinear]
    simp only [hu0, add_zero]
    rw [show ps (hs z) = ⟨hs z, hs_mem z⟩ from
      Submodule.projectionOnto_apply_of_mem_left hcompl (hs_mem z)]
    rfl
  have hmap : (transported H ((ps γ : Vs) : V) : M → M) =
      fun y ↦ R.symm (ρ (R y).1, (R y).2) := by
    funext y
    apply H.injective
    rw [transported_apply, H.apply_symm_apply, hlinear, hrho]
    have h := hlinear (R y)
    rw [R.symm_apply_apply] at h
    rw [h]
    abel
  rw [hmap]
  exact R.symm.contMDiff.comp ((hρ.comp R.contMDiff.fst).prodMk R.contMDiff.snd)

/-- Holomorphicity of transported translations on a dense set of parameters implies holomorphicity
for every parameter in the subspace. -/
theorem dense_translations_contMDiff {d : ℕ}
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (ComplexModel d) Y] [IsManifold (complexModel d) ∞ Y]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {I : Type*} (H : Y ≃ₜ V) (T : Submodule ℝ V) (q : I → T)
    (hDense : DenseRange q)
    (hhol : ∀ i, ContMDiff (complexModel d) (complexModel d) ∞
      (transported H (q i : V))) (a : T) :
    ContMDiff (complexModel d) (complexModel d) ∞ (transported H (a : V)) := by
  classical
  let : MetricSpace Y := H.isEmbedding.comapMetricSpace H
  obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp (hDense a)
  choose i hi using hz
  have ht : Tendsto (fun n ↦ (q (i n) : V)) atTop (𝓝 (a : V)) := by
    have hv := continuous_subtype_val.continuousAt.tendsto.comp hzt
    have heq : (fun n ↦ (q (i n) : V)) = Subtype.val ∘ z := by
      funext n
      exact congrArg Subtype.val (hi n)
    rw [heq]
    exact hv
  apply contMDiff_of_mdifferentiable
  apply holomorphic_map_compact_limit (fun n ↦ transported H (q (i n) : V))
    (transported H (a : V))
  · intro n
    exact (hhol (i n)).mdifferentiable (by simp)
  · exact (transported H (a : V)).continuous
  · exact transported_compact_convergence H (fun n ↦ (q (i n) : V)) (a : V) ht

/-- The projections of a full invariant lattice onto the stable and unstable decay subspaces of a
hyperbolic linear map have dense range. -/
theorem lattice_projection_dense_given_spaces {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (hfull : Submodule.span ℝ (Γ : Set V) = ⊤)
    (A : V ≃L[ℝ] V) (hAΓ : A '' (Γ : Set V) = (Γ : Set V))
    (hhyper : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1)
    (Vs Vu : Submodule ℝ V) (hcompl : IsCompl Vs Vu)
    (hs : ∀ v, v ∈ Vs ↔ Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0))
    (hu : ∀ v, v ∈ Vu ↔ Tendsto (fun n : ℕ ↦ (A.symm ^ n) v) atTop (𝓝 0)) :
    DenseRange (fun γ : Γ ↦ Vs.projectionOnto Vu hcompl γ) ∧
    DenseRange (fun γ : Γ ↦ Vu.projectionOnto Vs hcompl.symm γ) := by
  let decay : (V ≃L[ℝ] V) → Submodule ℝ V := fun B ↦ {
    carrier := {v | Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 0)}
    zero_mem' := by simp
    add_mem' := by
      intro v w hv hw
      simpa only [Set.mem_ofPred_eq, map_add, add_zero] using hv.add hw
    smul_mem' := by
      intro a v hv
      simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hv.const_smul a }
  have hDs : decay A = Vs := by ext v; exact (hs v).symm
  have hDu : decay A.symm = Vu := by ext v; exact (hu v).symm
  obtain ⟨hc, hds, hdu, _⟩ := lattice_projection_density Γ hfull A hAΓ hhyper
  have h : ∃ h : IsCompl (decay A) (decay A.symm),
      DenseRange (fun γ : Γ ↦ (decay A).projectionOnto (decay A.symm) h γ) ∧
      DenseRange (fun γ : Γ ↦ (decay A.symm).projectionOnto (decay A) h.symm γ) :=
    ⟨hc, hds, hdu⟩
  rw [hDs, hDu] at h
  obtain ⟨hc', hds', hdu'⟩ := h
  exact ⟨hds', hdu'⟩

end TranslationActionSupport

/-- Every real translation transported by the linearizing homeomorphism to the universal cover is
biholomorphic in the pulled-back complex atlas. (Zhang, Lemma 3.2, pp. 11–12) -/
theorem translation_action_holomorphic
    {d r s : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (anosov : AnosovDatum f)
    (S U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hS : IsHolomorphicTangentSubbundle r S)
    (hU : IsHolomorphicTangentSubbundle s U)
    (hSreal : ∀ x, ((S x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        anosov.splitting.stable.toDistribution x)
    (hUreal : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        anosov.splitting.unstable.toDistribution x)
    (_htorus : ∃ n : ℕ, Nonempty (X ≃ₜ UnitAddTorus (Fin n)))
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [ChartedSpace (ComplexModel d) Y] [IsManifold (complexModel d) ∞ Y]
    [SimplyConnectedSpace Y]
    (p : Y → X) (_hp : IsCoveringMap p) (_hsurj : Function.Surjective p)
    (hpullback : ∀ y : Y, ∃ e : OpenPartialHomeomorph Y X,
      y ∈ e.source ∧ Set.EqOn e p e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e e.source ∧
      ContMDiffOn (complexModel d) (complexModel d) ∞ e.symm e.target)
    {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (hfull : Submodule.span ℝ (Γ : Set V) = ⊤)
    (A : V ≃L[ℝ] V) (hAΓ : A '' (Γ : Set V) = (Γ : Set V))
    (hhyperbolic : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1)
    (F : Y ≃ₜ Y) (hF : ∀ y, p (F y) = f (p y))
    (H : Y ≃ₜ V) (_hconjugacy : ∀ y, H (F y) = A (H y))
    (deck : Γ → Y ≃ₜ Y)
    (hdeck : ∀ (γ : Γ) (y : Y), p (deck γ y) = p y)
    (hdecklinear : ∀ (γ : Γ) (y : Y), H (deck γ y) = (γ : V) + H y)
    (Vs Vu : Submodule ℝ V) (hcompl : IsCompl Vs Vu)
    (hstable : ∀ v : V, v ∈ Vs ↔
      Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0))
    (hunstable : ∀ v : V, v ∈ Vu ↔
      Tendsto (fun n : ℕ ↦ (A.symm ^ n) v) atTop (𝓝 0))
    (Ws : RegularHolomorphicFoliation.{v, v} d r s Y)
    (Wu : RegularHolomorphicFoliation.{v, v} d s r Y)
    (hWspullback : ∀ y, (Ws.tangent y).map
      (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = S (p y))
    (hWupullback : ∀ y, (Wu.tangent y).map
      (mfderiv (complexModel d) (complexModel d) p y).toLinearMap = U (p y))
    (hWsaffine : ∀ y, H '' (Set.range (fun z : Ws.Leaf y ↦ z.val)) =
      {v : V | ∃ a : Vs, v = H y + (a : V)})
    (hWuaffine : ∀ y, H '' (Set.range (fun z : Wu.Leaf y ↦ z.val)) =
      {v : V | ∃ a : Vu, v = H y + (a : V)}) :
    ∀ v : V, ∃ Φ : Biholomorph d d Y Y,
      ∀ y : Y, Φ y = H.symm (v + H y) := by
  classical
  have hcomplexcompl (x : X) : IsCompl (S x) (U x) := by
    apply TranslationActionSupport.complex_isCompl_of_realification
      (S x) (U x) (complexTangentToReal d x).toLinearEquiv
    rw [hSreal x, hUreal x]
    exact anosov.splitting.isCompl x
  have htransverse (y : Y) : IsCompl (Ws.tangent y) (Wu.tangent y) := by
    have hinv := TranslationActionSupport.pullback_derivative_isInvertible p hpullback y
    apply TranslationActionSupport.isCompl_of_image_isCompl
      (mfderiv (complexModel d) (complexModel d) p y).toLinearMap hinv.bijective
    rw [hWspullback y, hWupullback y]
    exact hcomplexcompl (p y)
  have hsleaf (y : Y) : H '' {z : Y | Ws.partition y z} =
      {v : V | v - H y ∈ Vs} := by
    have hset : Set.range (fun z : Ws.Leaf y ↦ z.val) = {z : Y | Ws.partition y z} := by
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        exact Quotient.exact a.property.symm
      · intro hz
        exact ⟨⟨z, Quotient.sound ((Ws.partition).symm hz)⟩, rfl⟩
    rw [← hset, hWsaffine y]
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro hv
      exact ⟨⟨v - H y, hv⟩, by simp⟩
  have huleaf (y : Y) : H '' {z : Y | Wu.partition y z} =
      {v : V | v - H y ∈ Vu} := by
    have hset : Set.range (fun z : Wu.Leaf y ↦ z.val) = {z : Y | Wu.partition y z} := by
      ext z
      constructor
      · rintro ⟨a, rfl⟩
        exact Quotient.exact a.property.symm
      · intro hz
        exact ⟨⟨z, Quotient.sound ((Wu.partition).symm hz)⟩, rfl⟩
    rw [← hset, hWuaffine y]
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro hv
      exact ⟨⟨v - H y, hv⟩, by simp⟩
  have hdim := Ws.dimension
  subst d
  obtain ⟨R, hRs, hRu, hRleaf, hRsunique, hRuunique, hBleaf, hBunique, hBlinear⟩ :=
    holomorphic_global_leaf_product r s Y Ws Wu V Vs Vu hcompl H hsleaf huleaf htransverse
  let o := H.symm 0
  let so : Ws.Leaf o := ⟨o, rfl⟩
  let uo : Wu.Leaf o := ⟨o, rfl⟩
  have hsmem (z : Ws.Leaf o) : H z.val ∈ Vs := by
    have hz : H z.val ∈ H '' Set.range (fun a : Ws.Leaf o ↦ a.val) :=
      ⟨z.val, ⟨z, rfl⟩, rfl⟩
    rw [hWsaffine o] at hz
    obtain ⟨a, ha⟩ := hz
    have hv : H z.val = (a : V) := by simpa [o] using ha
    rw [hv]
    exact a.property
  have humem (z : Wu.Leaf o) : H z.val ∈ Vu := by
    have hz : H z.val ∈ H '' Set.range (fun a : Wu.Leaf o ↦ a.val) :=
      ⟨z.val, ⟨z, rfl⟩, rfl⟩
    rw [hWuaffine o] at hz
    obtain ⟨a, ha⟩ := hz
    have hv : H z.val = (a : V) := by simpa [o] using ha
    rw [hv]
    exact a.property
  have hdeckSmooth (γ : Γ) : ContMDiff (complexModel (r + s))
      (complexModel (r + s)) ∞ (deck γ) :=
    TranslationActionSupport.deck_contMDiff p hpullback (deck γ) (hdeck γ)
  have hstableProjected (γ : Γ) : ContMDiff (complexModel (r + s))
      (complexModel (r + s)) ∞
      (TranslationActionSupport.transported H (Vs.projectionOnto Vu hcompl γ : V)) := by
    exact TranslationActionSupport.projected_translation_contMDiff R H Vs Vu hcompl
      (fun z : Ws.Leaf o ↦ H z.val) (fun z : Wu.Leaf o ↦ H z.val)
      hsmem humem (fun z ↦ hBlinear z.1 z.2) uo (by simp [uo, o]) (deck γ) (hdeckSmooth γ)
      γ (hdecklinear γ)
  have hunstableProjected (γ : Γ) : ContMDiff (complexModel (r + s))
      (complexModel (r + s)) ∞
      (TranslationActionSupport.transported H (Vu.projectionOnto Vs hcompl.symm γ : V)) := by
    let R' := R.trans (Diffeomorph.prodComm (complexModel r) (complexModel s)
      (Ws.Leaf o) (Wu.Leaf o) ∞)
    apply TranslationActionSupport.projected_translation_contMDiff R' H Vu Vs hcompl.symm
      (fun z : Wu.Leaf o ↦ H z.val) (fun z : Ws.Leaf o ↦ H z.val)
      humem hsmem (fun z ↦ ?_) so (by simp [so, o]) (deck γ) (hdeckSmooth γ)
      γ (hdecklinear γ)
    simpa [R', Prod.swap, add_comm] using hBlinear z.2 z.1
  have hdense := TranslationActionSupport.lattice_projection_dense_given_spaces
    Γ hfull A hAΓ hhyperbolic Vs Vu hcompl hstable hunstable
  have hstableSmooth (a : Vs) : ContMDiff (complexModel (r + s))
      (complexModel (r + s)) ∞ (TranslationActionSupport.transported H (a : V)) :=
    TranslationActionSupport.dense_translations_contMDiff H Vs
      (fun γ : Γ ↦ Vs.projectionOnto Vu hcompl γ) hdense.1 hstableProjected a
  have hunstableSmooth (a : Vu) : ContMDiff (complexModel (r + s))
      (complexModel (r + s)) ∞ (TranslationActionSupport.transported H (a : V)) :=
    TranslationActionSupport.dense_translations_contMDiff H Vu
      (fun γ : Γ ↦ Vu.projectionOnto Vs hcompl.symm γ) hdense.2 hunstableProjected a
  have hall (v : V) : ContMDiff (complexModel (r + s)) (complexModel (r + s)) ∞
      (TranslationActionSupport.transported H v) := by
    let a := Vs.projectionOnto Vu hcompl v
    let b := Vu.projectionOnto Vs hcompl.symm v
    have hv : (a : V) + (b : V) = v :=
      Submodule.projection_add_projection_eq_self hcompl v
    have hfunc : (TranslationActionSupport.transported H v : Y → Y) =
        (TranslationActionSupport.transported H (a : V)) ∘
          (TranslationActionSupport.transported H (b : V)) := by
      funext y
      change TranslationActionSupport.transported H v y =
        TranslationActionSupport.transported H (a : V)
          (TranslationActionSupport.transported H (b : V) y)
      rw [← TranslationActionSupport.transported_add, hv]
    rw [hfunc]
    exact (hstableSmooth a).comp (hunstableSmooth b)
  intro v
  let e := TranslationActionSupport.transported H v
  refine ⟨{ toEquiv := e.toEquiv
            contMDiff_toFun := hall v
            contMDiff_invFun := ?_ }, fun _ ↦ rfl⟩
  have heq : (e.symm : Y → Y) = TranslationActionSupport.transported H (-v) := by
    funext y
    apply e.injective
    simp [e, TranslationActionSupport.transported_apply]
  change ContMDiff (complexModel (r + s)) (complexModel (r + s)) ∞ (e.symm : Y → Y)
  rw [heq]
  exact hall (-v)

end HolomorphicAnosov





