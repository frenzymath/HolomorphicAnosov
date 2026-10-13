import HolomorphicAnosov.Analysis.CompactCoefficientUpperBound
import HolomorphicAnosov.Analysis.Complex.UniformFlatCoordinate
import HolomorphicAnosov.Ghys.NativeFlowboxConnectionCoefficient
import HolomorphicAnosov.Ghys.RealMetricAffinePlaque
import HolomorphicAnosov.Geometry.CompactFlowboxSliceBuffers
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import Mathlib.Data.Fintype.Lattice

noncomputable section
open Set MeasureTheory Filter _root_.Topology Metric
open scoped ContDiff Manifold ENNReal
namespace HolomorphicAnosov.Ghys
universe u
attribute [local instance] complex_isManifold_real curveScalarToProductChartedSpace

/-- For the given compact holomorphic Anosov system and affine leaf family, there are uniform positive radii giving intrinsic injectivity and a uniform ball in the image of every normalized affine development. (Ghys, Lemmas 3.2–3.3; HPS, proof of (6.7)) -/
theorem affine_complete_uniform_intrinsic_neighborhoods
    {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {ι : Type u} (L : ι → Type u)
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin 2 → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ (L i)]
    [∀ i, ChartedSpace ℂ (L i)] [∀ i, IsManifold 𝓘(ℂ) ∞ (L i)]
    (f : Biholomorph d d M M) (a : AnosovDatum f)
    (U : HPS.LeafPartition a.splitting.unstable.toDistribution ι L (fun _ ↦ 2))
    (G : NativeInvariantJetAffineLeafFamily f a L U)
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : M ↦ TangentSpace (realModel d) x)) :
    let Develops := fun (i : ι) (D : L i → ℂ) ↦
      ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y)
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      (∀ i (D : L i → ℂ), Develops i D → ∀ u v : L i,
        intrinsicRealMetricLeafEDist g (U.leaf i).inclusion u v < ENNReal.ofReal ε →
          D u = D v → u = v) ∧
      (∀ i (p : L i) (D : L i → ℂ), Develops i D → D p = 0 →
        realMetricDevelopmentDerivativeNorm g (U.leaf i).inclusion D p = 1 →
          Metric.ball (0 : ℂ) r ⊆ Set.range D) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · let : IsEmpty M := hM
    refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_, ?_⟩
    · intro i D hD u
      exact isEmptyElim ((U.leaf i).inclusion u)
    · intro i p
      exact isEmptyElim ((U.leaf i).inclusion p)
  let : Nonempty M := hM
  let : ∀ i, T2Space (L i) := fun i ↦ (U.leaf i).hausdorff
  obtain ⟨K, _, hKcompact, hKsource, hKcover, _, _⟩ :=
    compact_flowbox_slice_buffers G.box G.box_cover
  have hbuffer (j : Fin G.boxCount) : ∃ δ : ℝ, 0 < δ ∧
      cthickening δ ((G.box j) '' K j) ⊆ (G.box j).target := by
    apply ((hKcompact j).image_of_continuousOn
      ((G.box j).continuousOn.mono (hKsource j))).exists_cthickening_subset_open
      (G.box j).open_target
    rintro _ ⟨x, hx, rfl⟩
    exact (G.box j).map_source (hKsource j hx)
  choose δ hδ hδtarget using hbuffer
  let P := fun j ↦ cthickening (δ j) ((G.box j) '' K j)
  have hPcompact (j : Fin G.boxCount) : IsCompact (P j) :=
    ((hKcompact j).image_of_continuousOn ((G.box j).continuousOn.mono (hKsource j))).cthickening
  choose A hA hAleaf using native_flowbox_connection_coefficient L f a U G
  have hC (j : Fin G.boxCount) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ P j, ‖A j p‖ ≤ C := by
    obtain ⟨C, hC, hbound⟩ := Analysis.exists_abs_upper_bound_of_isCompact
      (P j) (hPcompact j) (fun p ↦ ‖A j p‖) ((hA j).mono (hδtarget j)).norm
    exact ⟨C, hC, fun p hp ↦ by simpa only [abs_norm] using hbound p hp⟩
  choose C hC hCbound using hC
  choose m hm hmetric using fun j ↦
    native_flowbox_compact_metric_lower_bound L f a U G g j (P j) (hPcompact j) (hδtarget j)
  choose R hR hRδ hflat using fun j ↦ uniform_flat_coordinate_chart (C j) (δ j) (hC j) (hδ j)
  have hlocal (j : Fin G.boxCount) (i : ι) (p : L i)
      (hpK : (U.leaf i).inclusion p ∈ K j) (D : L i → ℂ)
      (hD : ∀ c ∈ (G.affineAtlas i).charts, ∀ x ∈ c.source,
        ∃ b : ComplexAffineTransformation, ∀ᶠ y in 𝓝 x, D y = b.apply (c y)) :
      (∀ y, intrinsicRealMetricLeafEDist g (U.leaf i).inclusion p y < ENNReal.ofReal (m j * R j) →
        D p = D y → p = y) ∧
      (D p = 0 → realMetricDevelopmentDerivativeNorm g (U.leaf i).inclusion D p = 1 →
        ball (0 : ℂ) (m j * R j / 2) ⊆ range D) := by
    have hps := hKsource j hpK
    have hpt := (G.box j).map_source hps
    let t : G.transverse j := ⟨((G.box j) ((U.leaf i).inclusion p)).2,
      G.transverse_contains j _ hpt⟩
    let z : nativeAffineFlowboxSlice (G.box j) t.val :=
      ⟨((G.box j) ((U.leaf i).inclusion p)).1, hpt⟩
    have hincl : (U.leaf (G.label j t)).inclusion (G.parametrization j t z).val =
        (U.leaf i).inclusion p := by
      rw [← G.parametrization_inclusion j t z]
      exact (G.box j).left_inv hps
    have hi : G.label j t = i := U.disjoint _ _ _ _ hincl
    clear_value t z
    subst i
    have hzmark : (G.parametrization j t z).val = p := (U.leaf _).injective hincl
    obtain ⟨c, hcmax, hcs, hct, hcf, hci, hc, hcinv⟩ :=
      native_flowbox_real_chart f a L U G j t z
    have hzt : z.val ∈ c.target := by rw [hct]; exact z.property
    have hcp : c.symm z.val = p := (hci z).trans hzmark
    have hp : p ∈ c.source := hcp ▸ c.map_target hzt
    have hcz : c p = z.val := by rw [← hcp]; exact c.right_inv hzt
    have hzbase : (G.box j) ((U.leaf (G.label j t)).inclusion p) = (z.val,t.val) := by
      rw [← hincl, ← G.parametrization_inclusion j t z]
      exact (G.box j).right_inv z.property
    have hdisc (w : ℂ) (hw : w ∈ closedBall z.val (δ j)) : (w,t.val) ∈ P j := by
      apply closedBall_subset_cthickening (mem_image_of_mem (G.box j) hpK) (δ j)
      change dist (w,t.val) ((G.box j) ((U.leaf (G.label j t)).inclusion p)) ≤ δ j
      rw [hzbase, dist_prod_same_right]
      exact hw
    have hcbuffer : closedBall z.val (δ j) ⊆ c.target := by
      intro w hw
      rw [hct]
      exact hδtarget j (hdisc w hw)
    obtain ⟨B, hB, hBA, hgraph⟩ := hAleaf j t ⟨c,hcmax⟩ hct hci hcf
    obtain ⟨e, hes, hea, he'a, he, hei, himage, hODE⟩ := hflat j z.val B
      (hB.mono (ball_subset_closedBall.trans hcbuffer))
      (fun w hw ↦ by
        rw [hBA w (hcbuffer (ball_subset_closedBall hw))]
        exact hCbound j _ (hdisc w (ball_subset_closedBall hw)))
    have haff := native_connection_ode_chart_affine L f a U G (G.label j t)
      ⟨c,hcmax⟩ B hgraph e he hei hODE
    apply real_metric_affine_plaque_criterion g (U.leaf (G.label j t)).inclusion
      (G.affineAtlas (G.label j t)) c hc z.val (δ j) (R j) (m j)
      (hR j) (hRδ j) (hm j) hcbuffer ?_ e hes hea he'a he himage haff hp hcz D hD
    intro x hx hxd v
    have hxt : c x ∈ c.target := c.map_source hx
    let w : nativeAffineFlowboxSlice (G.box j) t.val := ⟨c x, by rwa [hct] at hxt⟩
    have hbase : (G.box j).symm (c x,t.val) = (U.leaf (G.label j t)).inclusion x := by
      rw [G.parametrization_inclusion j t w, ← hci w]
      exact congrArg (U.leaf (G.label j t)).inclusion (c.left_inv hx)
    have hder := native_flowbox_chart_derivative_identity L f a U G j t c hct hci hc hx v
    have hb := hmetric j (c x,t.val) (hdisc _ (ball_subset_closedBall hxd))
      ((tangentSpaceCastModel 𝓘(ℝ, ℂ) (c x)) (mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, ℂ) c x v))
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hb
    rw [hder] at hb
    rw [hbase] at hb
    exact hb
  obtain ⟨j₀, _⟩ := G.box_cover (Classical.choice (inferInstance : Nonempty M))
  let : Nonempty (Fin G.boxCount) := ⟨j₀⟩
  obtain ⟨jmin, hmin⟩ := Finite.exists_min (fun j ↦ m j * R j / 2)
  have hpos : 0 < m jmin * R jmin / 2 := div_pos (mul_pos (hm _) (hR _)) (by norm_num)
  refine ⟨m jmin * R jmin / 2, m jmin * R jmin / 2, hpos, hpos, ?_, ?_⟩
  · intro i D hD u v hd hDv
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hKcover (mem_univ ((U.leaf i).inclusion u)))
    apply (hlocal j i u (interior_subset hj) D hD).1 v _ hDv
    apply hd.trans_le (ENNReal.ofReal_le_ofReal _)
    exact (hmin j).trans (by nlinarith [mul_pos (hm j) (hR j)])
  · intro i p D hD hDp hnorm
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hKcover (mem_univ ((U.leaf i).inclusion p)))
    exact (ball_subset_ball (hmin j)).trans ((hlocal j i p (interior_subset hj) D hD).2 hDp hnorm)

end HolomorphicAnosov.Ghys
