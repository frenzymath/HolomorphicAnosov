import HolomorphicAnosov.Analysis.Complex.FiniteGridBoundaryCancellation
import HolomorphicAnosov.Analysis.Complex.ConwayRegularClosedGridCover
import HolomorphicAnosov.Analysis.Complex.PolygonSegmentIntegralReverse
import HolomorphicAnosov.Analysis.Complex.FiniteBalancedEdgesCycles
import HolomorphicAnosov.Analysis.Complex.PolygonSegmentKernelContinuous
import Mathlib.Topology.Algebra.Module.Cardinality
import HolomorphicAnosov.Analysis.Complex.RectangleCauchyKernelIntegral

/-!
# Finite polygonal Cauchy representation

DAG node: `analysis.conway_finite_polygon_cauchy_representation`.
Source: John B. Conway, *Functions of One Complex Variable*, second edition
(1978), VIII, Proposition 1.1, pp.195–196. Lower rectangle inputs follow
Lars V. Ahlfors, *Complex Analysis*, third edition (1979), IV §1.4,
Theorem 3, pp.111–112, and IV §2.1, Lemma 2, pp.116–117.

A polygon is represented here by its finite list of successive vertices,
including the repeated closing vertex. Its oriented integral is the sum of
the real interval integrals along the affine segments, each multiplied by
its constant complex tangent. No simplicity or connectedness is assumed.
The existential contour is outside the quantification of the holomorphic
function and evaluation point. Values of the function outside U are irrelevant.
Conway prints the assertion for a region; his grid proof uses only openness
and compactness, as the natural-language proof below explains. The empty
compact case permits n=0, including when U is empty.
-/

namespace HolomorphicAnosov.Analysis.Complex

open Set

private theorem cycles_vertex_arrays {E : Type*} [Fintype E] [DecidableEq E]
    (src dst : E → ℂ) (hn : ∀ e, src e ≠ dst e)
    (hbal : ∀ v, Fintype.card {e // dst e = v} = Fintype.card {e // src e = v}) :
    ∃ (n : ℕ) (m : Fin n → ℕ) (v : ∀ j, Fin (m j + 1) → ℂ)
      (e : (j : Fin n) → Fin (m j) → E),
      (∀ j, 0 < m j) ∧ (∀ j, v j 0 = v j (Fin.last (m j))) ∧
      (∀ j k, v j k.castSucc = src (e j k) ∧ v j k.succ = dst (e j k)) ∧
      (∀ F : E → ℂ, (∑ j, ∑ k, F (e j k)) = ∑ x, F x) := by
  classical
  obtain ⟨n, c, hc, hcov⟩ := finite_balanced_edges_cycles src dst hn hbal
  let m (j : Fin n) := (c j).length
  have hm (j : Fin n) : 0 < m j := List.length_pos_iff.mpr (hc j).1
  let e (j : Fin n) (k : Fin (m j)) := (c j)[k.val]
  let v (j : Fin n) (k : Fin (m j + 1)) :=
    src ((c j)[k.val % m j]'(Nat.mod_lt _ (hm j)))
  have he (j : Fin n) (k : Fin (m j)) :
      v j k.castSucc = src (e j k) ∧ v j k.succ = dst (e j k) := by
    constructor
    · simp [v, e, Nat.mod_eq_of_lt k.isLt]
    · dsimp [v, e]
      rw [← List.next_getElem (c j) (hc j).2.1 k.val k.isLt]
      exact ((hc j).2.2 _ (List.getElem_mem _)).symm
  have hbij : Function.Bijective (fun p : (j : Fin n) × Fin (m j) ↦ e p.1 p.2) := by
    constructor
    · rintro ⟨j, k⟩ ⟨j', k'⟩ h
      have hj : j = j' := by
        obtain ⟨i, hi, hu⟩ := hcov (e j k)
        have hi₁ : e j k ∈ c j := List.getElem_mem _
        have hi₂ : e j k ∈ c j' := by simpa only [h] using (List.getElem_mem (l := c j') k'.isLt)
        exact (hu j hi₁).trans (hu j' hi₂).symm
      subst j'
      have hk : k = k' := (hc j).2.1.injective_get h
      subst k'
      rfl
    · intro x
      obtain ⟨j, hj, _⟩ := hcov x
      obtain ⟨k, hk, hx⟩ := List.mem_iff_getElem.mp hj
      exact ⟨⟨j, ⟨k, hk⟩⟩, hx⟩
  refine ⟨n, m, v, e, hm, ?_, he, ?_⟩
  · intro j
    simp [v]
  · intro F
    rw [← Fintype.sum_sigma (fun p : (j : Fin n) × Fin (m j) ↦ F (e p.1 p.2))]
    exact Fintype.sum_equiv (Equiv.ofBijective _ hbij) _ _ (fun _ ↦ rfl)

private def gridPoint (δ : ℝ) (q : ℤ × ℤ) : ℂ := ⟨δ * q.1, δ * q.2⟩
private def edgeNeighbor : Fin 4 → ℤ × ℤ := ![(0, -1), (1, 0), (0, 1), (-1, 0)]
private def edgeStart : Fin 4 → ℤ × ℤ := ![(0, 0), (1, 0), (1, 1), (0, 1)]
private def edgeEnd : Fin 4 → ℤ × ℤ := ![(1, 0), (1, 1), (0, 1), (0, 0)]
private abbrev Exposed (S : Finset (ℤ × ℤ)) :=
  (k : Fin 4) × {q // q ∈ S.filter (fun q ↦ q + edgeNeighbor k ∉ S)}
private def exposedSrc (δ : ℝ) (S : Finset (ℤ × ℤ)) (e : Exposed S) :=
  gridPoint δ (e.2.val + edgeStart e.1)
private def exposedDst (δ : ℝ) (S : Finset (ℤ × ℤ)) (e : Exposed S) :=
  gridPoint δ (e.2.val + edgeEnd e.1)

private theorem exposed_sum {A : Type*} [AddCommGroup A]
    (δ : ℝ) (S : Finset (ℤ × ℤ)) (F : ℂ → ℂ → A)
    (hF : ∀ a b, F b a = -F a b) :
    (∑ e : Exposed S, F (exposedSrc δ S e) (exposedDst δ S e)) =
      ∑ q ∈ S, ∑ k : Fin 4,
        F (gridPoint δ (q + edgeStart k)) (gridPoint δ (q + edgeEnd k)) := by
  classical
  let H (q : ℤ × ℤ) := F (gridPoint δ q) (gridPoint δ (q + (1, 0)))
  let V (q : ℤ × ℤ) := F (gridPoint δ q) (gridPoint δ (q + (0, 1)))
  have hH (q : ℤ × ℤ) :
      F (gridPoint δ (q + (1, 1))) (gridPoint δ (q + (0, 1))) =
        -H (q + (0, 1)) := by
    dsimp [H]
    have hh : q + (0, 1) + (1, 0) = q + (1, 1) := by ext <;> simp
    rw [hh, hF]
  have hV (q : ℤ × ℤ) :
      F (gridPoint δ (q + (1, 0))) (gridPoint δ (q + (1, 1))) =
        V (q + (1, 0)) := by
    dsimp [V]
    congr 2; ext <;> simp
  have hminus (q : ℤ × ℤ) : q + (0, -1) = q - (0, 1) := by (ext <;> simp); omega
  have hminus' (q : ℤ × ℤ) : q + (-1, 0) = q - (1, 0) := by (ext <;> simp); omega
  have hs : (∑ e : Exposed S, F (exposedSrc δ S e) (exposedDst δ S e)) =
      ∑ k : Fin 4, ∑ q ∈ S.filter (fun q ↦ q + edgeNeighbor k ∉ S),
        F (gridPoint δ (q + edgeStart k)) (gridPoint δ (q + edgeEnd k)) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    exact (Finset.sum_subtype _ (fun _ ↦ Iff.rfl)
      (fun q ↦ F (gridPoint δ (q + edgeStart k)) (gridPoint δ (q + edgeEnd k)))).symm
  rw [hs]
  simp only [Fin.sum_univ_four, edgeStart, edgeEnd,
    edgeNeighbor, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Fin.isValue, Prod.mk_zero_zero, add_zero, hH, hV, hminus, hminus']
  simp only [Finset.sum_neg_distrib]
  simp_rw [hF (gridPoint δ _) (gridPoint δ (_ + (0, 1)))]
  simp only [Finset.sum_neg_distrib]
  change (∑ q ∈ S.filter (fun q ↦ q - (0, 1) ∉ S), H q) +
      (∑ q ∈ S.filter (fun q ↦ q + (1, 0) ∉ S), V (q + (1, 0))) +
      -(∑ q ∈ S.filter (fun q ↦ q + (0, 1) ∉ S), H (q + (0, 1))) +
      -(∑ q ∈ S.filter (fun q ↦ q - (1, 0) ∉ S), V q) =
    ∑ q ∈ S, (H q + V (q + (1, 0)) + -H (q + (0, 1)) + -V q)
  simp only [← sub_eq_add_neg]
  rw [finite_grid_boundary_cancellation]
  abel

private theorem exposed_balanced (δ : ℝ) (S : Finset (ℤ × ℤ)) (v : ℂ) :
    Fintype.card {e : Exposed S // exposedDst δ S e = v} =
      Fintype.card {e : Exposed S // exposedSrc δ S e = v} := by
  classical
  let w (a : ℂ) : ℤ := if a = v then 1 else 0
  have h := exposed_sum δ S (fun a b ↦ w b - w a) (fun a b ↦ by abel)
  have hz : (∑ q ∈ S, ∑ k : Fin 4,
      (w (gridPoint δ (q + edgeEnd k)) - w (gridPoint δ (q + edgeStart k)))) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp only [Fin.sum_univ_four, edgeStart, edgeEnd, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
    abel
  rw [hz, Finset.sum_sub_distrib, sub_eq_zero] at h
  simpa [w, ← Fintype.card_subtype] using h

private theorem exposed_distinct (δ : ℝ) (hδ : 0 < δ) (S : Finset (ℤ × ℤ))
    (e : Exposed S) : exposedSrc δ S e ≠ exposedDst δ S e := by
  rcases e with ⟨k, q, hq⟩
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  fin_cases k <;>
    simp [exposedSrc, exposedDst, edgeStart, edgeEnd, gridPoint] at hr hi <;>
    nlinarith

private theorem grid_edge_mem (δ : ℝ) (hδ : 0 < δ) (q : ℤ × ℤ)
    (k : Fin 4) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    AffineMap.lineMap (gridPoint δ (q + edgeStart k))
      (gridPoint δ (q + edgeEnd k)) t ∈
      complexGridSquare δ q ∩ complexGridSquare δ (q + edgeNeighbor k) := by
  have hdt : 0 ≤ δ * t := mul_nonneg hδ.le ht.1
  have hdtu : δ * t ≤ δ := mul_le_of_le_one_right hδ.le ht.2
  fin_cases k <;>
    simp [Set.mem_inter_iff, complexGridSquare, gridPoint, edgeStart, edgeEnd,
      edgeNeighbor, AffineMap.lineMap_apply] <;>
    (repeat' constructor) <;> nlinarith

private noncomputable def segIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (b - a) * ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap a b t)

private theorem segIntegral_reverse (f : ℂ → ℂ) (a b : ℂ) :
    segIntegral f b a = -segIntegral f a b := polygon_segment_integral_reverse f a b

private theorem segIntegral_param (f : ℂ → ℂ) (a c : ℂ) (x y : ℝ) :
    segIntegral f (a + c * x) (a + c * y) = c * ∫ t in x..y, f (a + c * t) := by
  have hpath (t : ℝ) : AffineMap.lineMap (a + c * x) (a + c * y) t =
      a + c * (x + (y - x) * t) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul]
    ring
  have htan : a + c * y - (a + c * x) = c * ((y - x : ℝ) : ℂ) := by
    push_cast; ring
  unfold segIntegral
  simp_rw [hpath]
  rw [htan, mul_assoc]
  congr 1
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun t : ℝ ↦ f (a + c * t)) (a := 0) (b := 1) (y - x) x
  simpa [Complex.real_smul] using h

private theorem grid_boundary_integral (δ : ℝ) (q : ℤ × ℤ) (f : ℂ → ℂ) :
    (∑ k : Fin 4, segIntegral f (gridPoint δ (q + edgeStart k))
      (gridPoint δ (q + edgeEnd k))) =
    (∫ x : ℝ in δ * q.1..δ * (q.1 + 1), f (x + (δ * q.2) * Complex.I)) -
    (∫ x : ℝ in δ * q.1..δ * (q.1 + 1), f (x + (δ * (q.2 + 1)) * Complex.I)) +
    Complex.I * (∫ y : ℝ in δ * q.2..δ * (q.2 + 1), f (δ * (q.1 + 1) + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in δ * q.2..δ * (q.2 + 1), f (δ * q.1 + y * Complex.I)) := by
  have hp (r : ℤ × ℤ) : gridPoint δ r = (δ * r.1 : ℝ) + (δ * r.2 : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [gridPoint]
  have hh (x y h : ℝ) : segIntegral f (x + h * Complex.I) (y + h * Complex.I) =
      ∫ t in x..y, f (t + h * Complex.I) := by
    simpa only [one_mul, add_comm] using segIntegral_param f (h * Complex.I) 1 x y
  have hv (x y h : ℝ) : segIntegral f (h + x * Complex.I) (h + y * Complex.I) =
      Complex.I * ∫ t in x..y, f (h + t * Complex.I) := by
    simpa only [mul_comm] using segIntegral_param f h Complex.I x y
  simp only [Fin.sum_univ_four, edgeStart, edgeEnd, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue]
  simp only [hp, Prod.fst_add, Prod.snd_add, Int.cast_add, Int.cast_one,
    add_zero]
  rw [hh, hv, hh, hv]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_intCast,
    Complex.ofReal_one]
  rw [intervalIntegral.integral_symm (δ * (q.1 : ℝ)),
    intervalIntegral.integral_symm (δ * (q.2 : ℝ))]
  ring

private def offGrid (δ : ℝ) : Set ℂ :=
  {z | (∀ n : ℤ, z.re ≠ δ * n) ∧ (∀ n : ℤ, z.im ≠ δ * n)}

private theorem offGrid_dense (δ : ℝ) : Dense (offGrid δ) := by
  have h : Dense (Set.range (fun n : ℤ ↦ δ * (n : ℝ)))ᶜ :=
    (Set.countable_range _).dense_compl (𝕜 := ℝ)
  have hp := (h.prod h).preimage Complex.equivRealProdCLM.toHomeomorph.isOpenMap
  change Dense {z : ℂ | z.re ∈ (Set.range (fun n : ℤ ↦ δ * (n : ℝ)))ᶜ ∧
    z.im ∈ (Set.range (fun n : ℤ ↦ δ * (n : ℝ)))ᶜ} at hp
  simpa only [offGrid, Set.mem_compl_iff, Set.mem_range, not_exists, ne_eq, eq_comm] using hp

private theorem grid_mem_strict (δ : ℝ) (z : ℂ) (hz : z ∈ offGrid δ)
    (q : ℤ × ℤ) (hq : z ∈ complexGridSquare δ q) :
    δ * q.1 < z.re ∧ z.re < δ * ((q.1 : ℝ) + 1) ∧
    δ * q.2 < z.im ∧ z.im < δ * ((q.2 : ℝ) + 1) := by
  have hx := hz.1 q.1
  have hx' := hz.1 (q.1 + 1)
  have hy := hz.2 q.2
  have hy' := hz.2 (q.2 + 1)
  simp only [Int.cast_add, Int.cast_one] at hx' hy'
  exact ⟨lt_of_le_of_ne hq.1 hx.symm, lt_of_le_of_ne hq.2.1 hx',
    lt_of_le_of_ne hq.2.2.1 hy.symm, lt_of_le_of_ne hq.2.2.2 hy'⟩

private theorem grid_mem_unique (δ : ℝ) (hδ : 0 < δ) (z : ℂ)
    (hz : z ∈ offGrid δ) (q r : ℤ × ℤ)
    (hq : z ∈ complexGridSquare δ q) (hr : z ∈ complexGridSquare δ r) : q = r := by
  have hqs := grid_mem_strict δ z hz q hq
  have hrs := grid_mem_strict δ z hz r hr
  have hxq : ⌊z.re / δ⌋ = q.1 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith [hq.1]),
      (div_lt_iff₀ hδ).mpr (by nlinarith [hqs.2.1])⟩
  have hxr : ⌊z.re / δ⌋ = r.1 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith [hr.1]),
      (div_lt_iff₀ hδ).mpr (by nlinarith [hrs.2.1])⟩
  have hyq : ⌊z.im / δ⌋ = q.2 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith [hq.2.2.1]),
      (div_lt_iff₀ hδ).mpr (by nlinarith [hqs.2.2.2])⟩
  have hyr : ⌊z.im / δ⌋ = r.2 := Int.floor_eq_iff.mpr
    ⟨(le_div_iff₀ hδ).mpr (by nlinarith [hr.2.2.1]),
      (div_lt_iff₀ hδ).mpr (by nlinarith [hrs.2.2.2])⟩
  exact Prod.ext (hxq.symm.trans hxr) (hyq.symm.trans hyr)

private theorem grid_square_rect (δ : ℝ) (hδ : 0 < δ) (q : ℤ × ℤ) :
    complexGridSquare δ q =
      (Set.uIcc (gridPoint δ q).re (gridPoint δ (q + (1, 1))).re ×ℂ
       Set.uIcc (gridPoint δ q).im (gridPoint δ (q + (1, 1))).im) := by
  have hx : δ * (q.1 : ℝ) ≤ δ * ((q.1 : ℝ) + 1) := by nlinarith
  have hy : δ * (q.2 : ℝ) ≤ δ * ((q.2 : ℝ) + 1) := by nlinarith
  ext z
  simp [complexGridSquare, gridPoint, Set.uIcc_of_le hx, Set.uIcc_of_le hy, Complex.mem_reProdIm,
    and_assoc]

private theorem grid_cauchy_off (U L : Set ℂ) (hU : IsOpen U)
    (δ : ℝ) (hδ : 0 < δ) (S : Finset (ℤ × ℤ))
    (hcover : ∀ z ∈ L, ∃ q ∈ S, z ∈ complexGridSquare δ q)
    (hinside : ∀ q ∈ S, complexGridSquare δ q ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (z : ℂ)
    (hzL : z ∈ L) (hz : z ∈ offGrid δ) :
    (∑ e : Exposed S, segIntegral (fun w ↦ f w / (w - z))
      (exposedSrc δ S e) (exposedDst δ S e)) = 2 * (Real.pi : ℂ) * Complex.I * f z := by
  classical
  rw [exposed_sum δ S _ (segIntegral_reverse _)]
  have hv (q : ℤ × ℤ) (hq : q ∈ S) :
      (∑ k : Fin 4, segIntegral (fun w ↦ f w / (w - z))
        (gridPoint δ (q + edgeStart k)) (gridPoint δ (q + edgeEnd k))) =
      if z ∈ complexGridSquare δ q then 2 * (Real.pi : ℂ) * Complex.I * f z else 0 := by
    rw [grid_boundary_integral]
    have hR : (Set.uIcc (gridPoint δ q).re (gridPoint δ (q + (1, 1))).re ×ℂ
        Set.uIcc (gridPoint δ q).im (gridPoint δ (q + (1, 1))).im) ⊆ U := by
      rw [← grid_square_rect δ hδ q]
      exact hinside q hq
    by_cases hzq : z ∈ complexGridSquare δ q
    · rw [ite_eq_left hzq]
      obtain ⟨h1, h2, h3, h4⟩ := grid_mem_strict δ z hz q hzq
      have hh := rectangle_cauchy_kernel_integral U hU f hf
        (gridPoint δ q) (gridPoint δ (q + (1, 1))) z hR
        h1 (by simpa [gridPoint] using h2) h3 (by simpa [gridPoint] using h4)
      simpa [gridPoint, Complex.ofReal_mul, Complex.ofReal_add] using hh
    · rw [ite_eq_right hzq]
      have hd : DifferentiableOn ℂ (fun w ↦ f w / (w - z))
          (Set.uIcc (gridPoint δ q).re (gridPoint δ (q + (1, 1))).re ×ℂ
           Set.uIcc (gridPoint δ q).im (gridPoint δ (q + (1, 1))).im) := by
        apply (hf.mono hR).div (differentiableOn_id.sub_const z)
        intro w hw hn
        have hwq : w ∈ complexGridSquare δ q := by rwa [grid_square_rect δ hδ q]
        exact hzq (sub_eq_zero.mp hn ▸ hwq)
      have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (fun w ↦ f w / (w - z)) (gridPoint δ q) (gridPoint δ (q + (1, 1))) hd
      simpa [gridPoint, Complex.ofReal_mul, Complex.ofReal_add, smul_eq_mul] using hh
  trans ∑ q ∈ S, if z ∈ complexGridSquare δ q then
    2 * (Real.pi : ℂ) * Complex.I * f z else 0
  · exact Finset.sum_congr rfl hv
  obtain ⟨q, hq, hzq⟩ := hcover z hzL
  rw [Finset.sum_eq_single q]
  · simp [hzq]
  · intro r hr hrq
    have hn : z ∉ complexGridSquare δ r := fun hzr ↦
      hrq (grid_mem_unique δ hδ z hz r q hzr hzq)
    simp [hn]
  · exact fun h ↦ (h hq).elim

/-- Finite closed polygonal contours in U\K give the Cauchy representation
of every holomorphic function on U at every point of K, with one contour
chosen independently of that function and point.

Source: Conway, VIII Proposition 1.1, pp.195–196; Ahlfors, IV §1.4
Theorem 3, pp.111–112, and IV §2.1 Lemma 2, pp.116–117.
`DifferentiableOn ℂ f U` is holomorphy on the given open U.
For polygon j, the Fin (m j + 1) vertices have first vertex equal to the
last; segment k runs from vertex k.castSucc to vertex k.succ. Its real
affine parameter has derivative equal to their difference. Thus the
literal double finite sum is exactly the stated polygon contour integral.

Complete natural-language proof:

1. The empty compact set uses the empty polygon family. Otherwise the compact
neighborhood/grid theorem gives a compact regular closed `L` with `K` inside
its interior, and exactly the finitely many mesh squares meeting `L`. Every
selected square is in `U`. A side shared by a selected and an unselected square
avoids `L`: a point of `L` on it would select both closed squares. Thus every
exposed closed side, including its endpoints, lies in `U \ L`.

2. Orient the four sides of each selected square counterclockwise. Cancellation
of the oppositely directed shared sides leaves precisely the exposed sides.
The same cancellation applied to the difference of vertex indicator functions
shows equality of the incoming and outgoing counts at every vertex. Positive
mesh size excludes loop edges. The finite balanced-edge cycle theorem partitions
these edges into nonempty cyclic lists. Enumerate each list by `Fin`, use the
source of the indexed edge as its vertex, and repeat the first source at the
last index. Cyclic adjacency identifies each next vertex with the edge target.
Unique cycle membership and absence of repeated edges identify the double
polygon sum with the sum of exposed sides.

3. Fix a holomorphic `f` and a point of `L` whose two coordinates avoid all grid
levels. There is exactly one selected square containing it; the coordinate
inequalities there are strict. On that square the rectangle Cauchy formula gives
`2πi f(z)`. On every other square the kernel `f(w)/(w-z)` is holomorphic, so its
rectangle boundary integral is zero. Affine substitution identifies the four
coordinate integrals with the four segment integrals, with reversal for top
and left. Sum these formulas and cancel all shared sides by step 2. Division
by nonzero `2πi` gives the desired identity at all these off-grid points.

4. The complement of the countable set of grid levels is dense in the real line.
Its product, transported by the real/imaginary homeomorphism, is dense in the
complex plane. Its intersection with the open interior of `L` is dense there;
regular closedness then makes its closure contain all of `L`. Each exposed
segment avoids `L`, so the segment-kernel continuity theorem makes its Cauchy
integral continuous in the pole on `L`. The finite exposed sum is consequently
continuous there, as is `f`. The equality in step 3 extends to `L` and hence to
`K`. The cycle reindexing of step 2 gives exactly the displayed polygon formula.

The grid and cancellation follow Conway VIII.1.1, pp.195–196. The rectangular
interior formula uses the separately registered Ahlfors normalization and divided
difference results. The finite-list conversion and the parameterized-integration
implementation of continuity are explicit formal bookkeeping of these steps.

-/
theorem conway_finite_polygon_cauchy_representation
    (U K : Set ℂ) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (n : ℕ) (m : Fin n → ℕ) (v : ∀ j, Fin (m j + 1) → ℂ),
      (∀ j, 0 < m j) ∧
      (∀ j, v j 0 = v j (Fin.last (m j))) ∧
      (∀ (j : Fin n) (k : Fin (m j)) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        AffineMap.lineMap (v j k.castSucc) (v j k.succ) t ∈ U \ K) ∧
      (∀ (f : ℂ → ℂ), DifferentiableOn ℂ f U → ∀ z ∈ K,
        f z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∑ j : Fin n, ∑ k : Fin (m j),
            (v j k.succ - v j k.castSucc) *
              ∫ t in (0 : ℝ)..1,
                f (AffineMap.lineMap (v j k.castSucc) (v j k.succ) t) /
                  (AffineMap.lineMap (v j k.castSucc) (v j k.succ) t - z)) := by
  classical
  by_cases hKe : K = ∅
  · subst K
    refine ⟨0, Fin.elim0, (fun j ↦ Fin.elim0 j), ?_⟩
    simp
  obtain ⟨L, δ, S, hLc, hKL, hLregular, hLU, hδ, hselect, hcover, hinside,
    hexposed⟩ := conway_regular_closed_grid_cover U K hU hK hKU
  have hedge (e : Exposed S) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AffineMap.lineMap (exposedSrc δ S e) (exposedDst δ S e) t ∈ U \ L := by
    exact hexposed e.2.val (Finset.mem_filter.mp e.2.property).1
      (e.2.val + edgeNeighbor e.1) (Finset.mem_filter.mp e.2.property).2
      (grid_edge_mem δ hδ e.2.val e.1 t ht)
  obtain ⟨n, m, v, e, hm, hclosed, he, hsum⟩ :=
    cycles_vertex_arrays (exposedSrc δ S) (exposedDst δ S)
      (exposed_distinct δ hδ S) (exposed_balanced δ S)
  refine ⟨n, m, v, hm, hclosed, ?_, ?_⟩
  · intro j k t ht
    rw [(he j k).1, (he j k).2]
    have h := hedge (e j k) t ht
    exact ⟨h.1, fun hK ↦ h.2 (interior_subset (hKL hK))⟩
  · intro f hf z hz
    let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    let F (w : ℂ) := c⁻¹ * ∑ i : Exposed S,
      segIntegral (fun ζ ↦ f ζ / (ζ - w)) (exposedSrc δ S i) (exposedDst δ S i)
    have hF : ContinuousOn F L := by
      apply continuousOn_const.mul
      exact continuousOn_finsetSum _ (fun i _ ↦
        polygon_segment_kernel_continuousOn L U f hf.continuousOn _ _ (hedge i))
    have hoff : Set.EqOn f F (interior L ∩ offGrid δ) := by
      intro w hw
      have hv := grid_cauchy_off U L hU δ hδ S hcover hinside f hf w
        (interior_subset hw.1) hw.2
      dsimp [F]
      rw [hv]
      change f w = c⁻¹ * (c * f w)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have hdense : L ⊆ closure (interior L ∩ offGrid δ) := by
      nth_rw 1 [← hLregular]
      exact closure_minimal ((offGrid_dense δ).open_subset_closure_inter isOpen_interior)
        isClosed_closure
    have hall : Set.EqOn f F L := hoff.of_subset_closure (hf.continuousOn.mono hLU) hF
      (fun w hw ↦ interior_subset hw.1) hdense
    have hh := hall (interior_subset (hKL hz))
    dsimp [F, c] at hh
    rw [← hsum (fun i ↦ segIntegral (fun ζ ↦ f ζ / (ζ - z))
      (exposedSrc δ S i) (exposedDst δ S i))] at hh
    convert hh using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    rw [(he j k).1, (he j k).2]
    rfl


end HolomorphicAnosov.Analysis.Complex
