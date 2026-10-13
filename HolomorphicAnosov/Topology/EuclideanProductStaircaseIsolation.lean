import HolomorphicAnosov.Topology.Homology.SignedShuffleStaircaseRecursion
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# An isolated simplex in the staircase product triangulation

Source: Hatcher, Algebraic Topology, §3.B pp.277–278.
DAG: `topo.euclidean_product_staircase_isolation_g17`.

The bottom-then-right staircase is the only staircase through the corner (p,0).
All other staircase images are compact, so a neighborhood of this corner misses
them. Mix the corner barycentric point with the barycenter by a sufficiently
small positive amount. Its weights are positive and its image remains in that
neighborhood. The standard coordinate simplex is embedded and positive weights
map to its interior. The selected product simplex is this coordinate simplex
followed by an explicit invertible shear: its last first-block coordinate adds
the sum of the second block. Translate each factor by the chosen interior point.
Then the selected summand contains zero in its interior, its faces avoid zero,
and every other summand misses zero. This works when either block is empty.
-/

noncomputable section
namespace HolomorphicAnosov.SignedSingularCrossProduct

/-- The staircase which traverses the bottom edge and then the right edge. -/
def bottomRight (p q : ℕ) : GridPath p q := fun k ↦
  (⟨min k.val p, by omega⟩,⟨k.val-p, by omega⟩)

/-- The bottom/right path satisfies the actual unit-step staircase definition. -/
theorem bottomRight_mem (p q : ℕ) : bottomRight p q ∈ staircases p q := by
  classical
  simp only [staircases, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_,?_,?_⟩
  · apply Prod.ext <;> apply Fin.ext <;> simp [bottomRight]
  · apply Prod.ext <;> apply Fin.ext <;> simp [bottomRight]
  · intro i
    by_cases hi : i.val < p
    · left
      constructor
      · dsimp [bottomRight]
        omega
      · apply Fin.ext
        dsimp [bottomRight]
        omega
    · right
      constructor
      · apply Fin.ext
        dsimp [bottomRight]
        omega
      · dsimp [bottomRight]
        omega

/-- At the kth vertex the two coordinate indices sum to k. -/
theorem staircase_vertex_sum {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) (k : Fin (p+q+1)) :
    (w k).1.val + (w k).2.val = k.val := by
  have hs := (Finset.mem_filter.mp hw).2
  induction k using Fin.induction with
  | zero => rw [hs.1]; rfl
  | succ i ih =>
    rcases hs.2.2 i with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · have hy' := congrArg Fin.val hy
      simp only [Fin.val_castSucc] at ih
      simp only [Fin.val_succ]
      omega
    · have hx' := congrArg Fin.val hx
      simp only [Fin.val_castSucc] at ih
      simp only [Fin.val_succ]
      omega

/-- Only the bottom/right path contains the distinguished corner `(p,0)`. -/
theorem eq_bottomRight_of_corner {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) (k : Fin (p+q+1))
    (hk : w k = (Fin.last p,0)) : w = bottomRight p q := by
  have hsum := staircase_vertex_sum w hw k
  rw [hk] at hsum
  have hkval : k.val = p := by simpa using hsum.symm
  have hm := staircase_coordinate_monotone w hw
  funext i
  have hi := staircase_vertex_sum w hw i
  by_cases hik : i ≤ k
  · have hy := hm.2 hik
    dsimp only at hy
    rw [hk] at hy
    apply Prod.ext <;> apply Fin.ext <;> dsimp [bottomRight]
    · change i.val ≤ k.val at hik
      simp only [Fin.val_zero] at hy
      omega
    · change i.val ≤ k.val at hik
      simp only [Fin.val_zero] at hy
      omega
  · have hx := hm.1 (le_of_not_ge hik)
    dsimp only at hx
    rw [hk] at hx
    apply Prod.ext <;> apply Fin.ext <;> dsimp [bottomRight]
    · change ¬i.val ≤ k.val at hik
      simp only [Fin.val_last] at hx
      have hbound := (w i).1.isLt
      omega
    · change ¬i.val ≤ k.val at hik
      simp only [Fin.val_last] at hx
      have hbound := (w i).1.isLt
      omega

/-- A positive weight remains positive in the image coordinate it contributes to. -/
theorem simplex_weight_le_map {ι κ : Type} [Fintype ι]
    (f : ι → κ) (t : Convexity.StdSimplex ℝ ι) (i : ι) :
    t.weights i ≤ (Convexity.StdSimplex.map f t).weights (f i) := by
  classical
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  have h := Finset.single_le_sum
    (f := fun j ↦ (Finsupp.single (f j) (t.weights j) : κ →₀ ℝ) (f i))
    (s := Finset.univ) (fun j _ ↦ by
      simp only [Finsupp.single_apply]
      split_ifs
      · exact t.nonneg j
      · exact le_rfl) (Finset.mem_univ i)
  simpa using h

/-- A positive coefficient in a simplex with vertex image has that same vertex image. -/
theorem simplex_map_single_of_positive {ι κ : Type} [Fintype ι]
    (f : ι → κ) (t : Convexity.StdSimplex ℝ ι) (a : κ)
    (h : Convexity.StdSimplex.map f t = Convexity.StdSimplex.single a)
    (i : ι) (hi : 0 < t.weights i) : f i = a := by
  classical
  by_contra hn
  have hb := simplex_weight_le_map f t i
  rw [h] at hb
  have hz : (Convexity.StdSimplex.single (R := ℝ) a).weights (f i) = 0 := by
    simp [Convexity.StdSimplex.single, Ne.symm hn]
  rw [hz] at hb
  exact (not_lt_of_ge hb) hi

/-- The affine map of the grid simplex into the two factor simplexes. -/
def gridSimplexMap {p q : ℕ} (w : GridPath p q) :
    C(Convexity.StdSimplex ℝ (Fin (p+q+1)),
      Convexity.StdSimplex ℝ (Fin (p+1)) × Convexity.StdSimplex ℝ (Fin (q+1))) :=
  (firstSimplexMap w).prodMk (secondSimplexMap w)

/-- The distinguished product corner lies in only the bottom/right staircase simplex. -/
theorem corner_not_mem_other_simplex {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) (hne : w ≠ bottomRight p q) :
    (Convexity.StdSimplex.single (R := ℝ) (Fin.last p),
      Convexity.StdSimplex.single (R := ℝ) (0 : Fin (q+1))) ∉ Set.range (gridSimplexMap w) := by
  rintro ⟨t,ht⟩
  have hpos : ∃ i, 0 < t.weights i := by
    by_contra h
    push Not at h
    have hz : t.weights = 0 := by
      ext i
      exact le_antisymm (h i) (t.nonneg i)
    have htotal := t.total
    simp [hz] at htotal
  obtain ⟨i,hi⟩ := hpos
  have hfirst : Convexity.StdSimplex.map (fun k ↦ (w k).1) t =
      Convexity.StdSimplex.single (Fin.last p) := congrArg Prod.fst ht
  have hsecond : Convexity.StdSimplex.map (fun k ↦ (w k).2) t =
      Convexity.StdSimplex.single (0 : Fin (q+1)) := congrArg Prod.snd ht
  have hcorner : w i = (Fin.last p,0) := Prod.ext
    (simplex_map_single_of_positive _ t _ hfirst i hi)
    (simplex_map_single_of_positive _ t _ hsecond i hi)
  exact hne (eq_bottomRight_of_corner w hw i hcorner)

/-- All other staircase simplex images are closed and miss the distinguished corner.
Finiteness therefore gives an open neighborhood on which only one summand survives. -/
theorem corner_has_isolating_neighborhood (p q : ℕ) :
    ∃ W : Set (Convexity.StdSimplex ℝ (Fin (p+1)) ×
        Convexity.StdSimplex ℝ (Fin (q+1))),
      IsOpen W ∧
      (Convexity.StdSimplex.single (Fin.last p),Convexity.StdSimplex.single 0) ∈ W ∧
      ∀ w ∈ staircases p q, w ≠ bottomRight p q →
        Disjoint W (Set.range (gridSimplexMap w)) := by
  classical
  let : T2Space (Convexity.StdSimplex ℝ (Fin (p+1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (p+1))).t2Space
  let : T2Space (Convexity.StdSimplex ℝ (Fin (q+1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (q+1))).t2Space
  let S := (staircases p q).erase (bottomRight p q)
  let C := ⋃ w ∈ S, Set.range (gridSimplexMap w)
  have hc : IsCompact C := S.isCompact_biUnion (fun w _ ↦
    isCompact_range (gridSimplexMap w).continuous)
  refine ⟨Cᶜ,hc.isClosed.isOpen_compl,?_,?_⟩
  · intro hz
    obtain ⟨w,hw,hcorner⟩ := Set.mem_iUnion₂.mp hz
    exact corner_not_mem_other_simplex w (Finset.mem_erase.mp hw).2
      (Finset.mem_erase.mp hw).1 hcorner
  · intro w hw hne
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact hz (Set.mem_iUnion₂.mpr ⟨w,Finset.mem_erase.mpr ⟨hne,hw⟩,hz'⟩)

/-- Move a simplex point toward its barycenter by a parameter in the unit interval. -/
def barycenterMix {ι : Type} [Fintype ι] [Nonempty ι]
    (t : Convexity.StdSimplex ℝ ι) (a : unitInterval) : Convexity.StdSimplex ℝ ι where
  weights := (a : ℝ) • (Convexity.StdSimplex.barycenter (K := ℝ) (M := ι)).weights +
    (1-(a : ℝ)) • t.weights
  nonneg := by
    intro i
    change 0 ≤ (a : ℝ) * _ + (1-(a : ℝ)) * t.weights i
    exact add_nonneg (mul_nonneg a.2.1 (Convexity.StdSimplex.weights_nonneg _))
      (mul_nonneg (sub_nonneg.mpr a.2.2) (t.nonneg i))
  total := by
    classical
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, Convexity.StdSimplex.total_of_fintype]
    ring

/-- Barycentric interpolation is continuous in its parameter. -/
theorem continuous_barycenterMix {ι : Type} [Fintype ι] [Nonempty ι]
    (t : Convexity.StdSimplex ℝ ι) : Continuous (barycenterMix t) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff.mpr
  apply continuous_pi
  intro i
  change Continuous (fun a : unitInterval ↦
    (a : ℝ) * (Convexity.StdSimplex.barycenter (K := ℝ) (M := ι)).weights i +
      (1-(a : ℝ)) * t.weights i)
  fun_prop

/-- Every neighborhood of a simplex point contains a point with all weights positive. -/
theorem positive_weights_in_nhds {ι : Type} [Fintype ι] [Nonempty ι]
    (t : Convexity.StdSimplex ℝ ι) (W : Set (Convexity.StdSimplex ℝ ι))
    (hW : IsOpen W) (ht : t ∈ W) :
    ∃ u ∈ W, ∀ i, 0 < u.weights i := by
  have hzero : barycenterMix t 0 = t := by
    ext i
    simp [barycenterMix]
  have hpre : (barycenterMix t) ⁻¹' W ∈ nhds (0 : unitInterval) :=
    (continuous_barycenterMix t).continuousAt.preimage_mem_nhds
      (hW.mem_nhds (hzero.symm ▸ ht))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hpre
  let a : unitInterval := ⟨min (ε/2) (1/2),by
    constructor
    · exact le_min (by positivity) (by norm_num)
    · exact (min_le_right _ _).trans (by norm_num)⟩
  have ha : (0 : ℝ) < a := lt_min (by positivity) (by norm_num)
  have hae : (a : ℝ) < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have haW : barycenterMix t a ∈ W := by
    apply hball
    change |(a : ℝ)-0| < ε
    simpa [abs_of_pos ha] using hae
  refine ⟨barycenterMix t a,haW,?_⟩
  intro i
  change 0 < (a : ℝ) * (Convexity.StdSimplex.barycenter (K := ℝ) (M := ι)).weights i +
    (1-(a : ℝ)) * t.weights i
  apply add_pos_of_pos_of_nonneg
  · rw [Convexity.StdSimplex.weights_barycenter_apply]
    exact mul_pos ha (inv_pos.mpr (by exact_mod_cast Fintype.card_pos))
  · exact mul_nonneg (sub_nonneg.mpr a.2.2) (t.nonneg i)

/-- A strictly positive point in the bottom/right simplex misses every other staircase image. -/
theorem exists_isolated_positive_bottomRight (p q : ℕ) :
    ∃ t : Convexity.StdSimplex ℝ (Fin (p+q+1)),
      (∀ i, 0 < t.weights i) ∧
      ∀ w ∈ staircases p q, w ≠ bottomRight p q →
        gridSimplexMap (bottomRight p q) t ∉ Set.range (gridSimplexMap w) := by
  obtain ⟨W,hW,hcorner,hsep⟩ := corner_has_isolating_neighborhood p q
  let k : Fin (p+q+1) := ⟨p,by omega⟩
  let t0 : Convexity.StdSimplex ℝ (Fin (p+q+1)) := Convexity.StdSimplex.single k
  have ht0 : gridSimplexMap (bottomRight p q) t0 ∈ W := by
    convert hcorner using 1
    apply Prod.ext
    · change Convexity.StdSimplex.map _ (Convexity.StdSimplex.single k) = _
      rw [Convexity.StdSimplex.map_single]
      congr 1
      apply Fin.ext
      simp [bottomRight,k]
    · change Convexity.StdSimplex.map _ (Convexity.StdSimplex.single k) = _
      rw [Convexity.StdSimplex.map_single]
      congr 1
      apply Fin.ext
      simp [bottomRight,k]
  obtain ⟨t,ht,hpos⟩ := positive_weights_in_nhds t0 _
    (hW.preimage (gridSimplexMap (bottomRight p q)).continuous) ht0
  refine ⟨t,hpos,?_⟩
  intro w hw hne hin
  exact Set.disjoint_left.mp (hsep w hw hne) ht hin

/-- The standard affine simplex with vertices zero and the coordinate vectors. -/
def coordinateSimplex (n : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (n+1)), EuclideanSpace ℝ (Fin n)) :=
  ⟨fun t ↦ WithLp.toLp 2 (fun i ↦ t.weights i.succ),
    (PiLp.continuous_toLp 2 _).comp
      (continuous_pi (fun i ↦ Convexity.StdSimplex.continuous_weights_apply ℝ i.succ))⟩

/-- Dropping the zeroth barycentric coordinate is injective since all weights sum to one. -/
theorem coordinateSimplex_injective (n : ℕ) : Function.Injective (coordinateSimplex n) := by
  intro t u h
  have hsucc (i : Fin n) : t.weights i.succ = u.weights i.succ := congrArg (fun z ↦ z i) h
  have h0 : t.weights 0 = u.weights 0 := by
    have ht := t.total_of_fintype
    have hu := u.total_of_fintype
    rw [Fin.sum_univ_succ] at ht hu
    have hs : ∑ i : Fin n, t.weights i.succ = ∑ i : Fin n, u.weights i.succ :=
      Finset.sum_congr rfl (fun i _ ↦ hsucc i)
    linarith
  ext i
  exact Fin.cases h0 hsucc i

/-- The standard affine simplex is a closed embedding. -/
theorem coordinateSimplex_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (coordinateSimplex n) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (coordinateSimplex n).continuous (coordinateSimplex_injective n)
    (coordinateSimplex n).continuous.isClosedMap

/-- A simplex point with positive weights maps to an ambient interior point. -/
theorem coordinateSimplex_mem_interior (n : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (n+1))) (ht : ∀ i, 0 < t.weights i) :
    coordinateSimplex n t ∈ interior (Set.range (coordinateSimplex n)) := by
  classical
  let W : Set (EuclideanSpace ℝ (Fin n)) :=
    {z | (∀ i, 0 < z i) ∧ ∑ i, z i < 1}
  have hW : IsOpen W := by
    change IsOpen ({z : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < z i} ∩
      {z | ∑ i, z i < 1})
    apply IsOpen.inter
    · simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite (fun i ↦ isOpen_lt continuous_const (by fun_prop))
    · exact isOpen_lt (show Continuous (fun z : EuclideanSpace ℝ (Fin n) ↦ ∑ i, z i) by
        fun_prop) continuous_const
  have hmem : coordinateSimplex n t ∈ W := by
    refine ⟨fun i ↦ ht i.succ,?_⟩
    have hsum := t.total_of_fintype
    rw [Fin.sum_univ_succ] at hsum
    have h0 := ht 0
    change ∑ i : Fin n, t.weights i.succ < 1
    linarith
  have hsub : W ⊆ Set.range (coordinateSimplex n) := by
    intro z hz
    let w : Fin (n+1) → ℝ := Fin.cases (1-∑ i, z i) (fun i ↦ z i)
    have hsum : ∑ i, w i = 1 := by
      simp only [w,Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ]
      ring
    have hw : w ∈ Set.range (fun s : Convexity.StdSimplex ℝ (Fin (n+1)) ↦
        (s.weights : Fin (n+1) → ℝ)) := by
      rw [Convexity.StdSimplex.range_toFun_comp_weights]
      refine ⟨Set.mem_iInter.mpr ?_,hsum⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact sub_nonneg.mpr hz.2.le
      · exact (hz.1 j).le
    obtain ⟨s,hs⟩ := hw
    refine ⟨s,?_⟩
    ext i
    exact congrFun hs i.succ
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hW.mem_nhds hmem) hsub)

/-- The coefficient of a map with a singleton fibre. -/
theorem simplex_map_weight_unique {ι κ : Type} [Fintype ι]
    (f : ι → κ) (t : Convexity.StdSimplex ℝ ι) (a : κ) (i : ι)
    (hi : f i = a) (hf : ∀ j, f j = a → j = i) :
    (Convexity.StdSimplex.map f t).weights a = t.weights i := by
  classical
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    exact Finsupp.single_eq_of_ne (fun h ↦ hji (hf j h.symm))
  · simp

/-- Positive second-coordinate fibres of the bottom/right path are singletons. -/
theorem bottomRight_second_weight {p q : ℕ}
    (t : Convexity.StdSimplex ℝ (Fin (p+q+1))) (j : Fin q) :
    (secondSimplexMap (bottomRight p q) t).weights j.succ =
      t.weights ⟨p+j.val+1,by omega⟩ := by
  apply simplex_map_weight_unique
  · apply Fin.ext
    simp only [bottomRight,Fin.val_succ]
    omega
  · intro k hk
    have hh := congrArg Fin.val hk
    apply Fin.ext
    simp only [bottomRight,Fin.val_succ] at hh
    dsimp only
    omega

/-- The map coefficient is the sum over its fibre. -/
theorem simplex_map_weight_sum {ι κ : Type} [Fintype ι] [DecidableEq κ]
    (f : ι → κ) (t : Convexity.StdSimplex ℝ ι) (a : κ) :
    (Convexity.StdSimplex.map f t).weights a = ∑ i with f i = a, t.weights i := by
  classical
  rw [Convexity.StdSimplex.weights_map, Finsupp.mapDomain_fintype,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  simp only [Finsupp.single_apply,Finset.sum_filter]

/-- All nonterminal first-coordinate fibres are singletons. -/
theorem bottomRight_first_weight_lt {p q : ℕ}
    (t : Convexity.StdSimplex ℝ (Fin (p+q+1))) (i : Fin (p+1)) (hi : i.val < p) :
    (firstSimplexMap (bottomRight p q) t).weights i = t.weights ⟨i.val,by omega⟩ := by
  apply simplex_map_weight_unique
  · apply Fin.ext
    dsimp [bottomRight]
    omega
  · intro k hk
    have hh := congrArg Fin.val hk
    apply Fin.ext
    dsimp [bottomRight] at hh ⊢
    omega

/-- The terminal first-coordinate fibre is the whole vertical edge. -/
theorem bottomRight_first_weight_last {p q : ℕ}
    (t : Convexity.StdSimplex ℝ (Fin (p+q+1))) :
    (firstSimplexMap (bottomRight p q) t).weights (Fin.last p) =
      ∑ j : Fin (q+1), t.weights ⟨p+j.val,by omega⟩ := by
  classical
  change (Convexity.StdSimplex.map (fun k ↦ (bottomRight p q k).1) t).weights _ = _
  rw [simplex_map_weight_sum]
  symm
  apply Finset.sum_bij (fun j _ ↦ (⟨p+j.val,by omega⟩ : Fin (p+q+1)))
  · intro j hj
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply Fin.ext
    dsimp [bottomRight]
    omega
  · intro j hj k hk h
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp only at hh
    omega
  · intro k hk
    have hh := congrArg Fin.val (Finset.mem_filter.mp hk).2
    dsimp [bottomRight] at hh
    refine ⟨⟨k.val-p,by omega⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    dsimp only
    omega
  · intro j hj
    rfl

/-- The standard bottom/right product simplex in concatenated Euclidean coordinates. -/
def bottomRightCoordinateSimplex (p q : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (p+q+1)),EuclideanSpace ℝ (Fin (p+q))) :=
  ⟨fun t ↦ (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm
      (coordinateSimplex p (firstSimplexMap (bottomRight p q) t),
        coordinateSimplex q (secondSimplexMap (bottomRight p q) t)),
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.continuous.comp
      (((coordinateSimplex p).continuous.comp (firstSimplexMap (bottomRight p q)).continuous).prodMk
        ((coordinateSimplex q).continuous.comp (secondSimplexMap (bottomRight p q)).continuous))⟩

/-- The shear which adds the sum of the second block to the last first-block coordinate. -/
def bottomRightShear (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃ₜ
      (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) where
  toFun z := (WithLp.toLp 2 (fun i ↦ z.1 i + if i.val+1=p then ∑ j, z.2 j else 0),z.2)
  invFun z := (WithLp.toLp 2 (fun i ↦ z.1 i - if i.val+1=p then ∑ j, z.2 j else 0),z.2)
  left_inv z := by
    apply Prod.ext
    · ext i
      simp
    · rfl
  right_inv z := by
    apply Prod.ext
    · ext i
      simp
    · rfl
  continuous_toFun := by
    apply Continuous.prodMk _ continuous_snd
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    split_ifs <;> fun_prop
  continuous_invFun := by
    apply Continuous.prodMk _ continuous_snd
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    split_ifs <;> fun_prop

/-- The distinguished simplex is the image of the standard simplex by an ambient shear. -/
theorem bottomRightCoordinateSimplex_shear (p q : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (p+q+1))) :
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (bottomRightCoordinateSimplex p q t) =
      bottomRightShear p q (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (coordinateSimplex (p+q) t)) := by
  change EuclideanSpace.finAddEquivProd ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    change (firstSimplexMap (bottomRight p q) t).weights i.succ =
      t.weights (Fin.castAdd q i).succ +
        if i.val+1=p then ∑ j : Fin q, t.weights (Fin.natAdd p j).succ else 0
    by_cases hi : i.val+1=p
    · rw [ite_eq_left hi]
      have hi' : i.succ = Fin.last p := Fin.ext hi
      rw [hi',bottomRight_first_weight_last,Fin.sum_univ_succ]
      congr 1
      · congr 1
        apply Fin.ext
        simpa using hi.symm
    · rw [ite_eq_right hi,add_zero,bottomRight_first_weight_lt t i.succ (by
        simp only [Fin.val_succ]; omega)]
      rfl
  · ext j
    change (secondSimplexMap (bottomRight p q) t).weights j.succ =
      t.weights (Fin.natAdd p j).succ
    rw [bottomRight_second_weight]
    rfl

/-- The ambient homeomorphism expressing the distinguished staircase as an affine simplex. -/
def bottomRightAmbientEquiv (p q : ℕ) :
    EuclideanSpace ℝ (Fin (p+q)) ≃ₜ EuclideanSpace ℝ (Fin (p+q)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).toHomeomorph.trans
    ((bottomRightShear p q).trans (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.toHomeomorph)

/-- Coordinate form of the ambient homeomorphism comparison. -/
theorem bottomRightCoordinateSimplex_eq (p q : ℕ) :
    (bottomRightCoordinateSimplex p q : _ → _) =
      bottomRightAmbientEquiv p q ∘ coordinateSimplex (p+q) := by
  funext t
  apply (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).injective
  rw [bottomRightCoordinateSimplex_shear]
  exact ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).apply_symm_apply _).symm

/-- The selected staircase simplex is a closed embedding. -/
theorem bottomRightCoordinateSimplex_isClosedEmbedding (p q : ℕ) :
    Topology.IsClosedEmbedding (bottomRightCoordinateSimplex p q) := by
  rw [bottomRightCoordinateSimplex_eq]
  exact (bottomRightAmbientEquiv p q).isClosedEmbedding.comp
    (coordinateSimplex_isClosedEmbedding (p+q))

/-- Every point with positive barycentric weights is an ambient interior point of the
selected staircase simplex. -/
theorem bottomRightCoordinateSimplex_mem_interior (p q : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (p+q+1))) (ht : ∀ i, 0 < t.weights i) :
    bottomRightCoordinateSimplex p q t ∈ interior (Set.range (bottomRightCoordinateSimplex p q)) := by
  rw [bottomRightCoordinateSimplex_eq]
  rw [Set.range_comp]
  rw [← (bottomRightAmbientEquiv p q).image_interior]
  exact ⟨coordinateSimplex (p+q) t,coordinateSimplex_mem_interior (p+q) t ht,rfl⟩

/-- Both projected simplex points retain strictly positive weights. -/
theorem bottomRight_positive_weights {p q : ℕ}
    (t : Convexity.StdSimplex ℝ (Fin (p+q+1))) (ht : ∀ i, 0 < t.weights i) :
    (∀ i, 0 < (firstSimplexMap (bottomRight p q) t).weights i) ∧
      (∀ j, 0 < (secondSimplexMap (bottomRight p q) t).weights j) := by
  constructor
  · intro i
    let k : Fin (p+q+1) := ⟨i.val,by omega⟩
    have hk : (bottomRight p q k).1 = i := by
      apply Fin.ext
      dsimp [bottomRight,k]
      omega
    have h := simplex_weight_le_map (fun k ↦ (bottomRight p q k).1) t k
    rw [hk] at h
    exact (ht k).trans_le h
  · intro j
    let k : Fin (p+q+1) := ⟨p+j.val,by omega⟩
    have hk : (bottomRight p q k).2 = j := by
      apply Fin.ext
      dsimp [bottomRight,k]
      omega
    have h := simplex_weight_le_map (fun k ↦ (bottomRight p q k).2) t k
    rw [hk] at h
    exact (ht k).trans_le h

/-- Translate a Euclidean simplex so a specified simplex point maps to zero. -/
def translatedSimplex {n : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)) :=
  ⟨fun u ↦ s u - s t,s.continuous.sub continuous_const⟩

/-- Translation preserves a simplex's closed embedding. -/
theorem translatedSimplex_isClosedEmbedding {n : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (hs : Topology.IsClosedEmbedding s) (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    Topology.IsClosedEmbedding (translatedSimplex s t) :=
  (Homeomorph.subRight (s t)).isClosedEmbedding.comp hs

/-- Translation carries an interior base point to interior zero. -/
theorem translatedSimplex_zero_interior {n : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (t : Convexity.StdSimplex ℝ (Fin (n+1))) (ht : s t ∈ interior (Set.range s)) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ interior (Set.range (translatedSimplex s t)) := by
  change 0 ∈ interior (Set.range (Homeomorph.subRight (s t) ∘ s))
  rw [Set.range_comp,← (Homeomorph.subRight (s t)).image_interior]
  exact ⟨s t,ht,sub_self _⟩

/-- For an injective simplex a positive-weight preimage of zero excludes every face. -/
theorem translatedSimplex_faces {n : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (n+1)),EuclideanSpace ℝ (Fin n)))
    (hs : Function.Injective s) (t : Convexity.StdSimplex ℝ (Fin (n+1)))
    (ht : ∀ i, 0 < t.weights i) (i : Fin (n+1))
    (u : Convexity.StdSimplex ℝ (Fin n)) :
    translatedSimplex s t (Convexity.StdSimplex.map i.succAbove u) ≠ 0 := by
  intro hzero
  have heq := hs (sub_eq_zero.mp hzero)
  have hz : (Convexity.StdSimplex.map i.succAbove u).weights i = 0 := by
    rw [Convexity.StdSimplex.weights_map]
    exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)
  rw [heq] at hz
  exact (ne_of_gt (ht i)) hz

/-- A product simplex transported to concatenated coordinates. -/
def pairedCoordinateSimplex {p q : ℕ}
    (s : C(Convexity.StdSimplex ℝ (Fin (p+1)),EuclideanSpace ℝ (Fin p)))
    (t : C(Convexity.StdSimplex ℝ (Fin (q+1)),EuclideanSpace ℝ (Fin q)))
    (w : GridPath p q) :
    C(Convexity.StdSimplex ℝ (Fin (p+q+1)),EuclideanSpace ℝ (Fin (p+q))) :=
  ⟨fun u ↦ (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm
    (s (firstSimplexMap w u),t (secondSimplexMap w u)),
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.continuous.comp
      ((s.continuous.comp (firstSimplexMap w).continuous).prodMk
        (t.continuous.comp (secondSimplexMap w).continuous))⟩

/-- The selected product of translated factor simplexes is the translated selected simplex. -/
theorem paired_translated_bottomRight {p q : ℕ}
    (u : Convexity.StdSimplex ℝ (Fin (p+q+1))) :
    pairedCoordinateSimplex
      (translatedSimplex (coordinateSimplex p) (firstSimplexMap (bottomRight p q) u))
      (translatedSimplex (coordinateSimplex q) (secondSimplexMap (bottomRight p q) u))
      (bottomRight p q) = translatedSimplex (bottomRightCoordinateSimplex p q) u := by
  ext v : 1
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := p) (m := q)
  let a := (coordinateSimplex p (firstSimplexMap (bottomRight p q) v),
    coordinateSimplex q (secondSimplexMap (bottomRight p q) v))
  let b := (coordinateSimplex p (firstSimplexMap (bottomRight p q) u),
    coordinateSimplex q (secondSimplexMap (bottomRight p q) u))
  change e.symm (a - b) = e.symm a - e.symm b
  exact e.symm.map_sub a b

/-- There are factor simplexes for which exactly one signed staircase summand meets zero,
and that summand is an embedded simplex with zero in its interior. -/
theorem exists_isolated_product_simplexes (p q : ℕ) :
    ∃ (s : C(Convexity.StdSimplex ℝ (Fin (p+1)),EuclideanSpace ℝ (Fin p)))
      (t : C(Convexity.StdSimplex ℝ (Fin (q+1)),EuclideanSpace ℝ (Fin q))),
      (∀ (i : Fin (p+1)) (a : Convexity.StdSimplex ℝ (Fin p)),
        s (Convexity.StdSimplex.map i.succAbove a) ≠ 0) ∧
      (∀ (j : Fin (q+1)) (b : Convexity.StdSimplex ℝ (Fin q)),
        t (Convexity.StdSimplex.map j.succAbove b) ≠ 0) ∧
      Topology.IsClosedEmbedding (pairedCoordinateSimplex s t (bottomRight p q)) ∧
      (0 : EuclideanSpace ℝ (Fin (p+q))) ∈
        interior (Set.range (pairedCoordinateSimplex s t (bottomRight p q))) ∧
      (∀ (i : Fin (p+q+1)) (a : Convexity.StdSimplex ℝ (Fin (p+q))),
        pairedCoordinateSimplex s t (bottomRight p q)
          (Convexity.StdSimplex.map i.succAbove a) ≠ 0) ∧
      ∀ w ∈ staircases p q, w ≠ bottomRight p q →
        ∀ a, pairedCoordinateSimplex s t w a ≠ 0 := by
  obtain ⟨u,hpos,hisolate⟩ := exists_isolated_positive_bottomRight p q
  have hproj := bottomRight_positive_weights u hpos
  let s := translatedSimplex (coordinateSimplex p) (firstSimplexMap (bottomRight p q) u)
  let t := translatedSimplex (coordinateSimplex q) (secondSimplexMap (bottomRight p q) u)
  have hsel : pairedCoordinateSimplex s t (bottomRight p q) =
      translatedSimplex (bottomRightCoordinateSimplex p q) u := paired_translated_bottomRight u
  refine ⟨s,t,?_,?_,?_,?_,?_,?_⟩
  · exact translatedSimplex_faces _ (coordinateSimplex_injective p) _ hproj.1
  · exact translatedSimplex_faces _ (coordinateSimplex_injective q) _ hproj.2
  · rw [hsel]
    exact translatedSimplex_isClosedEmbedding _ (bottomRightCoordinateSimplex_isClosedEmbedding p q) u
  · rw [hsel]
    exact translatedSimplex_zero_interior _ u (bottomRightCoordinateSimplex_mem_interior p q u hpos)
  · rw [hsel]
    exact translatedSimplex_faces _ (bottomRightCoordinateSimplex_isClosedEmbedding p q).injective
      u hpos
  · intro w hw hne a ha
    apply hisolate w hw hne
    refine ⟨a,?_⟩
    have h := congrArg (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)) ha
    change EuclideanSpace.finAddEquivProd ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm _) = _ at h
    rw [ContinuousLinearEquiv.apply_symm_apply,map_zero] at h
    apply Prod.ext
    · apply coordinateSimplex_injective p
      exact sub_eq_zero.mp (congrArg Prod.fst h)
    · apply coordinateSimplex_injective q
      exact sub_eq_zero.mp (congrArg Prod.snd h)

end HolomorphicAnosov.SignedSingularCrossProduct

