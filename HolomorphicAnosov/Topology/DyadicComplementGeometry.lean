import HolomorphicAnosov.Topology.ClosedComplementDyadicCubeCover
import HolomorphicAnosov.Topology.DyadicCubeCompact
import Mathlib.Topology.LocallyFinite
import Mathlib.Data.Int.DivMod
import HolomorphicAnosov.Topology.RealTorusCoordinateCWStructure
import HolomorphicAnosov.Topology.CoordinateBoxCompact
import Mathlib.Topology.Compactness.LocallyFinite
import HolomorphicAnosov.Topology.DyadicCoordinateBoxDiameter
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Powerset

/-! # Minimal dyadic faces and the complement CW structure
Source: Hatcher, Algebraic Topology, proof of Theorem A.7, pp.525–526.
The integer-coordinate nesting and minimal-face existence arguments below expand
the omitted details of that construction. All topology is the original Euclidean
subspace topology. The actual CW structure, its finite boundary decompositions,
and affine closed-disk homeomorphisms are constructed explicitly.
-/
noncomputable section
namespace HolomorphicAnosov.DyadicComplement
open Set Metric
variable {N : ℕ}

/-- Closed dyadic coordinate cube; Hatcher pp.525–526. -/
def cube (k : ℕ) (m : Fin N → ℤ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | ∀ j, (m j : ℝ) / (2 : ℝ)^k ≤ x j ∧ x j ≤ ((m j : ℝ)+1)/(2:ℝ)^k}

/-- A cube is selected when it avoids C and no earlier avoiding cube contains it.
Source: Hatcher pp.525–526, the sets A_k. -/
def Selected (C : Set (EuclideanSpace ℝ (Fin N))) (q : ℕ × (Fin N → ℤ)) : Prop :=
  Disjoint (cube q.1 q.2) C ∧
    ∀ l < q.1, ∀ m, cube q.1 q.2 ⊆ cube l m → ¬ Disjoint (cube l m) C

/-- Every dyadic cube has a containing ancestor at any coarser level.
Source: Hatcher pp.525–526, successive dyadic subdivision. Divide each integer
coordinate by 2^(k-l); the quotient and remainder inequalities give inclusion. -/
theorem cube_ancestor (k l : ℕ) (h : l ≤ k) (m : Fin N → ℤ) :
    cube k m ⊆ cube l (fun j ↦ m j / (2 : ℤ)^(k-l)) := by
  intro x hx j
  have hp : 0 < (2 : ℝ)^l := by positivity
  have hd : 0 < (2 : ℝ)^(k-l) := by positivity
  have hz : 0 < (2 : ℤ)^(k-l) := by positivity
  have hpow : (2 : ℝ)^k = (2 : ℝ)^l * (2 : ℝ)^(k-l) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  have hloZ := Int.ediv_mul_le (m j) (ne_of_gt hz)
  have hrem := Int.emod_lt_of_pos (m j) hz
  have heq := Int.ediv_mul_add_emod (m j) ((2 : ℤ)^(k-l))
  have hhiZ : m j + 1 ≤ (m j / (2 : ℤ)^(k-l) + 1) * (2 : ℤ)^(k-l) := by
    nlinarith
  have hlo : ((m j / (2 : ℤ)^(k-l) : ℤ) : ℝ) * (2 : ℝ)^(k-l) ≤ m j := by
    exact_mod_cast hloZ
  have hhi : (m j : ℝ) + 1 ≤
      (((m j / (2 : ℤ)^(k-l) : ℤ) : ℝ) + 1) * (2 : ℝ)^(k-l) := by
    exact_mod_cast hhiZ
  have hxlo := (div_le_iff₀ (show 0 < (2 : ℝ)^k by positivity)).1 (hx j).1
  have hxhi := (le_div_iff₀ (show 0 < (2 : ℝ)^k by positivity)).1 (hx j).2
  rw [hpow] at hxlo hxhi
  constructor
  · apply (div_le_iff₀ hp).2
    exact (mul_le_mul_iff_left₀ hd).1 (by nlinarith)
  · apply (le_div_iff₀ hp).2
    exact (mul_le_mul_iff_left₀ hd).1 (by nlinarith)

/-- The Euclidean diameter of a level-k cube is at most sqrt(N)/2^k.
Source: Hatcher pp.525–526, dyadic size estimate. -/
lemma dist_le_size (k : ℕ) (m : Fin N → ℤ) {x y : EuclideanSpace ℝ (Fin N)}
    (hx : x ∈ cube k m) (hy : y ∈ cube k m) :
    dist x y ≤ Real.sqrt N * (1 / (2 : ℝ)^k) := by
  apply euclidean_coordinate_box_diameter_le _ (by positivity)
  intro j
  rw [Real.dist_eq, abs_le]
  have heq : ((m j : ℝ)+1)/(2:ℝ)^k - (m j : ℝ)/(2:ℝ)^k = 1/(2:ℝ)^k := by ring
  constructor <;> linarith [hx j, hy j]

/-- At bounded dyadic levels, only finitely many grid cubes meet a fixed unit ball.
Source: Hatcher pp.525–526, local finiteness; each integer coordinate is bounded. -/
lemma finite_bounded_levels (K : ℕ) (c : EuclideanSpace ℝ (Fin N)) :
    {q : ℕ × (Fin N → ℤ) | q.1 ≤ K ∧ ∃ x ∈ cube q.1 q.2, dist x c < 1}.Finite := by
  obtain ⟨B, hB⟩ := exists_int_gt ((2 : ℝ)^K * (‖c‖ + 1) + 1)
  apply ((Set.finite_Iic K).prod
    (Set.Finite.pi' fun _ : Fin N ↦ Set.finite_Icc (-B) B)).subset
  rintro ⟨k, m⟩ ⟨hk, x, hx, hxc⟩
  refine ⟨hk, ?_⟩
  intro j
  constructor
  all_goals
    have hp : 0 < (2 : ℝ)^k := by positivity
    have hpK : (2 : ℝ)^k ≤ (2 : ℝ)^K :=
      pow_le_pow_right₀ (by norm_num) hk
    have hxn : ‖x‖ < ‖c‖ + 1 := norm_lt_of_mem_ball hxc
    have hnorm : |x j| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
    have hxj : |x j| < ‖c‖ + 1 := hnorm.trans_lt hxn
    have hlo := (div_le_iff₀ hp).mp (hx j).1
    have hhi := (le_div_iff₀ hp).mp (hx j).2
    have hupper : x j * (2 : ℝ)^k ≤ (‖c‖ + 1) * (2 : ℝ)^K := by
      calc
        x j * (2 : ℝ)^k ≤ (‖c‖ + 1) * (2 : ℝ)^k :=
          mul_le_mul_of_nonneg_right (le_of_lt (abs_lt.mp hxj).2) hp.le
        _ ≤ (‖c‖ + 1) * (2 : ℝ)^K := mul_le_mul_of_nonneg_left hpK (by positivity)
    have hlower : -(‖c‖ + 1) * (2 : ℝ)^K ≤ x j * (2 : ℝ)^k := by
      calc
        -(‖c‖ + 1) * (2 : ℝ)^K ≤ -(‖c‖ + 1) * (2 : ℝ)^k :=
          mul_le_mul_of_nonpos_left hpK (by linarith [norm_nonneg c])
        _ ≤ x j * (2 : ℝ)^k :=
          mul_le_mul_of_nonneg_right (le_of_lt (abs_lt.mp hxj).1) hp.le
  · have hh : (-(B : ℝ)) ≤ (m j : ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (m j : ℝ) ≤ (B : ℝ) := by nlinarith
    exact_mod_cast hh

/-- The selected cubes cover the closed-set complement.
Source: Hatcher pp.525–526; choose the least avoiding level through each point. -/
lemma selected_cover (C : Set (EuclideanSpace ℝ (Fin N))) (hC : IsClosed C)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∉ C) :
    ∃ q, Selected C q ∧ x ∈ cube q.1 q.2 := by
  obtain ⟨k, m, hxm, hdisj, hmin⟩ := closed_complement_dyadic_cube_cover C hC x hx
  exact ⟨(k,m), ⟨hdisj, hmin⟩, hxm⟩

/-- The selected closed cubes form a locally finite family on the original complement.
Source: Hatcher pp.525–526. Choose an avoiding ball at x and a scale K whose
cube diameter is less than half its radius. A selected cube of level greater
than K meeting the half ball would have an avoiding K-ancestor, a contradiction.
Only bounded levels remain, and only finitely many positions at those levels
meet a bounded neighborhood. -/
theorem selected_locallyFinite (C : Set (EuclideanSpace ℝ (Fin N))) (hC : IsClosed C) :
    LocallyFinite (fun q : {q : ℕ × (Fin N → ℤ) // Selected C q} ↦
      {x : ↥(Cᶜ) | x.val ∈ cube q.val.1 q.val.2}) := by
  intro x
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hC.isOpen_compl x.val x.property
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one
    (div_pos (half_pos hr) (show 0 < Real.sqrt N + 1 by positivity))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hsize : Real.sqrt N * (1 / (2 : ℝ)^K) < r / 2 := by
    have hh : 1 / (2 : ℝ)^K < (r / 2) / (Real.sqrt N + 1) := by
      simpa [div_pow] using hK
    have hh' := (lt_div_iff₀ (show 0 < Real.sqrt N + 1 by positivity)).1 hh
    nlinarith [show 0 < 1 / (2 : ℝ)^K by positivity]
  let δ := min (r / 2) 1
  have hδ : 0 < δ := lt_min (half_pos hr) zero_lt_one
  refine ⟨ball x δ, Metric.ball_mem_nhds x hδ, ?_⟩
  apply Set.Finite.of_injOn (f := Subtype.val) ?_
    (fun _ _ _ _ he ↦ Subtype.val_injective he) (finite_bounded_levels K x.val)
  rintro q ⟨y, hyq, hyx⟩
  have hyd : dist y.val x.val < δ := hyx
  refine ⟨?_, y.val, hyq, hyd.trans_le (min_le_right _ _)⟩
  by_contra! hq
  let m := fun j ↦ q.val.2 j / (2 : ℤ)^(q.val.1-K)
  have hsub : cube q.val.1 q.val.2 ⊆ cube K m := cube_ancestor _ _ hq.le _
  apply q.property.2 K hq m hsub
  apply Set.disjoint_left.mpr
  intro z hz hzC
  have hzdist : dist z x.val < r := by
    calc
      dist z x.val ≤ dist z y.val + dist y.val x.val := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add
        ((dist_le_size K m hz (hsub hyq)).trans_lt hsize)
        (hyd.trans_le (min_le_left _ _))
      _ = r := by ring
  exact hb hzdist hzC

end HolomorphicAnosov.DyadicComplement


/-! # Nesting of dyadic open coordinate faces
Source: Hatcher, Algebraic Topology, proof of Theorem A.7, p.526.
-/
noncomputable section
namespace HolomorphicAnosov.DyadicComplement
open Set

/-- A coordinate of a dyadic open face is its lower endpoint, strict interval,
or upper endpoint, encoded respectively by 0, 1, and 2. Source: Hatcher p.526. -/
def faceCoord (k : ℕ) (m : ℤ) (s : Fin 3) (x : ℝ) : Prop :=
  if s = 0 then x = (m : ℝ)/(2:ℝ)^k
  else if s = 1 then (m : ℝ)/(2:ℝ)^k < x ∧ x < ((m : ℝ)+1)/(2:ℝ)^k
  else x = ((m : ℝ)+1)/(2:ℝ)^k

/-- The face coordinate after multiplying by its positive grid denominator.
Source: Hatcher p.526, dyadic coordinates. -/
lemma faceCoord_iff (k : ℕ) (m : ℤ) (s : Fin 3) (x : ℝ) :
    faceCoord k m s x ↔
      if s = 0 then x * (2:ℝ)^k = (m : ℝ)
      else if s = 1 then (m : ℝ) < x * (2:ℝ)^k ∧ x * (2:ℝ)^k < (m : ℝ)+1
      else x * (2:ℝ)^k = (m : ℝ)+1 := by
  have hp : 0 < (2:ℝ)^k := by positivity
  unfold faceCoord
  split_ifs <;> simp only [eq_div_iff (ne_of_gt hp), div_lt_iff₀ hp, lt_div_iff₀ hp]

/-- An integer in a strict interval between consecutive integers is impossible.
Source: integer grid arithmetic used in Hatcher p.526. -/
lemma integer_not_between (a m : ℤ) : ¬ ((m : ℝ) < a ∧ (a : ℝ) < (m : ℝ)+1) := by
  intro h
  have h₁ : m < a := by exact_mod_cast h.1
  have h₂ : a < m + 1 := by exact_mod_cast h.2
  omega

/-- Open unit grid intervals meeting an interval with integer endpoints are
contained in that open interval. Source: dyadic face nesting, Hatcher p.526. -/
lemma unit_interval_nested (a b m : ℤ) {x y : ℝ}
    (hx : (a : ℝ) < x ∧ x < (b : ℝ))
    (hmx : (m : ℝ) < x ∧ x < (m : ℝ)+1)
    (hmy : (m : ℝ) < y ∧ y < (m : ℝ)+1) : (a : ℝ) < y ∧ y < b := by
  have ham : a ≤ m := by
    have hh : (a : ℝ) < (m : ℝ)+1 := hx.1.trans hmx.2
    have hh' : a < m+1 := by exact_mod_cast hh
    omega
  have hmb : m+1 ≤ b := by
    have hh : (m : ℝ) < (b : ℝ) := hmx.1.trans hx.2
    have hh' : m < b := by exact_mod_cast hh
    omega
  constructor
  · exact lt_of_le_of_lt (by exact_mod_cast ham) hmy.1
  · exact lt_of_lt_of_le hmy.2 (by exact_mod_cast hmb)

/-- Meeting open-face coordinates nest from finer to coarser dyadic scale.
Source: Hatcher p.526. Multiplication by the fine denominator turns coarse
endpoints into integers. A fine open unit interval cannot meet an integer
singleton, and if it meets a coarse open interval its endpoints lie between
the coarse endpoints. Fine singleton coordinates are immediate. -/
theorem faceCoord_nested {k l : ℕ} (hkl : k ≤ l) (a b : ℤ) (s t : Fin 3)
    {x y : ℝ} (hxs : faceCoord k a s x) (hxt : faceCoord l b t x)
    (hyt : faceCoord l b t y) : faceCoord k a s y := by
  have hd : 0 < (2 : ℝ)^(l-k) := by positivity
  have hl : 0 < (2 : ℝ)^l := by positivity
  have hp : (2 : ℝ)^l = (2 : ℝ)^k * (2 : ℝ)^(l-k) := by
    rw [← pow_add, Nat.add_sub_of_le hkl]
  rw [faceCoord_iff] at hxs hxt hyt ⊢
  by_cases ht0 : t = 0
  · simp only [ht0, ↓reduceIte] at hxt hyt
    have he : y = x := (mul_right_cancel₀ (ne_of_gt hl)) (hyt.trans hxt.symm)
    simpa only [he] using hxs
  by_cases ht1 : t = 1
  · simp only [ht1, ↓reduceIte] at hxt hyt
    by_cases hs0 : s = 0
    · simp only [hs0, ↓reduceIte] at hxs
      have he : x * (2 : ℝ)^l = ((a * (2 : ℤ)^(l-k) : ℤ) : ℝ) := by
        rw [hp, ← mul_assoc, hxs]
        push_cast
        rfl
      rw [he] at hxt
      exact (integer_not_between _ b hxt).elim
    by_cases hs1 : s = 1
    · simp only [hs1, ↓reduceIte] at hxs ⊢
      have hx : (((a * (2 : ℤ)^(l-k) : ℤ) : ℝ) < x * (2 : ℝ)^l) ∧
          (x * (2 : ℝ)^l < (((a+1) * (2 : ℤ)^(l-k) : ℤ) : ℝ)) := by
        push_cast
        rw [hp, ← mul_assoc]
        exact ⟨mul_lt_mul_of_pos_right hxs.1 hd, mul_lt_mul_of_pos_right hxs.2 hd⟩
      have hy := unit_interval_nested (a*(2:ℤ)^(l-k)) ((a+1)*(2:ℤ)^(l-k)) b hx hxt hyt
      push_cast at hy
      rw [hp, ← mul_assoc] at hy
      exact ⟨(mul_lt_mul_iff_left₀ hd).1 hy.1, (mul_lt_mul_iff_left₀ hd).1 hy.2⟩
    · simp only [hs0, hs1, ↓reduceIte] at hxs
      have he : x * (2 : ℝ)^l = (((a+1) * (2 : ℤ)^(l-k) : ℤ) : ℝ) := by
        rw [hp, ← mul_assoc, hxs]
        push_cast
        rfl
      rw [he] at hxt
      exact (integer_not_between _ b hxt).elim
  · simp only [ht0, ht1, ↓reduceIte] at hxt hyt
    have he : y = x := (mul_right_cancel₀ (ne_of_gt hl)) (hyt.trans hxt.symm)
    simpa only [he] using hxs

/-- Product open faces of a dyadic cube. Source: Hatcher p.526. -/
def openFace {N : ℕ} (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) :
    Set (EuclideanSpace ℝ (Fin N)) := {x | ∀ j, faceCoord k (m j) (s j) (x j)}

/-- Intersecting dyadic open faces nest in the direction of increasing grid level.
Source: Hatcher p.526; apply the one-coordinate nesting in each coordinate. -/
theorem openFace_nested {N k l : ℕ} (hkl : k ≤ l)
    (a b : Fin N → ℤ) (s t : Fin N → Fin 3)
    (h : (openFace k a s ∩ openFace l b t).Nonempty) :
    openFace l b t ⊆ openFace k a s := by
  obtain ⟨x, hx, hxt⟩ := h
  intro y hy j
  exact faceCoord_nested hkl (a j) (b j) (s j) (t j) (hx j) (hxt j) (hy j)

end HolomorphicAnosov.DyadicComplement

namespace HolomorphicAnosov.DyadicComplement
open Set Metric
variable {N : ℕ}

/-- Lower and upper coordinates of a closed face; Hatcher p.526. -/
def faceLower (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) (j : Fin N) : ℝ :=
  if s j = 2 then ((m j : ℝ)+1)/(2:ℝ)^k else (m j : ℝ)/(2:ℝ)^k

/-- Upper endpoint of a coordinate face, including its fixed endpoint coordinates.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
def faceUpper (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) (j : Fin N) : ℝ :=
  if s j = 0 then (m j : ℝ)/(2:ℝ)^k else ((m j : ℝ)+1)/(2:ℝ)^k

/-- Closed coordinate face; Hatcher p.526. -/
def closedFace (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {x | ∀ j, faceLower k m s j ≤ x j ∧ x j ≤ faceUpper k m s j}

lemma grid_lt (k : ℕ) (m : ℤ) : (m : ℝ)/(2:ℝ)^k < ((m : ℝ)+1)/(2:ℝ)^k :=
  (div_lt_div_iff_of_pos_right (by positivity)).2 (by linarith)

lemma openFace_subset_closedFace (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) :
    openFace k m s ⊆ closedFace k m s := by
  intro x hx j
  have h := hx j
  have hs : s j = 0 ∨ s j = 1 ∨ s j = 2 := by omega
  rcases hs with hs | hs | hs <;> simp [faceCoord, faceLower, faceUpper, hs] at h ⊢
  · exact ⟨h.ge, h.le⟩
  · exact ⟨h.1.le, h.2.le⟩
  · exact ⟨h.ge, h.le⟩

lemma closedFace_subset_cube (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) :
    closedFace k m s ⊆ cube k m := by
  intro x hx j
  have h := hx j
  have hg := (grid_lt k (m j)).le
  have hs : s j = 0 ∨ s j = 1 ∨ s j = 2 := by omega
  rcases hs with hs | hs | hs <;> simp [faceLower, faceUpper, hs] at h
  · exact ⟨h.1, h.2.trans hg⟩
  · exact h
  · exact ⟨hg.trans h.1, h.2⟩

lemma closure_faceCoord (k : ℕ) (m : ℤ) (s : Fin 3) :
    closure {x : ℝ | faceCoord k m s x} =
      Icc (if s = 2 then ((m : ℝ)+1)/(2:ℝ)^k else (m : ℝ)/(2:ℝ)^k)
        (if s = 0 then (m : ℝ)/(2:ℝ)^k else ((m : ℝ)+1)/(2:ℝ)^k) := by
  fin_cases s
  · simp [faceCoord]
  · change closure (Ioo ((m : ℝ)/(2:ℝ)^k) (((m : ℝ)+1)/(2:ℝ)^k)) = _
    exact closure_Ioo (grid_lt k m).ne
  · simp [faceCoord]

/-- Closure of each open face is its corresponding closed face; Hatcher p.526.
The coordinate map is a homeomorphism, so closure is computed coordinatewise. -/
lemma closure_openFace (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) :
    closure (openFace k m s) = closedFace k m s := by
  let e := EuclideanSpace.equiv (Fin N) ℝ
  have ho : openFace k m s = e ⁻¹' pi univ (fun j ↦ {x | faceCoord k (m j) (s j) x}) := by
    ext x
    simp [openFace, e]
  rw [ho, ← e.preimage_closure, closure_pi_set]
  simp only [closure_faceCoord]
  ext x
  simp only [closedFace, faceLower, faceUpper, e, mem_preimage, mem_pi,
    mem_univ, forall_const, mem_Icc, Set.mem_ofPred_eq]
  rfl

/-- Every point of a cube lies in one of its open faces; Hatcher p.526. -/
lemma exists_openFace (k : ℕ) (m : Fin N → ℤ) {x : EuclideanSpace ℝ (Fin N)}
    (hx : x ∈ cube k m) : ∃ s : Fin N → Fin 3, x ∈ openFace k m s := by
  classical
  let s : Fin N → Fin 3 := fun j ↦
    if x j = (m j : ℝ)/(2:ℝ)^k then 0
    else if x j = ((m j : ℝ)+1)/(2:ℝ)^k then 2 else 1
  refine ⟨s, fun j ↦ ?_⟩
  by_cases h₀ : x j = (m j : ℝ)/(2:ℝ)^k
  · simp [s, faceCoord, h₀]
  by_cases h₁ : x j = ((m j : ℝ)+1)/(2:ℝ)^k
  · simp [s, faceCoord, h₁]
  simp only [s, h₀, h₁, ↓reduceIte, faceCoord, Fin.reduceEq]
  exact ⟨lt_of_le_of_ne (hx j).1 (Ne.symm h₀), lt_of_le_of_ne (hx j).2 h₁⟩

lemma full_closedFace (k : ℕ) (m : Fin N → ℤ) :
    closedFace k m (fun _ ↦ 1) = cube k m := by
  ext x
  simp [closedFace, cube, faceLower, faceUpper]

/-- The closure of the interior face is the whole cube; Hatcher pp.525–526. -/
lemma closure_full_openFace (k : ℕ) (m : Fin N → ℤ) :
    closure (openFace k m (fun _ ↦ 1)) = cube k m := by
  rw [closure_openFace, full_closedFace]

end HolomorphicAnosov.DyadicComplement

namespace HolomorphicAnosov.DyadicComplement
open Set Metric
open scoped Topology _root_.Topology
variable {N : ℕ}

lemma openFace_nonempty (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3) :
    (openFace k m s).Nonempty := by
  let x : EuclideanSpace ℝ (Fin N) := (EuclideanSpace.equiv (Fin N) ℝ).symm
    (fun j ↦ if s j = 0 then (m j : ℝ)/(2:ℝ)^k
      else if s j = 1 then ((m j : ℝ) + 1/2)/(2:ℝ)^k
      else ((m j : ℝ)+1)/(2:ℝ)^k)
  refine ⟨x, fun j ↦ ?_⟩
  change faceCoord k (m j) (s j) (if s j = 0 then _ else if s j = 1 then _ else _)
  unfold faceCoord
  split_ifs
  · rfl
  · constructor <;> apply (div_lt_div_iff_of_pos_right (by positivity)).2 <;> linarith
  · rfl

/-- Every complement point belongs to an open face that is minimal among all
selected-cube open faces. Source: Hatcher p.526. Choose a selected cube of
finest level through the point. If its face contained a proper smaller face,
the latter cube's ancestor would contain the whole first face. Approaching the
point through that ancestor's interior forces a finer selected cube through
the point, by local finiteness and closedness, contrary to maximality. -/
theorem exists_minimal_openFace (C : Set (EuclideanSpace ℝ (Fin N))) (hC : IsClosed C)
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∉ C) :
    ∃ (q : ℕ × (Fin N → ℤ)) (s : Fin N → Fin 3),
      Selected C q ∧ x ∈ openFace q.1 q.2 s ∧
      ∀ (r : ℕ × (Fin N → ℤ)) (t : Fin N → Fin 3), Selected C r →
        openFace r.1 r.2 t ⊆ openFace q.1 q.2 s →
        openFace q.1 q.2 s ⊆ openFace r.1 r.2 t := by
  classical
  let I := {q : ℕ × (Fin N → ℤ) // Selected C q}
  let Q : I → Set ↥(Cᶜ) := fun q ↦ {y | y.val ∈ cube q.val.1 q.val.2}
  let x' : ↥(Cᶜ) := ⟨x, hx⟩
  have hlf : LocallyFinite Q := selected_locallyFinite C hC
  have hclosed (q : I) : IsClosed (Q q) :=
    (dyadic_cube_compact q.val.1 q.val.2).isClosed.preimage continuous_subtype_val
  have hf := hlf.point_finite x'
  have hne : {q | x' ∈ Q q}.Nonempty := by
    obtain ⟨q, hq, hxq⟩ := selected_cover C hC x hx
    exact ⟨⟨q, hq⟩, hxq⟩
  obtain ⟨q, hqx, hqmax⟩ := Finset.exists_max_image hf.toFinset (fun q : I ↦ q.val.1)
    (by simpa using hne)
  simp only [Set.Finite.mem_toFinset] at hqx hqmax
  obtain ⟨s, hxs⟩ := exists_openFace q.val.1 q.val.2 hqx
  refine ⟨q.val, s, q.property, hxs, ?_⟩
  intro r t hr hsub
  obtain ⟨z, hzt⟩ := openFace_nonempty r.1 r.2 t
  by_cases hlevel : r.1 ≤ q.val.1
  · exact openFace_nested hlevel r.2 q.val.2 t s ⟨z, hzt, hsub hzt⟩
  have hlt : q.val.1 < r.1 := lt_of_not_ge hlevel
  let m : Fin N → ℤ := fun j ↦ r.2 j / (2 : ℤ)^(r.1-q.val.1)
  have hrP : cube r.1 r.2 ⊆ cube q.val.1 m := cube_ancestor _ _ hlt.le _
  have hzP : z ∈ cube q.val.1 m := hrP
    (closedFace_subset_cube _ _ _ (openFace_subset_closedFace _ _ _ hzt))
  obtain ⟨u, hzu⟩ := exists_openFace q.val.1 m hzP
  have hF : openFace q.val.1 q.val.2 s ⊆ openFace q.val.1 m u :=
    openFace_nested le_rfl m q.val.2 u s ⟨z, hzu, hsub hzt⟩
  have hxP : x ∈ cube q.val.1 m :=
    closedFace_subset_cube _ _ _ (openFace_subset_closedFace _ _ _ (hF hxs))
  have hxcl : x' ∈ closure {y : ↥(Cᶜ) | y.val ∈ openFace q.val.1 m (fun _ ↦ 1)} := by
    change x' ∈ closure (Subtype.val ⁻¹' openFace q.val.1 m (fun _ ↦ 1))
    rw [← hC.isOpen_compl.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (openFace q.val.1 m (fun _ ↦ 1)), closure_full_openFace]
    exact hxP
  obtain ⟨y, hstar, hyP⟩ := mem_closure_iff_nhds.mp hxcl _ (hlf.iInter_compl_mem_nhds hclosed x')
  obtain ⟨v, hv, hyv⟩ := selected_cover C hC y.val y.property
  have hxv : x' ∈ Q ⟨v, hv⟩ := by
    by_contra hn
    exact (mem_iInter₂.mp hstar ⟨v, hv⟩ hn) hyv
  have hvlevel : v.1 ≤ q.val.1 := hqmax ⟨v, hv⟩ hxv
  obtain ⟨w, hyw⟩ := exists_openFace v.1 v.2 hyv
  have hPV : cube q.val.1 m ⊆ cube v.1 v.2 := by
    rw [← closure_full_openFace q.val.1 m]
    apply (closure_mono (openFace_nested hvlevel v.2 m w (fun _ ↦ 1)
      ⟨y.val, hyw, hyP⟩)).trans
    rw [closure_openFace]
    exact closedFace_subset_cube _ _ _
  exact (hr.2 v.1 (hvlevel.trans_lt hlt) v.2 (hrP.trans hPV) hv.1).elim

end HolomorphicAnosov.DyadicComplement

namespace HolomorphicAnosov.DyadicComplement
open Set Metric
variable {N : ℕ}

lemma openFace_coord_surjective (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3)
    (j : Fin N) {a : ℝ} (ha : faceCoord k (m j) (s j) a) :
    ∃ x ∈ openFace k m s, x j = a := by
  classical
  obtain ⟨z, hz⟩ := openFace_nonempty k m s
  let x : EuclideanSpace ℝ (Fin N) := (EuclideanSpace.equiv (Fin N) ℝ).symm
    (fun i ↦ if i = j then a else z i)
  refine ⟨x, ?_, ?_⟩
  · intro i
    change faceCoord k (m i) (s i) (if i = j then a else z i)
    by_cases h : i = j
    · simpa [h] using ha
    · simpa [h] using hz i
  · change (if j = j then a else z j) = a
    simp

/-- Containment of open faces preserves active-coordinate inclusion.
Source: Hatcher p.526. Varying an active coordinate produces two distinct
values, so it cannot be fixed in any containing open face. -/
lemma active_subset_of_openFace_subset {k l : ℕ} {a b : Fin N → ℤ} {s t : Fin N → Fin 3}
    (h : openFace k a s ⊆ openFace l b t) (j : Fin N) (hs : s j = 1) : t j = 1 := by
  have hp : 0 < (2 : ℝ)^k := by positivity
  have hz₁ : faceCoord k (a j) (s j) (((a j : ℝ)+1/3)/(2:ℝ)^k) := by
    simp only [faceCoord, hs, Fin.reduceEq, ↓reduceIte]
    constructor <;> apply (div_lt_div_iff_of_pos_right hp).2 <;> linarith
  have hz₂ : faceCoord k (a j) (s j) (((a j : ℝ)+2/3)/(2:ℝ)^k) := by
    simp only [faceCoord, hs, Fin.reduceEq, ↓reduceIte]
    constructor <;> apply (div_lt_div_iff_of_pos_right hp).2 <;> linarith
  obtain ⟨x, hx, hxj⟩ := openFace_coord_surjective k a s j hz₁
  obtain ⟨y, hy, hyj⟩ := openFace_coord_surjective k a s j hz₂
  have hxt := h hx j
  have hyt := h hy j
  rw [hxj] at hxt
  rw [hyj] at hyt
  by_contra ht
  have he : ((a j : ℝ)+1/3)/(2:ℝ)^k = ((a j : ℝ)+2/3)/(2:ℝ)^k := by
    unfold faceCoord at hxt hyt
    by_cases ht0 : t j = 0
    · simp only [ht0, ↓reduceIte] at hxt hyt
      exact hxt.trans hyt.symm
    · simp only [ht0, ht, ↓reduceIte] at hxt hyt
      exact hxt.trans hyt.symm
  have := (div_left_inj' (ne_of_gt hp)).1 he
  linarith

/-- Active coordinates of a face. Source: Hatcher p.526. -/
def active (s : Fin N → Fin 3) : Finset (Fin N) := Finset.univ.filter (fun j ↦ s j = 1)

lemma dim_mono {k l : ℕ} {a b : Fin N → ℤ} {s t : Fin N → Fin 3}
    (h : openFace k a s ⊆ openFace l b t) : (active s).card ≤ (active t).card := by
  apply Finset.card_le_card
  intro j hj
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact active_subset_of_openFace_subset h j hj

/-- The open face through a boundary point of a closed face at the same grid
level is a proper lower-dimensional face. Source: Hatcher p.526.
Inactive coordinates remain fixed. If every previously active coordinate were
still active, the point would have belonged to the original open face. -/
lemma boundary_openFace (k : ℕ) (m : Fin N → ℤ) (s : Fin N → Fin 3)
    {x : EuclideanSpace ℝ (Fin N)} (hx : x ∈ closedFace k m s) (hxo : x ∉ openFace k m s) :
    ∃ t : Fin N → Fin 3, x ∈ openFace k m t ∧
      closedFace k m t ⊆ closedFace k m s \ openFace k m s ∧ (active t).card < (active s).card := by
  classical
  obtain ⟨t, hxt⟩ := exists_openFace k m (closedFace_subset_cube k m s hx)
  have hfixed (j : Fin N) (hj : s j ≠ 1) : t j = s j := by
    have hxj := hx j
    have htj := hxt j
    have hlt := grid_lt k (m j)
    have hs : s j = 0 ∨ s j = 2 := by omega
    have ht : t j = 0 ∨ t j = 1 ∨ t j = 2 := by omega
    rcases hs with hs | hs <;> rcases ht with ht | ht | ht <;>
      simp [faceLower, faceUpper, faceCoord, hs, ht] at hxj htj ⊢ <;> linarith
  have hsub : active t ⊆ active s := by
    intro j hj
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_contra hs
    exact hs ((hfixed j hs).symm.trans hj)
  have hne : active t ≠ active s := by
    intro he
    apply hxo
    intro j
    by_cases hs : s j = 1
    · have ht : t j = 1 := by
        have hj : j ∈ active t := he.symm ▸ (by simp [active, hs])
        simpa [active] using hj
      simpa only [ht, hs] using hxt j
    · rw [← hfixed j hs]
      exact hxt j
  refine ⟨t, hxt, ?_, Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)⟩
  intro y hy
  constructor
  · intro j
    by_cases hs : s j = 1
    · have hyc := closedFace_subset_cube k m t hy j
      simpa [faceLower, faceUpper, hs] using hyc
    · have he := hfixed j hs
      simpa only [faceLower, faceUpper, he] using hy j
  · intro hyo
    obtain ⟨j, hjs, hjt⟩ := Finset.exists_of_ssubset (ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hs : s j = 1 := by simpa [active] using hjs
    have ht : t j ≠ 1 := by simpa [active] using hjt
    have hyj := hy j
    have hoj := hyo j
    have htt : t j = 0 ∨ t j = 2 := by omega
    rcases htt with htt | htt <;> simp [faceLower, faceUpper, faceCoord, hs, htt] at hyj hoj <;>
      linarith

end HolomorphicAnosov.DyadicComplement

namespace HolomorphicAnosov.DyadicComplement
open Set Metric
variable {N : ℕ} (C : Set (EuclideanSpace ℝ (Fin N)))

/-- A minimal selected-cube open face, identified by its actual point set.
Source: Hatcher p.526, minimal open faces give the cells. -/
def IsCell (F : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∃ q : {q : ℕ × (Fin N → ℤ) // Selected C q}, ∃ s : Fin N → Fin 3,
    F = openFace q.val.1 q.val.2 s ∧
    ∀ (r : ℕ × (Fin N → ℤ)) (t : Fin N → Fin 3), Selected C r →
      openFace r.1 r.2 t ⊆ F → F ⊆ openFace r.1 r.2 t

abbrev Cell := {F : Set (EuclideanSpace ℝ (Fin N)) // IsCell C F}

namespace Cell
variable {C}
/-- A selected cube presenting this minimal face.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
noncomputable def cubeIndex (f : Cell C) := f.property.choose
/-- The endpoint or interval choice presenting the minimal face in its chosen cube.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
noncomputable def shape (f : Cell C) := f.property.choose_spec.choose
lemma carrier_eq (f : Cell C) :
    f.val = openFace f.cubeIndex.val.1 f.cubeIndex.val.2 f.shape :=
  f.property.choose_spec.choose_spec.1
lemma minimal (f : Cell C) (r : ℕ × (Fin N → ℤ)) (t : Fin N → Fin 3)
    (hr : Selected C r) (hsub : openFace r.1 r.2 t ⊆ f.val) :
    f.val ⊆ openFace r.1 r.2 t :=
  f.property.choose_spec.choose_spec.2 r t hr hsub

/-- Dimension of a minimal face, counted by its active coordinates.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
def dim (f : Cell C) : ℕ := (active f.shape).card

/-- Closure of a minimal face, viewed inside the original complement.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
def closed (f : Cell C) : Set ↥(Cᶜ) := Subtype.val ⁻¹' closure f.val

/-- The minimal relative open face viewed inside the original complement.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
def openCell (f : Cell C) : Set ↥(Cᶜ) := Subtype.val ⁻¹' f.val

lemma closure_eq (f : Cell C) :
    closure f.val = closedFace f.cubeIndex.val.1 f.cubeIndex.val.2 f.shape := by
  rw [f.carrier_eq, closure_openFace]
lemma closure_subset_cube (f : Cell C) :
    closure f.val ⊆ cube f.cubeIndex.val.1 f.cubeIndex.val.2 := by
  rw [f.closure_eq]
  exact closedFace_subset_cube _ _ _
lemma closure_subset_compl (f : Cell C) : closure f.val ⊆ Cᶜ := by
  intro x hx hc
  exact Set.disjoint_left.mp f.cubeIndex.property.1 (f.closure_subset_cube hx) hc
lemma nonempty (f : Cell C) : f.val.Nonempty := by
  rw [f.carrier_eq]
  exact openFace_nonempty _ _ _
lemma closed_nonempty (f : Cell C) : f.closed.Nonempty := by
  obtain ⟨x, hx⟩ := f.nonempty
  exact ⟨⟨x, f.closure_subset_compl (subset_closure hx)⟩, subset_closure hx⟩
lemma open_subset_closed (f : Cell C) : f.openCell ⊆ f.closed :=
  fun _ hx ↦ subset_closure hx
lemma closed_isClosed (f : Cell C) : IsClosed f.closed :=
  isClosed_closure.preimage continuous_subtype_val
lemma closed_isCompact (f : Cell C) : IsCompact f.closed := by
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' _
    (by simpa only [Subtype.range_coe] using f.closure_subset_compl)
  rw [f.closure_eq]
  apply coordinate_box_compact
  intro j
  unfold faceLower faceUpper
  have hs : f.shape j = 0 ∨ f.shape j = 1 ∨ f.shape j = 2 := by omega
  rcases hs with hs | hs | hs <;> simp [hs, (grid_lt _ _).le]

lemma subset_of_inter (f : Cell C) (r : ℕ × (Fin N → ℤ)) (t : Fin N → Fin 3)
    (hr : Selected C r) (hi : (f.val ∩ openFace r.1 r.2 t).Nonempty) :
    f.val ⊆ openFace r.1 r.2 t := by
  rw [f.carrier_eq] at hi
  rcases le_total r.1 f.cubeIndex.val.1 with h | h
  · rw [f.carrier_eq]
    exact openFace_nested h r.2 f.cubeIndex.val.2 t f.shape (Set.inter_comm _ _ ▸ hi)
  · apply f.minimal r t hr
    rw [f.carrier_eq]
    exact openFace_nested h f.cubeIndex.val.2 r.2 f.shape t hi

lemma eq_of_inter (f g : Cell C) (h : (f.val ∩ g.val).Nonempty) : f = g := by
  apply Subtype.ext
  apply Set.Subset.antisymm
  · rw [g.carrier_eq] at h ⊢
    exact f.subset_of_inter _ _ g.cubeIndex.property h
  · rw [f.carrier_eq] at h ⊢
    exact g.subset_of_inter _ _ f.cubeIndex.property (Set.inter_comm _ _ ▸ h)

lemma dim_le (f : Cell C) : f.dim ≤ N := by
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)

lemma data_injective : Function.Injective
    (fun f : Cell C ↦ (f.cubeIndex, f.shape)) := by
  intro f g he
  apply Subtype.ext
  rw [f.carrier_eq, g.carrier_eq]
  have hq : f.cubeIndex = g.cubeIndex := congrArg Prod.fst he
  have hs : f.shape = g.shape := congrArg Prod.snd he
  rw [hq, hs]

lemma locallyFinite (hC : IsClosed C) : LocallyFinite (fun f : Cell C ↦ f.closed) := by
  intro x
  obtain ⟨U, hU, hf⟩ := selected_locallyFinite C hC x
  refine ⟨U, hU, ?_⟩
  apply Set.Finite.of_injOn (f := fun f : Cell C ↦ (f.cubeIndex, f.shape)) ?_
    (fun _ _ _ _ h ↦ data_injective h) (hf.prod (Set.toFinite (univ : Set (Fin N → Fin 3))))
  rintro f ⟨y, hyf, hyU⟩
  exact ⟨⟨y, f.closure_subset_cube hyf, hyU⟩, Set.mem_univ _⟩

lemma exists_at (hC : IsClosed C) (x : EuclideanSpace ℝ (Fin N)) (hx : x ∉ C) :
    ∃ f : Cell C, x ∈ f.val := by
  obtain ⟨q, s, hq, hxs, hmin⟩ := exists_minimal_openFace C hC x hx
  exact ⟨⟨openFace q.1 q.2 s, ⟨⟨q,hq⟩,s,rfl,hmin⟩⟩, hxs⟩

/-- Every boundary point lies in a cell of smaller dimension whose entire
closed cell lies in that boundary. Source: Hatcher p.526. -/
lemma boundary_cover (hC : IsClosed C) (f : Cell C) (x : ↥(Cᶜ))
    (hx : x ∈ f.closed \ f.openCell) :
    ∃ g : Cell C, x ∈ g.openCell ∧ g.dim < f.dim ∧ g.closed ⊆ f.closed \ f.openCell := by
  obtain ⟨g, hxg⟩ := exists_at hC x.val x.property
  have hxcl := hx.1
  change x.val ∈ closure f.val at hxcl
  rw [f.closure_eq] at hxcl
  have hxnot : x.val ∉ openFace f.cubeIndex.val.1 f.cubeIndex.val.2 f.shape := by
    rw [← f.carrier_eq]
    exact hx.2
  obtain ⟨t, hxt, htsub, htdim⟩ := boundary_openFace _ _ _ hxcl hxnot
  have hgsub := g.subset_of_inter _ t f.cubeIndex.property ⟨x.val,hxg,hxt⟩
  refine ⟨g, hxg, (dim_mono (by simpa only [g.carrier_eq] using hgsub)).trans_lt htdim, ?_⟩
  intro y hyg
  have hh := closure_mono hgsub hyg
  rw [closure_openFace] at hh
  have hh' := htsub hh
  change y.val ∈ closure f.val ∧ y.val ∉ f.val
  rw [f.closure_eq, f.carrier_eq]
  exact hh'

/-- A cell's boundary is a finite union of closed cells of smaller dimension.
Source: Hatcher p.526. Compactness and local finiteness make the boundary's
covering cells finite, and the pointwise boundary lemma gives exact equality. -/
theorem finite_boundary (hC : IsClosed C) (f : Cell C) :
    ∃ F : Finset (Cell C), (∀ g ∈ F, g.dim < f.dim) ∧
      f.closed \ f.openCell = ⋃ g ∈ F, g.closed := by
  classical
  let S : Set (Cell C) := {g | g.dim < f.dim ∧ g.closed ⊆ f.closed \ f.openCell}
  have hf : S.Finite := by
    apply ((locallyFinite hC).finite_nonempty_inter_compact f.closed_isCompact).subset
    intro g hg
    obtain ⟨x,hx⟩ := g.closed_nonempty
    exact ⟨x,hx,(hg.2 hx).1⟩
  refine ⟨hf.toFinset, fun g hg ↦ (hf.mem_toFinset.mp hg).1, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨g,hxg,hdim,hsub⟩ := boundary_cover hC f x hx
    exact mem_iUnion₂.mpr ⟨g, hf.mem_toFinset.mpr ⟨hdim,hsub⟩,g.open_subset_closed hxg⟩
  · intro hx
    obtain ⟨g,hg,hxg⟩ := mem_iUnion₂.mp hx
    exact (hf.mem_toFinset.mp hg).2 hxg

end Cell
end HolomorphicAnosov.DyadicComplement

namespace HolomorphicAnosov.DyadicComplement.Cell
open Set Metric
variable {N : ℕ} {C : Set (EuclideanSpace ℝ (Fin N))}

/-- Enumeration of active face coordinates; Hatcher p.526, characteristic boxes. -/
def enum (f : Cell C) : Fin f.dim ≃ ↥(active f.shape) :=
  (Fintype.equivFinOfCardEq (by simp [dim])).symm

/-- Embed the parameter coordinates as the active ambient coordinates.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
def embed (f : Cell C) : Fin f.dim ↪ Fin N :=
  f.enum.toEmbedding.trans (Function.Embedding.subtype _)

lemma shape_embed (f : Cell C) (i : Fin f.dim) : f.shape (f.embed i) = 1 := by
  exact (Finset.mem_filter.mp (f.enum i).property).2

lemma range_embed (f : Cell C) (j : Fin N) : j ∈ Set.range f.embed ↔ f.shape j = 1 := by
  constructor
  · rintro ⟨i,rfl⟩
    exact f.shape_embed i
  · intro hj
    refine ⟨f.enum.symm ⟨j, by simp [active, hj]⟩, ?_⟩
    change (f.enum (f.enum.symm _)).val = j
    simp

/-- Lower ambient coordinate endpoints of the minimal closed face.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
def lower (f : Cell C) := faceLower f.cubeIndex.val.1 f.cubeIndex.val.2 f.shape
/-- Upper ambient coordinate endpoints of the minimal closed face.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
def upper (f : Cell C) := faceUpper f.cubeIndex.val.1 f.cubeIndex.val.2 f.shape

lemma lower_le_upper (f : Cell C) (j : Fin N) : f.lower j ≤ f.upper j := by
  have hs : f.shape j = 0 ∨ f.shape j = 1 ∨ f.shape j = 2 := by omega
  rcases hs with hs | hs | hs <;> simp [lower, upper, faceLower, faceUpper, hs, (grid_lt _ _).le]

lemma lower_lt_iff (f : Cell C) (j : Fin N) : f.lower j < f.upper j ↔ j ∈ Set.range f.embed := by
  rw [f.range_embed]
  have hs : f.shape j = 0 ∨ f.shape j = 1 ∨ f.shape j = 2 := by omega
  rcases hs with hs | hs | hs <;> simp [lower, upper, faceLower, faceUpper, hs, grid_lt]

/-- The affine parametrization of a closed coordinate face; Hatcher p.526. -/
def affine (f : Cell C) (u : Fin f.dim → ℝ) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm (fun j ↦
    if hj : f.shape j = 1 then
      ((f.cubeIndex.val.2 j : ℝ) + (u (f.enum.symm ⟨j, by simp [active, hj]⟩) + 1)/2) /
        (2:ℝ)^f.cubeIndex.val.1
    else f.lower j)

lemma affine_embed (f : Cell C) (u : Fin f.dim → ℝ) (i : Fin f.dim) :
    f.affine u (f.embed i) = ((f.cubeIndex.val.2 (f.embed i) : ℝ) + (u i+1)/2) /
      (2:ℝ)^f.cubeIndex.val.1 := by
  change (if h : f.shape (f.embed i) = 1 then _ else _) = _
  rw [dite_eq_left (f.shape_embed i)]
  have he : f.enum.symm ⟨f.embed i, by simp [active, f.shape_embed]⟩ = i :=
    f.enum.symm_apply_apply i
  rw [he]

lemma affine_inactive (f : Cell C) (u : Fin f.dim → ℝ) (j : Fin N)
    (hj : j ∉ Set.range f.embed) : f.affine u j = f.lower j := by
  change (if h : f.shape j = 1 then _ else _) = _
  exact dite_eq_right (fun h ↦ hj ((f.range_embed j).2 h))

lemma continuous_affine (f : Cell C) : Continuous f.affine := by
  apply (EuclideanSpace.equiv (Fin N) ℝ).symm.continuous.comp
  apply continuous_pi
  intro j
  split_ifs
  · fun_prop
  · exact continuous_const

/-- Clamp a coordinate to the closed parameter interval; it is the identity
on the native closed ball. This extends characteristic maps off that ball. -/
def clamp {d : ℕ} (u : Fin d → ℝ) : Fin d → ℝ := fun i ↦ max (-1) (min 1 (u i))

lemma continuous_clamp {d : ℕ} : Continuous (@clamp d) := by
  apply continuous_pi
  intro i
  exact continuous_const.max (continuous_const.min (continuous_apply i))

lemma clamp_mem {d : ℕ} (u : Fin d → ℝ) : clamp u ∈ closedBall 0 1 := by
  rw [coordinate_closedBall_iff]
  intro i
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clamp_eq {d : ℕ} (u : Fin d → ℝ) (hu : u ∈ closedBall 0 1) : clamp u = u := by
  funext i
  have hi := (coordinate_closedBall_iff u).mp hu i
  exact (max_eq_right (hi.1.trans_eq (min_eq_right hi.2).symm)).trans (min_eq_right hi.2)

lemma affine_mem_closed (f : Cell C) {u : Fin f.dim → ℝ} (hu : u ∈ closedBall 0 1) :
    f.affine u ∈ closure f.val := by
  rw [f.closure_eq]
  intro j
  by_cases hj : j ∈ Set.range f.embed
  · obtain ⟨i,rfl⟩ := hj
    rw [f.affine_embed]
    have hs := f.shape_embed i
    have hi := (coordinate_closedBall_iff u).mp hu i
    simp only [faceLower, faceUpper, hs, Fin.reduceEq, ↓reduceIte]
    constructor
    · apply (div_le_div_iff_of_pos_right (by positivity)).2
      linarith
    · apply (div_le_div_iff_of_pos_right (by positivity)).2
      linarith
  · rw [f.affine_inactive _ _ hj]
    have he : f.lower j = f.upper j := le_antisymm (f.lower_le_upper j)
      (le_of_not_gt (fun h ↦ hj ((f.lower_lt_iff j).1 h)))
    change f.lower j ≤ f.lower j ∧ f.lower j ≤ f.upper j
    exact ⟨le_rfl,f.lower_le_upper j⟩

/-- Native total forward characteristic map, clamped outside the closed ball.
Source: Hatcher p.526, affine characteristic boxes. -/
def forward (f : Cell C) (u : Fin f.dim → ℝ) : ↥(Cᶜ) :=
  ⟨f.affine (clamp u), f.closure_subset_compl (f.affine_mem_closed (clamp_mem u))⟩

lemma continuous_forward (f : Cell C) : Continuous f.forward :=
  (f.continuous_affine.comp continuous_clamp).subtype_mk _

/-- Inverse affine coordinates along the active axes; Hatcher p.526. -/
def inverse (f : Cell C) (x : ↥(Cᶜ)) (i : Fin f.dim) : ℝ :=
  (x.val (f.embed i) * (2:ℝ)^f.cubeIndex.val.1 - f.cubeIndex.val.2 (f.embed i)) * 2 - 1

lemma continuous_inverse (f : Cell C) : Continuous f.inverse := by
  apply continuous_pi
  intro i
  exact ((((EuclideanSpace.proj (f.embed i)).continuous.comp continuous_subtype_val).mul_const _
    |>.sub continuous_const).mul_const 2 |>.sub continuous_const)

lemma inverse_forward (f : Cell C) {u : Fin f.dim → ℝ} (hu : u ∈ closedBall 0 1) :
    f.inverse (f.forward u) = u := by
  funext i
  change ((f.affine (clamp u)) (f.embed i) * _ - _) * 2 - 1 = _
  rw [clamp_eq u hu, f.affine_embed, div_mul_cancel₀ _ (by positivity)]
  ring

lemma inverse_mem_closed (f : Cell C) {x : ↥(Cᶜ)} (hx : x ∈ f.closed) :
    f.inverse x ∈ closedBall 0 1 := by
  rw [coordinate_closedBall_iff]
  intro i
  have hi := hx
  change x.val ∈ closure f.val at hi
  rw [f.closure_eq] at hi
  have hj := hi (f.embed i)
  simp only [faceLower, faceUpper, f.shape_embed, Fin.reduceEq, ↓reduceIte] at hj
  have hp : 0 < (2:ℝ)^f.cubeIndex.val.1 := by positivity
  have hlo := (div_le_iff₀ hp).1 hj.1
  have hhi := (le_div_iff₀ hp).1 hj.2
  dsimp [inverse]
  constructor <;> linarith

lemma forward_inverse (f : Cell C) {x : ↥(Cᶜ)} (hx : x ∈ f.closed) :
    f.forward (f.inverse x) = x := by
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin N) ℝ).injective
  funext j
  change f.affine (clamp (f.inverse x)) j = x.val j
  rw [clamp_eq _ (f.inverse_mem_closed hx)]
  by_cases hj : j ∈ Set.range f.embed
  · obtain ⟨i,rfl⟩ := hj
    rw [f.affine_embed]
    dsimp [inverse]
    field_simp
    ring
  · rw [f.affine_inactive _ _ hj]
    have hi := hx
    change x.val ∈ closure f.val at hi
    rw [f.closure_eq] at hi
    have hab : f.lower j = f.upper j := le_antisymm (f.lower_le_upper j)
      (le_of_not_gt (fun h ↦ hj ((f.lower_lt_iff j).1 h)))
    have hh : f.lower j ≤ x.val j ∧ x.val j ≤ f.upper j := hi j
    exact le_antisymm hh.1 (hab ▸ hh.2)

end HolomorphicAnosov.DyadicComplement.Cell

namespace HolomorphicAnosov.DyadicComplement.Cell
open Set Metric
variable {N : ℕ} {C : Set (EuclideanSpace ℝ (Fin N))}

lemma forward_mem_open (f : Cell C) {u : Fin f.dim → ℝ} (hu : u ∈ ball 0 1) :
    f.forward u ∈ f.openCell := by
  change f.affine (clamp u) ∈ f.val
  rw [clamp_eq u (ball_subset_closedBall hu), f.carrier_eq]
  intro j
  by_cases hj : j ∈ Set.range f.embed
  · obtain ⟨i,rfl⟩ := hj
    rw [f.affine_embed]
    have hi := (coordinate_ball_iff u).mp hu i
    simp only [faceCoord, f.shape_embed, Fin.reduceEq, ↓reduceIte]
    constructor <;> apply (div_lt_div_iff_of_pos_right (by positivity)).2 <;> linarith
  · rw [f.affine_inactive _ _ hj]
    have hs : f.shape j ≠ 1 := fun h ↦ hj ((f.range_embed j).2 h)
    have hs' : f.shape j = 0 ∨ f.shape j = 2 := by omega
    rcases hs' with hs' | hs' <;> simp [lower, faceLower, faceCoord, hs']

lemma inverse_mem_open (f : Cell C) {x : ↥(Cᶜ)} (hx : x ∈ f.openCell) :
    f.inverse x ∈ ball 0 1 := by
  rw [coordinate_ball_iff]
  intro i
  change x.val ∈ f.val at hx
  rw [f.carrier_eq] at hx
  have hi := hx (f.embed i)
  simp only [faceCoord, f.shape_embed, Fin.reduceEq, ↓reduceIte] at hi
  have hp : 0 < (2:ℝ)^f.cubeIndex.val.1 := by positivity
  have hlo := (div_lt_iff₀ hp).1 hi.1
  have hhi := (lt_div_iff₀ hp).1 hi.2
  dsimp [inverse]
  constructor <;> linarith

/-- Affine characteristic partial equivalence for a minimal dyadic face.
Source: Hatcher p.526. It is inverse on the open disk and continuous on the
closed disk; clamping outside the disk makes its total function complement-valued. -/
noncomputable def characteristic (f : Cell C) : PartialEquiv (Fin f.dim → ℝ) ↥(Cᶜ) where
  toFun := f.forward
  invFun := f.inverse
  source := ball 0 1
  target := f.openCell
  map_source' := fun _ hu ↦ f.forward_mem_open hu
  map_target' := fun _ hx ↦ f.inverse_mem_open hx
  left_inv' := fun _ hu ↦ f.inverse_forward (ball_subset_closedBall hu)
  right_inv' := fun _ hx ↦ f.forward_inverse (f.open_subset_closed hx)

lemma image_closedBall (f : Cell C) : f.characteristic '' closedBall 0 1 = f.closed := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact f.affine_mem_closed (clamp_mem u)
  · intro hx
    exact ⟨f.inverse x,f.inverse_mem_closed hx,f.forward_inverse hx⟩

lemma image_ball (f : Cell C) : f.characteristic '' ball 0 1 = f.openCell :=
  f.characteristic.image_source_eq_target

lemma image_sphere (f : Cell C) :
    f.characteristic '' sphere 0 1 = f.closed \ f.openCell := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨f.affine_mem_closed (clamp_mem u), ?_⟩
    intro hx
    have hi := f.inverse_mem_open hx
    change f.inverse (f.forward u) ∈ ball 0 1 at hi
    rw [f.inverse_forward (sphere_subset_closedBall hu)] at hi
    exact (ne_of_lt (mem_ball_zero_iff.mp hi)) (mem_sphere_zero_iff_norm.mp hu)
  · rintro ⟨hc, ho⟩
    have hu := f.inverse_mem_closed hc
    have hnu : f.inverse x ∉ ball 0 1 := by
      intro h
      have hh := f.forward_mem_open h
      rw [f.forward_inverse hc] at hh
      exact ho hh
    refine ⟨f.inverse x, ?_, f.forward_inverse hc⟩
    rw [mem_sphere_zero_iff_norm]
    have hle := mem_closedBall_zero_iff.mp hu
    have hge : 1 ≤ ‖f.inverse x‖ := le_of_not_gt (fun h ↦ hnu (mem_ball_zero_iff.mpr h))
    exact le_antisymm hle hge

/-- The closed-disk restriction is a homeomorphism onto the closed cell.
Source: Hatcher p.526, regular affine coordinate cells. Both maps are the
explicit continuous affine coordinates, including in dimension zero. -/
noncomputable def closedHomeomorph (f : Cell C) :
    ↥(closedBall (0 : Fin f.dim → ℝ) 1) ≃ₜ ↥f.closed where
  toFun u := ⟨f.forward u.val, f.affine_mem_closed (clamp_mem u.val)⟩
  invFun x := ⟨f.inverse x.val, f.inverse_mem_closed x.property⟩
  left_inv u := Subtype.ext (f.inverse_forward u.property)
  right_inv x := Subtype.ext (f.forward_inverse x.property)
  continuous_toFun := (f.continuous_forward.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (f.continuous_inverse.comp continuous_subtype_val).subtype_mk _

lemma characteristic_formula (f : Cell C) (u : Fin f.dim → ℝ) (hu : u ∈ closedBall 0 1) :
    (∀ i : Fin f.dim, (f.characteristic u).val (f.embed i) =
      (f.lower (f.embed i) + f.upper (f.embed i))/2 +
        (f.upper (f.embed i) - f.lower (f.embed i)) * u i / 2) ∧
    (∀ j : Fin N, j ∉ Set.range f.embed → (f.characteristic u).val j = f.lower j) := by
  constructor
  · intro i
    change f.affine (clamp u) (f.embed i) = _
    rw [clamp_eq u hu, f.affine_embed]
    simp only [lower, upper, faceLower, faceUpper, f.shape_embed, Fin.reduceEq, ↓reduceIte]
    ring
  · intro j hj
    exact f.affine_inactive _ _ hj

lemma closed_eq_box (f : Cell C) :
    f.closed = {x : ↥(Cᶜ) | ∀ j, f.lower j ≤ x.val j ∧ x.val j ≤ f.upper j} := by
  unfold closed
  rw [f.closure_eq]
  rfl

lemma open_eq_box (f : Cell C) : f.openCell =
    {x : ↥(Cᶜ) | (∀ i : Fin f.dim, f.lower (f.embed i) < x.val (f.embed i) ∧
      x.val (f.embed i) < f.upper (f.embed i)) ∧
      ∀ j : Fin N, j ∉ Set.range f.embed → x.val j = f.lower j} := by
  ext x
  change x.val ∈ f.val ↔ _
  rw [f.carrier_eq]
  constructor
  · intro hx
    constructor
    · intro i
      have hi := hx (f.embed i)
      simpa only [faceCoord, lower, upper, faceLower, faceUpper, f.shape_embed,
        Fin.reduceEq, ↓reduceIte] using hi
    · intro j hj
      have hs : f.shape j ≠ 1 := fun h ↦ hj ((f.range_embed j).2 h)
      have hs' : f.shape j = 0 ∨ f.shape j = 2 := by omega
      have hi := hx j
      rcases hs' with hs' | hs' <;> simpa [faceCoord, lower, faceLower, hs'] using hi
  · rintro ⟨ha,hb⟩ j
    by_cases hj : j ∈ Set.range f.embed
    · obtain ⟨i,rfl⟩ := hj
      simpa only [faceCoord, lower, upper, faceLower, faceUpper, f.shape_embed,
        Fin.reduceEq, ↓reduceIte] using ha i
    · have hs : f.shape j ≠ 1 := fun h ↦ hj ((f.range_embed j).2 h)
      have hs' : f.shape j = 0 ∨ f.shape j = 2 := by omega
      rw [hb j hj]
      rcases hs' with hs' | hs' <;> simp [faceCoord, lower, faceLower, hs']

end HolomorphicAnosov.DyadicComplement.Cell

namespace HolomorphicAnosov.DyadicComplement
open Set Metric
variable {N : ℕ} (C : Set (EuclideanSpace ℝ (Fin N)))

/-- Dimension-indexed cells from the minimal dyadic open faces. Source: Hatcher p.526. -/
abbrev Cells (n : ℕ) := {f : Cell C // f.dim = n}

/-- Characteristic maps transported to the dimension-indexed cell family.
Source: Hatcher, proof of Theorem A.7, pp.525–526. -/
noncomputable def maps (n : ℕ) (i : Cells C n) : PartialEquiv (Fin n → ℝ) ↥(Cᶜ) :=
  i.property ▸ i.val.characteristic

lemma maps_image_closed (n : ℕ) (i : Cells C n) :
    maps C n i '' closedBall 0 1 = i.val.closed := by
  rcases i with ⟨f, rfl⟩
  exact f.image_closedBall
lemma maps_image_open (n : ℕ) (i : Cells C n) :
    maps C n i '' ball 0 1 = i.val.openCell := by
  rcases i with ⟨f, rfl⟩
  exact f.image_ball
lemma maps_image_sphere (n : ℕ) (i : Cells C n) :
    maps C n i '' sphere 0 1 = i.val.closed \ i.val.openCell := by
  rcases i with ⟨f, rfl⟩
  exact f.image_sphere

/-- The actual CW structure of the closed-set complement obtained from minimal
dyadic faces. Source: Hatcher Theorem A.7, pp.525–526. Closure finiteness follows
from the finite boundary decomposition; the weak topology follows from the
locally finite closed cover in the original complement topology. -/
@[instance_reducible]
noncomputable def cw (hC : IsClosed C) : Topology.CWComplex (univ : Set ↥(Cᶜ)) where
  cell := Cells C
  map := maps C
  source_eq := by
    rintro n ⟨f,rfl⟩
    rfl
  continuousOn := by
    rintro n ⟨f,rfl⟩
    exact f.continuous_forward.continuousOn
  continuousOn_symm := by
    rintro n ⟨f,rfl⟩
    exact f.continuous_inverse.continuousOn
  pairwiseDisjoint' := by
    rintro ⟨n,⟨f,hf⟩⟩ _ ⟨m,⟨g,hg⟩⟩ _ hne
    subst n
    subst m
    change Disjoint (maps C f.dim ⟨f,rfl⟩ '' ball 0 1) (maps C g.dim ⟨g,rfl⟩ '' ball 0 1)
    rw [maps_image_open, maps_image_open]
    apply Set.disjoint_left.mpr
    intro x hx hy
    have he := f.eq_of_inter g ⟨x.val,hx,hy⟩
    subst g
    exact hne rfl
  mapsTo' := by
    classical
    rintro n ⟨f,rfl⟩
    obtain ⟨F,hF,hboundary⟩ := f.finite_boundary hC
    refine ⟨fun m ↦ F.subtype (fun g : Cell C ↦ g.dim = m), ?_⟩
    intro u hu
    have hh : maps C f.dim ⟨f,rfl⟩ u ∈ f.closed \ f.openCell := by
      rw [← maps_image_sphere C f.dim ⟨f,rfl⟩]
      exact ⟨u,hu,rfl⟩
    rw [hboundary] at hh
    obtain ⟨g,hg,hhg⟩ := mem_iUnion₂.mp hh
    refine mem_iUnion.mpr ⟨g.dim, mem_iUnion.mpr ⟨hF g hg,
      mem_iUnion.mpr ⟨⟨g,rfl⟩, mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩⟩
    · simpa using hg
    · rw [maps_image_closed]
      exact hhg
  closed' := by
    intro A _ hA
    have hlf := (Cell.locallyFinite hC).subset (g := fun f ↦ A ∩ f.closed)
      (fun _ ↦ inter_subset_right)
    have hc : IsClosed (⋃ f : Cell C, A ∩ f.closed) := hlf.isClosed_iUnion (by
      intro f
      simpa only [maps_image_closed] using hA f.dim ⟨f,rfl⟩)
    have he : (⋃ f : Cell C, A ∩ f.closed) = A := by
      ext x
      constructor
      · intro hx
        obtain ⟨f,hf⟩ := mem_iUnion.mp hx
        exact hf.1
      · intro hx
        obtain ⟨f,hxf⟩ := Cell.exists_at hC x.val x.property
        exact mem_iUnion.mpr ⟨f,hx,f.open_subset_closed hxf⟩
    rwa [he] at hc
  union' := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨f,hxf⟩ := Cell.exists_at hC x.val x.property
    refine mem_iUnion.mpr ⟨f.dim, mem_iUnion.mpr ⟨⟨f,rfl⟩, ?_⟩⟩
    rw [maps_image_closed]
    exact f.open_subset_closed hxf

end HolomorphicAnosov.DyadicComplement

namespace HolomorphicAnosov.DyadicComplement
variable {N : ℕ} {C : Set (EuclideanSpace ℝ (Fin N))}

/-- Forgetting the dimension label identifies the dependent cell family with
its actual minimal-face cells. Source: Hatcher p.526, indexing by dimension. -/
def cellsEquiv : (Σ n, Cells C n) ≃ Cell C where
  toFun i := i.2.val
  invFun f := ⟨f.dim, ⟨f,rfl⟩⟩
  left_inv := by
    rintro ⟨n,⟨f,rfl⟩⟩
    rfl
  right_inv _ := rfl

end HolomorphicAnosov.DyadicComplement
