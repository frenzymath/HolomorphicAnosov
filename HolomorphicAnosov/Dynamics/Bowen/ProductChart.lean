import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic

namespace HolomorphicAnosov
namespace Bowen

/-- Closed local stable set from Bowen, *Markov Partitions*, p.727, defined by all forward iterates. -/
private def stableSet {X : Type*} [PseudoMetricSpace X]
    (f : X ≃ₜ X) (δ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f : X → X)^[n] y) ((f : X → X)^[n] x) ≤ δ}

/-- Closed local unstable set from Bowen, *Markov Partitions*, p.727, defined by all inverse iterates. -/
private def unstableSet {X : Type*} [PseudoMetricSpace X]
    (f : X ≃ₜ X) (δ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] x) ≤ δ}

/-- Points related in both original time directions at radius γ are equal.
Source: Bowen Fact 1 at the diagonal pair, whose unique intersection contains x. -/
private theorem diagonal_unique {X : Type*} [MetricSpace X] (f : X ≃ₜ X)
    (γ ε : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hunique : ∀ a b : X, dist a b ≤ ε →
      ∃! z, z ∈ stableSet f γ a ∧ z ∈ unstableSet f γ b)
    (x z : X) (hs : z ∈ stableSet f γ x) (hu : z ∈ unstableSet f γ x) : z = x := by
  have hx : x ∈ stableSet f γ x ∧ x ∈ unstableSet f γ x :=
    ⟨fun _ ↦ by simpa using hγ.le, fun _ ↦ by simpa using hγ.le⟩
  exact (hunique x x (by simpa using hε.le)).unique ⟨hs, hu⟩ hx

/-- Two narrow original orbit intersections coincide when the sum of their
stable and unstable radii is at most γ. This is triangle inequality followed
by Fact 1 diagonal uniqueness, and uses no uniqueness for a distant pair. -/
private theorem orbit_intersection_unique {X : Type*} [MetricSpace X]
    (f : X ≃ₜ X) (γ ε δ δ' η η' : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hδ : δ + δ' ≤ γ) (hη : η + η' ≤ γ)
    (hunique : ∀ a b : X, dist a b ≤ ε →
      ∃! z, z ∈ stableSet f γ a ∧ z ∈ unstableSet f γ b)
    (a b z w : X) (hzs : z ∈ stableSet f δ a) (hws : w ∈ stableSet f δ' a)
    (hzu : z ∈ unstableSet f η b) (hwu : w ∈ unstableSet f η' b) : z = w := by
  apply diagonal_unique f γ ε hγ hε hunique w z
  · intro n
    calc
      dist (((f : X → X)^[n]) z) (((f : X → X)^[n]) w) ≤
        dist (((f : X → X)^[n]) z) (((f : X → X)^[n]) a) +
          dist (((f : X → X)^[n]) a) (((f : X → X)^[n]) w) := dist_triangle _ _ _
      _ ≤ δ + δ' := add_le_add (hzs n) (by simpa only [dist_comm] using hws n)
      _ ≤ γ := hδ
  · intro n
    calc
      dist (((f.symm : X → X)^[n]) z) (((f.symm : X → X)^[n]) w) ≤
        dist (((f.symm : X → X)^[n]) z) (((f.symm : X → X)^[n]) b) +
          dist (((f.symm : X → X)^[n]) b) (((f.symm : X → X)^[n]) w) := dist_triangle _ _ _
      _ ≤ η + η' := add_le_add (hzu n) (by simpa only [dist_comm] using hwu n)
      _ ≤ γ := hη

/-- Closed graph on a genuine narrow modulus domain. The graph is the literal
closed orbit relation because diagonal uniqueness identifies each narrow fibre.
Source: Bowen Fact 1 and Bredon's compact-factor closed-projection theorem. -/
private theorem bracket_modulus_continuous
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ ε δ : ℝ) (hγ : 0 < γ) (hε : 0 < ε)
    (hδγ : 2 * δ ≤ γ) (εmod : ℝ → ℝ) (bracket : X → X → X)
    (hmodulus : ∀ a b : X, dist a b ≤ εmod δ →
      bracket a b ∈ stableSet f δ a ∧ bracket a b ∈ unstableSet f δ b)
    (hunique : ∀ a b : X, dist a b ≤ ε →
      ∃! z, z ∈ stableSet f γ a ∧ z ∈ unstableSet f γ b) :
    ContinuousOn (fun p : X × X => bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ εmod δ} := by
  let A : Set (X × X) := {p | dist p.1 p.2 ≤ εmod δ}
  let b : A → X := fun p ↦ bracket p.val.1 p.val.2
  let R : Set (A × X) := {q |
    q.2 ∈ stableSet f δ q.1.val.1 ∧ q.2 ∈ unstableSet f δ q.1.val.2}
  have hR : IsClosed R := by
    change IsClosed ({q : A × X | ∀ n : ℕ,
      dist (((f : X → X)^[n]) q.2) (((f : X → X)^[n]) q.1.val.1) ≤ δ} ∩
      {q : A × X | ∀ n : ℕ,
      dist (((f.symm : X → X)^[n]) q.2) (((f.symm : X → X)^[n]) q.1.val.2) ≤ δ})
    simp only [Set.ofPred_forall]
    apply IsClosed.inter <;> apply isClosed_iInter <;> intro n
    · exact isClosed_le
        (((f.continuous.iterate n).comp continuous_snd).dist
          ((f.continuous.iterate n).comp
            (continuous_fst.comp (continuous_subtype_val.comp continuous_fst)))) continuous_const
    · exact isClosed_le
        (((f.symm.continuous.iterate n).comp continuous_snd).dist
          ((f.symm.continuous.iterate n).comp
            (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)))) continuous_const
  have hgraph : b.graph = R := by
    ext q
    change b q.1 = q.2 ↔ _
    constructor
    · intro h
      change q.2 ∈ stableSet f δ q.1.val.1 ∧ q.2 ∈ unstableSet f δ q.1.val.2
      rw [← h]
      exact hmodulus q.1.val.1 q.1.val.2 q.1.property
    · intro h
      have hb := hmodulus q.1.val.1 q.1.val.2 q.1.property
      apply diagonal_unique f γ ε hγ hε hunique q.2 (b q.1)
      · intro n
        calc
          dist (((f : X → X)^[n]) (b q.1)) (((f : X → X)^[n]) q.2) ≤
            dist (((f : X → X)^[n]) (b q.1)) (((f : X → X)^[n]) q.1.val.1) +
              dist (((f : X → X)^[n]) q.1.val.1) (((f : X → X)^[n]) q.2) := dist_triangle _ _ _
          _ ≤ δ + δ := add_le_add (hb.1 n) (by simpa [dist_comm] using h.1 n)
          _ ≤ γ := by linarith
      · intro n
        calc
          dist (((f.symm : X → X)^[n]) (b q.1)) (((f.symm : X → X)^[n]) q.2) ≤
            dist (((f.symm : X → X)^[n]) (b q.1)) (((f.symm : X → X)^[n]) q.1.val.2) +
              dist (((f.symm : X → X)^[n]) q.1.val.2) (((f.symm : X → X)^[n]) q.2) := dist_triangle _ _ _
          _ ≤ δ + δ := add_le_add (hb.2 n) (by simpa [dist_comm] using h.2 n)
          _ ≤ γ := by linarith
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_of_isClosed_graph (hgraph ▸ hR))

/--
Product chart from Bowen's canonical coordinates (Bowen, *Markov Partitions for
Axiom A Diffeomorphisms*, Fact 1 p.727, Lemma 5 and the scale choice p.728;
Shub, *Stabilité globale des systèmes dynamiques*, Proposition 10.15,
pp.150–151).  The closed orbit sets are written with the forward and inverse
iterates of the original homeomorphism, so their subspace topologies are the
native ones.  The total Lean argument `bracket : X → X → X` represents the source's
partially specified bracket: its values on each modulus domain are constrained
by the displayed membership hypotheses, while no regularity or extension
hypothesis outside those domains is added.  Continuity on every such closed
domain is part of the conclusion.  The proof uses Shub's two projections and open-preimage argument,
and the compact-factor closed-projection proof of Bredon, *Topology and
Geometry* I§8 Proposition 8.2 (printed p.22), applied to the literal orbit
relation.  No manifold, differentiability, connectedness, or global extension
of the bracket is assumed.  Empty factors are included by the same statement.
-/
theorem bowen_fact1_product_chart_g6
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X ≃ₜ X) (lam γ ε : ℝ)
    (hlam : 0 < lam) (hlam1 : lam < 1) (hγ : 0 < γ) (hε : 0 < ε)
    (α : Fin 5 → ℝ) (εmod : ℝ → ℝ)
    (hεmod : ∀ δ, 0 < δ → δ ≤ γ → 0 < εmod δ)
    (hα0 : α 0 = γ)
    (hαpos : ∀ i, 0 < α i)
    (hαscale : ∀ i : Fin 4,
      α i.succ < (1 / 3 : ℝ) * min (α i.castSucc / 3) (εmod (α i.castSucc / 3)))
    (hsmall : ∀ i : Fin 4, ∀ a b : X,
      dist a b ≤ α i.succ →
        dist (f a) (f b) < α i.castSucc ∧ dist (f.symm a) (f.symm b) < α i.castSucc)
    (bracket : X → X → X)
    (hcontract_s : ∀ (x y z : X) (n : ℕ),
      y ∈ stableSet f γ x → z ∈ stableSet f γ x →
      dist ((f : X → X)^[n] y) ((f : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (hcontract_u : ∀ (x y z : X) (n : ℕ),
      y ∈ unstableSet f γ x → z ∈ unstableSet f γ x →
      dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (hunique : ∀ a b : X, dist a b ≤ ε →
      ∃! z, z ∈ stableSet f γ a ∧ z ∈ unstableSet f γ b)
    (hbracket_mem : ∀ a b : X, dist a b ≤ ε →
      bracket a b ∈ stableSet f γ a ∧ bracket a b ∈ unstableSet f γ b)
    (hbracket_cont : ContinuousOn (fun p : X × X => bracket p.1 p.2)
      {p | dist p.1 p.2 ≤ ε})
    (hmodulus : ∀ δ, 0 < δ → δ ≤ γ → ∀ a b : X,
      dist a b ≤ εmod δ →
      bracket a b ∈ stableSet f δ a ∧ bracket a b ∈ unstableSet f δ b) :
    (∀ δ, 0 < δ → δ ≤ γ / 3 →
      ContinuousOn (fun p : X × X => bracket p.1 p.2)
        {p | dist p.1 p.2 ≤ εmod δ}) ∧
    (∀ x : X, ∀ U V : Set X,
      U ⊆ unstableSet f (α 2) x → V ⊆ stableSet f (α 2) x →
      IsOpen {u : unstableSet f γ x | (u : X) ∈ U} →
      IsOpen {v : stableSet f γ x | (v : X) ∈ V} →
      let UV : Set X := {z | ∃ u ∈ U, ∃ v ∈ V, bracket u v = z}
      IsOpen UV ∧
      ∃ h : Homeomorph
          ({u : unstableSet f γ x // (u : X) ∈ U} × {v : stableSet f γ x // (v : X) ∈ V})
          {z : X // z ∈ UV},
        (∀ p, ((h p : {z : X // z ∈ UV}) : X) = bracket p.1 p.2) ∧
        (∀ z : {z : X // z ∈ UV},
          ((h.symm z).1 : X) = bracket (z : X) x ∧
          ((h.symm z).2 : X) = bracket x (z : X))) := by
  -- Retain the exact source interface; narrow membership and diagonal uniqueness
  -- give this chart without needing the stronger contraction/one-step inputs.
  have _ := hlam
  have _ := hlam1
  have _ := hεmod
  have _ := hsmall
  have _ := hcontract_s
  have _ := hcontract_u
  have _ := hbracket_mem
  have _ := hbracket_cont
  have hcont : ∀ δ, 0 < δ → δ ≤ γ / 3 →
      ContinuousOn (fun p : X × X => bracket p.1 p.2)
        {p | dist p.1 p.2 ≤ εmod δ} := by
    intro δ hδ hδγ
    exact bracket_modulus_continuous f γ ε δ hγ hε (by linarith)
      εmod bracket (hmodulus δ hδ (by linarith)) hunique
  refine ⟨hcont, ?_⟩
  intro x U V hU hV hUopen hVopen
  have hscale0a : α 1 < γ / 9 := by
    have h := lt_of_lt_of_le (hαscale 0)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, hα0] at h
    linarith
  have hscale0b : α 1 < εmod (γ / 3) / 3 := by
    have h := lt_of_lt_of_le (hαscale 0)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    simp only [Fin.succ_zero_eq_one, Fin.castSucc_zero, hα0] at h
    linarith
  have hscale1a : α 2 < α 1 / 9 := by
    have h := lt_of_lt_of_le (hαscale 1)
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    norm_num at h ⊢
    linarith
  have hscale1b : 3 * α 2 < εmod (α 1 / 3) := by
    have h := lt_of_lt_of_le (hαscale 1)
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    norm_num at h ⊢
    linarith
  have hβpos : 0 < α 1 / 3 := by linarith [hαpos 1]
  have hβγ : α 1 / 3 ≤ γ / 3 := by linarith [hαpos 1]
  have hβmem (u v : X) (hu : u ∈ U) (hv : v ∈ V) :
      bracket u v ∈ stableSet f (α 1 / 3) u ∧
        bracket u v ∈ unstableSet f (α 1 / 3) v := by
    apply hmodulus (α 1 / 3) hβpos (by linarith) u v
    calc
      dist u v ≤ dist u x + dist x v := dist_triangle _ _ _
      _ ≤ α 2 + α 2 := add_le_add
        (by simpa only [Function.iterate_zero, id_eq] using hU hu 0)
        (by simpa only [Function.iterate_zero, id_eq, dist_comm] using hV hv 0)
      _ ≤ εmod (α 1 / 3) := by linarith [hαpos 2]
  let O : Set X := {q | dist q x < εmod (γ / 3)}
  have hO : IsOpen O := isOpen_lt (continuous_id.dist continuous_const) continuous_const
  have hqO (u v : X) (hu : u ∈ U) (hv : v ∈ V) : bracket u v ∈ O := by
    have hm := hβmem u v hu hv
    calc
      dist (bracket u v) x ≤ dist (bracket u v) u + dist u x := dist_triangle _ _ _
      _ ≤ α 1 / 3 + α 2 := add_le_add
        (by simpa only [Function.iterate_zero, id_eq] using hm.1 0)
        (by simpa only [Function.iterate_zero, id_eq] using hU hu 0)
      _ < εmod (γ / 3) := by linarith
  have hproj (q : O) :
      (bracket q.val x ∈ stableSet f (γ / 3) q.val ∧
        bracket q.val x ∈ unstableSet f (γ / 3) x) ∧
      (bracket x q.val ∈ stableSet f (γ / 3) x ∧
        bracket x q.val ∈ unstableSet f (γ / 3) q.val) := by
    constructor
    · exact hmodulus (γ / 3) (by positivity) (by linarith) q.val x q.property.le
    · apply hmodulus (γ / 3) (by positivity) (by linarith) x q.val
      have hq : dist q.val x ≤ εmod (γ / 3) := q.property.le
      change dist x q.val ≤ εmod (γ / 3)
      simpa only [dist_comm] using hq
  have hinverse (u v : X) (hu : u ∈ U) (hv : v ∈ V) :
      bracket (bracket u v) x = u ∧ bracket x (bracket u v) = v := by
    have hm := hβmem u v hu hv
    have hp := hproj ⟨bracket u v, hqO u v hu hv⟩
    constructor
    · apply orbit_intersection_unique f γ ε (γ / 3) (α 1 / 3) (γ / 3) (α 2)
        hγ hε (by linarith) (by linarith) hunique (bracket u v) x
        (bracket (bracket u v) x) u hp.1.1 _ hp.1.2 (hU hu)
      intro n
      simpa only [dist_comm] using hm.1 n
    · apply orbit_intersection_unique f γ ε (γ / 3) (α 2) (γ / 3) (α 1 / 3)
        hγ hε (by linarith) (by linarith) hunique x (bracket u v)
        (bracket x (bracket u v)) v hp.2.1 (hV hv) hp.2.2 _
      intro n
      simpa only [dist_comm] using hm.2 n
  let pu : O → unstableSet f γ x := fun q ↦ ⟨bracket q.val x,
    fun n ↦ (hproj q).1.2 n |>.trans (by linarith)⟩
  let ps : O → stableSet f γ x := fun q ↦ ⟨bracket x q.val,
    fun n ↦ (hproj q).2.1 n |>.trans (by linarith)⟩
  have hcu : Continuous pu := by
    apply Continuous.subtype_mk
    exact (hcont (γ / 3) (by positivity) le_rfl).comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun q ↦ by
        change dist q.val x ≤ εmod (γ / 3)
        exact q.property.le)
  have hcs : Continuous ps := by
    apply Continuous.subtype_mk
    apply (hcont (γ / 3) (by positivity) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_subtype_val)
    intro q
    have hq : dist q.val x ≤ εmod (γ / 3) := q.property.le
    change dist x q.val ≤ εmod (γ / 3)
    simpa only [dist_comm] using hq
  let UV : Set X := {z | ∃ u ∈ U, ∃ v ∈ V, bracket u v = z}
  have hUV_O : UV ⊆ O := by
    rintro q ⟨u,hu,v,hv,rfl⟩
    exact hqO u v hu hv
  have reconstruct (q : O) (hu : (pu q : X) ∈ U) (hv : (ps q : X) ∈ V) :
      bracket (pu q) (ps q) = q.val := by
    have hm := hβmem _ _ hu hv
    have hp := hproj q
    apply orbit_intersection_unique f γ ε (α 1 / 3) (γ / 3)
      (α 1 / 3) (γ / 3) hγ hε (by linarith) (by linarith) hunique
      (pu q) (ps q) (bracket (pu q) (ps q)) q.val hm.1 _ hm.2 _
    · intro n
      simpa only [pu, dist_comm] using hp.1.1 n
    · intro n
      simpa only [ps, dist_comm] using hp.2.2 n
  have hUVeq : UV = Subtype.val ''
      (pu ⁻¹' {u : unstableSet f γ x | (u : X) ∈ U} ∩
        ps ⁻¹' {v : stableSet f γ x | (v : X) ∈ V}) := by
    ext q
    constructor
    · rintro ⟨u,hu,v,hv,rfl⟩
      refine ⟨⟨bracket u v, hqO u v hu hv⟩, ?_, rfl⟩
      have hi := hinverse u v hu hv
      exact ⟨by simpa only [Set.mem_preimage, Set.mem_ofPred_eq, pu, hi.1] using hu,
        by simpa only [Set.mem_preimage, Set.mem_ofPred_eq, ps, hi.2] using hv⟩
    · rintro ⟨q, ⟨hu,hv⟩, rfl⟩
      exact ⟨pu q, hu, ps q, hv, reconstruct q hu hv⟩
  have hopen : IsOpen UV := by
    rw [hUVeq]
    exact hO.isOpenMap_subtype_val _
      ((hUopen.preimage hcu).inter (hVopen.preimage hcs))
  have hcoords (q : UV) : (pu ⟨q.val, hUV_O q.property⟩ : X) ∈ U ∧
      (ps ⟨q.val, hUV_O q.property⟩ : X) ∈ V := by
    rcases q.property with ⟨u,hu,v,hv,hq⟩
    have hi := hinverse u v hu hv
    constructor
    · change bracket q.val x ∈ U
      rw [← hq, hi.1]
      exact hu
    · change bracket x q.val ∈ V
      rw [← hq, hi.2]
      exact hv
  let P := {u : unstableSet f γ x // (u : X) ∈ U} ×
      {v : stableSet f γ x // (v : X) ∈ V}
  have hforward : Continuous (fun p : P ↦ bracket p.1.val.val p.2.val.val) := by
    apply (hcont (α 1 / 3) hβpos hβγ).comp_continuous
      (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd))
    intro p
    calc
      dist p.1.val.val p.2.val.val ≤ dist p.1.val.val x + dist x p.2.val.val := dist_triangle _ _ _
      _ ≤ α 2 + α 2 := add_le_add
        (by simpa only [Function.iterate_zero, id_eq] using hU p.1.property 0)
        (by simpa only [Function.iterate_zero, id_eq, dist_comm] using hV p.2.property 0)
      _ ≤ εmod (α 1 / 3) := by linarith [hαpos 2]
  let toO : UV → O := fun q ↦ ⟨q.val, hUV_O q.property⟩
  have htoO : Continuous toO := continuous_subtype_val.subtype_mk _
  let h : P ≃ₜ UV :=
    { toFun := fun p ↦ ⟨bracket p.1.val.val p.2.val.val,
        p.1.val.val, p.1.property, p.2.val.val, p.2.property, rfl⟩
      invFun := fun q ↦ (⟨pu (toO q), (hcoords q).1⟩,
        ⟨ps (toO q), (hcoords q).2⟩)
      left_inv := by
        intro p
        apply Prod.ext <;> apply Subtype.ext <;> apply Subtype.ext
        · exact (hinverse _ _ p.1.property p.2.property).1
        · exact (hinverse _ _ p.1.property p.2.property).2
      right_inv := by
        intro q
        apply Subtype.ext
        exact reconstruct (toO q) (hcoords q).1 (hcoords q).2
      continuous_toFun := hforward.subtype_mk _
      continuous_invFun := ((hcu.comp htoO).subtype_mk _).prodMk
        ((hcs.comp htoO).subtype_mk _) }
  exact ⟨hopen, h, fun _ ↦ rfl, fun _ ↦ ⟨rfl, rfl⟩⟩


end Bowen
end HolomorphicAnosov
