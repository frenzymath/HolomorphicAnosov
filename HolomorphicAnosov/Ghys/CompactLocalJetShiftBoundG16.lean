import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

noncomputable section
namespace HolomorphicAnosov.Ghys
open Set Filter Function
open scoped Topology
universe u v w x

/-- Over a compact base subset in continuous first- and second-jet flowbox charts, the principal
shift from a continuous homogeneous section to the local quadratic-zero section is bounded by a
constant times any positive continuous homogeneous first-jet norm. (Ghys, Lemma 3.3, pp.592–593) -/
theorem compact_local_jet_shift_bound {M : Type u} {Z : Type v} {J : Type w} {H : Type x} [TopologicalSpace M] [TopologicalSpace Z]
    [TopologicalSpace J] [TopologicalSpace H]
    (c : OpenPartialHomeomorph M Z) (base : J → M) (base2 : H → M)
    (e : OpenPartialHomeomorph J (Z × ℂ))
    (e2 : OpenPartialHomeomorph H ((Z × ℂ) × ℂ))
    (hsource : e.source = base ⁻¹' c.source)
    (htarget : e.target = {w | w.1 ∈ c.target ∧ w.2 ≠ 0})
    (hbase : ∀ j, (e j).1 = c (base j))
    (hsource2 : e2.source = base2 ⁻¹' c.source)
    (p : H → J) (hpbase : ∀ v, base (p v) = base2 v)
    (hpcoeff : ∀ v, base2 v ∈ c.source → e (p v) = (e2 v).1)
    (scale : ℂˣ → J → J)
    (hscale : ∀ w j, base j ∈ c.source → base (scale w j) = base j ∧
      e (scale w j) = ((e j).1, (w : ℂ) * (e j).2))
    (scale2 : ℂˣ → H → H)
    (hscale2 : ∀ w v, base2 v ∈ c.source → (e2 (scale2 w v)).2 = (w : ℂ)^2*(e2 v).2)
    (shift : ℂ → H → H)
    (hshift : ∀ mu v, base2 v ∈ c.source →
      (e2 (shift mu v)).2 = (e2 v).2 - mu*(e2 v).1.2)
    (hshiftExists : ∀ v w, p v = p w → ∃ mu, shift mu v = w)
    (s : C(J,H)) (hs : ∀ j, p (s j) = j)
    (hsscale : ∀ w j, s (scale w j) = scale2 w (s j))
    (sLoc : {j : J | base j ∈ c.source} → H)
    (hsLoc : ∀ j, p (sLoc j) = j.val ∧ (e2 (sLoc j)).2 = 0)
    (ν : J → ℝ) (hν : Continuous ν) (hνpos : ∀ j, 0 < ν j)
    (hνscale : ∀ w j, ν (scale w j) = ‖(w : ℂ)‖ * ν j)
    (K : Set M) (hK : IsCompact K) (hKU : K ⊆ c.source) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j (hj : base j ∈ K), ∃ mu,
      shift mu (s j) = sLoc ⟨j,hKU hj⟩ ∧ ‖mu‖ ≤ B*ν j := by
  have flowboxUnitFrame {M : Type u} {Z : Type v} {J : Type w} [TopologicalSpace M] [TopologicalSpace Z] [TopologicalSpace J]
      (c : OpenPartialHomeomorph M Z) (base : J → M)
      (e : OpenPartialHomeomorph J (Z × ℂ))
      (hsource : e.source = base ⁻¹' c.source)
      (htarget : e.target = {w | w.1 ∈ c.target ∧ w.2 ≠ 0})
      (hbase : ∀ j, (e j).1 = c (base j))
      (scale : ℂˣ → J → J)
      (hscale : ∀ w j, base j ∈ c.source → base (scale w j) = base j ∧
        e (scale w j) = ((e j).1, (w : ℂ) * (e j).2)) :
      ∃ frame : M → J, ContinuousOn frame c.source ∧
        (∀ x ∈ c.source, base (frame x) = x ∧ e (frame x) = (c x, 1)) ∧
        ∀ j, base j ∈ c.source → ∃ w : ℂˣ, j = scale w (frame (base j)) := by
    let frame := fun x ↦ e.symm (c x, 1)
    have htargetUnit (x : M) (hx : x ∈ c.source) : (c x, 1) ∈ e.target := by
      rw [htarget]
      exact ⟨c.map_source hx, one_ne_zero⟩
    have hcoeff (x : M) (hx : x ∈ c.source) : e (frame x) = (c x, 1) :=
      e.right_inv (htargetUnit x hx)
    have hb (x : M) (hx : x ∈ c.source) : base (frame x) = x := by
      have hf := e.map_target (htargetUnit x hx)
      rw [hsource] at hf
      apply c.injOn hf hx
      exact (hbase _).symm.trans (congrArg Prod.fst (hcoeff x hx))
    refine ⟨frame, e.continuousOn_symm.comp (c.continuousOn.prodMk continuousOn_const)
      (fun x hx ↦ htargetUnit x hx), (fun x hx ↦ ⟨hb x hx, hcoeff x hx⟩), ?_⟩
    intro j hj
    have he : j ∈ e.source := by rwa [hsource]
    have ha : (e j).2 ≠ 0 := by
      have ht := e.map_source he
      rw [htarget] at ht
      exact ht.2
    let w : ℂˣ := Units.mk0 (e j).2 ha
    refine ⟨w, e.injOn he ?_ ?_⟩
    · rw [hsource, mem_preimage, (hscale w _ (by rw [hb _ hj]; exact hj)).1, hb _ hj]
      exact hj
    · rw [(hscale w _ (by rw [hb _ hj]; exact hj)).2, hcoeff _ hj]
      simp only [w, Units.val_mk0, mul_one]
      exact Prod.ext (hbase j) rfl
  have compactHomogeneousBound {X : Type u} {J : Type w} [TopologicalSpace X] [TopologicalSpace J]
      (base : J → X) (frame : X → J) (scale : ℂˣ → J → J)
      (U K : Set X) (hK : IsCompact K) (hKU : K ⊆ U)
      (hframe : ContinuousOn frame U) (hbframe : ∀ x ∈ U, base (frame x) = x)
      (hreconstruct : ∀ j, base j ∈ U → ∃ w : ℂˣ, j = scale w (frame (base j)))
      (f : J → ℂ) (ν : J → ℝ)
      (hf : ContinuousOn f (base ⁻¹' U)) (hν : Continuous ν)
      (hνpos : ∀ j, 0 < ν j)
      (hfscale : ∀ w j, base j ∈ U → f (scale w j) = (w : ℂ) * f j)
      (hνscale : ∀ w j, ν (scale w j) = ‖(w : ℂ)‖ * ν j) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ j, base j ∈ K → ‖f j‖ ≤ B * ν j := by
    have hfframe : ContinuousOn (f ∘ frame) U :=
      hf.comp hframe (fun x hx ↦ by simpa only [mem_preimage, hbframe x hx] using hx)
    have hnframe : ContinuousOn (ν ∘ frame) U := hν.continuousOn.comp hframe (mapsTo_univ _ _)
    have hc : ContinuousOn (fun x ↦ ‖f (frame x)‖ / ν (frame x)) U :=
      hfframe.norm.div hnframe (fun x _ ↦ (hνpos (frame x)).ne')
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro j hj
    have hu := hKU hj
    have hh0 : |‖f (frame (base j))‖ / ν (frame (base j))| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB (base j) hj
    have hh : ‖f (frame (base j))‖ / ν (frame (base j)) ≤ max B 0 :=
      (le_abs_self _).trans (hh0.trans (le_max_left _ _))
    have hb := (div_le_iff₀ (hνpos (frame (base j)))).mp hh
    obtain ⟨w, he⟩ := hreconstruct j hu
    calc
      ‖f j‖ = ‖(w : ℂ)‖ * ‖f (frame (base j))‖ := by
        calc
          _ = ‖f (scale w (frame (base j)))‖ := congrArg (fun j ↦ ‖f j‖) he
          _ = _ := by rw [hfscale w _ (by rw [hbframe _ hu]; exact hu), norm_mul]
      _ ≤ ‖(w : ℂ)‖ * (max B 0 * ν (frame (base j))) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = max B 0 * ν j := by
        have hn := (congrArg ν he).trans (hνscale w _)
        rw [hn]
        ring
  have localSectionErrorBound {M : Type u} {Z : Type v} {J : Type w} [TopologicalSpace M] [TopologicalSpace Z] [TopologicalSpace J]
      (c : OpenPartialHomeomorph M Z) (base : J → M)
      (e : OpenPartialHomeomorph J (Z × ℂ))
      (hsource : e.source = base ⁻¹' c.source)
      (htarget : e.target = {w | w.1 ∈ c.target ∧ w.2 ≠ 0})
      (hbase : ∀ j, (e j).1 = c (base j))
      (scale : ℂˣ → J → J)
      (hscale : ∀ w j, base j ∈ c.source → base (scale w j) = base j ∧
        e (scale w j) = ((e j).1, (w : ℂ) * (e j).2))
      (b : J → ℂ) (hb : ContinuousOn b (base ⁻¹' c.source))
      (hbscale : ∀ w j, base j ∈ c.source → b (scale w j) = (w : ℂ) ^ 2 * b j)
      (ν : J → ℝ) (hν : Continuous ν) (hνpos : ∀ j, 0 < ν j)
      (hνscale : ∀ w j, ν (scale w j) = ‖(w : ℂ)‖ * ν j)
      (K : Set M) (hK : IsCompact K) (hKU : K ⊆ c.source) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ j, base j ∈ K → ‖b j / (e j).2‖ ≤ B * ν j := by
    have ha (j : J) (hj : base j ∈ c.source) : (e j).2 ≠ 0 := by
      have ht := e.map_source (show j ∈ e.source by rwa [hsource])
      rw [htarget] at ht
      exact ht.2
    obtain ⟨frame, hframe, hbframe, hreconstruct⟩ :=
      flowboxUnitFrame c base e hsource htarget hbase scale hscale
    apply compactHomogeneousBound base frame scale c.source K hK hKU hframe
      (fun x hx ↦ (hbframe x hx).1) hreconstruct (fun j ↦ b j / (e j).2)
      ν _ hν hνpos _ hνscale
    · exact hb.div (by simpa only [hsource] using e.continuousOn.snd) (fun j hj ↦ ha j hj)
    · intro w j hj
      rw [hbscale w j hj, (hscale w j hj).2]
      change (w : ℂ) ^ 2 * b j / ((w : ℂ) * (e j).2) = (w : ℂ) * (b j / (e j).2)
      field_simp
  have hsb (j : J) : base2 (s j) = base j := by rw [← hpbase,hs]
  have hb : ContinuousOn (fun j ↦ (e2 (s j)).2) (base ⁻¹' c.source) :=
    e2.continuousOn.snd.comp s.continuous.continuousOn (by
      intro j hj
      rw [hsource2,mem_preimage,hsb]
      exact hj)
  obtain ⟨B,hB,hbound⟩ := localSectionErrorBound c base e hsource htarget hbase
    scale hscale (fun j ↦ (e2 (s j)).2) hb
    (by intro w j hj; rw [hsscale,hscale2 w _ (by rw [hsb]; exact hj)])
    ν hν hνpos hνscale K hK hKU
  refine ⟨B,hB,?_⟩
  intro j hj
  have hu := hKU hj
  obtain ⟨mu,hmu⟩ := hshiftExists (s j) (sLoc ⟨j,hu⟩) ((hs j).trans (hsLoc ⟨j,hu⟩).1.symm)
  refine ⟨mu,hmu,?_⟩
  have ha : (e j).2 ≠ 0 := by
    have hh := e.map_source (show j ∈ e.source by rwa [hsource])
    rw [htarget] at hh
    exact hh.2
  have hc := congrArg (fun v ↦ (e2 v).2) hmu
  rw [hshift mu _ (by rw [hsb]; exact hu),(hsLoc ⟨j,hu⟩).2] at hc
  have hfirst : (e2 (s j)).1.2 = (e j).2 := by
    rw [← hpcoeff _ (by rw [hsb]; exact hu),hs]
  rw [hfirst] at hc
  have hmuEq : mu = (e2 (s j)).2 / (e j).2 := by
    apply (eq_div_iff ha).mpr
    linear_combination -hc
  rw [hmuEq]
  exact hbound j hj

end HolomorphicAnosov.Ghys

