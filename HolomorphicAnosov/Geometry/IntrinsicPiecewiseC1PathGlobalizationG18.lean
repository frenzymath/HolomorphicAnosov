import HolomorphicAnosov.Geometry.HermitianLeafPathDistance

open Set
open scoped ContDiff Manifold

noncomputable section
namespace HolomorphicAnosov

universe u

/-- A finite intrinsic piecewise-C¹ path has a genuine global continuous representative (Lee, *Introduction to Smooth Manifolds* (2003), §11, pp.275--279).-/
theorem intrinsicPiecewiseC1Path_global_representative
    {r : ℕ} {L : Type u} [TopologicalSpace L]
    [ChartedSpace (Fin r → ℝ) L]
    {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y) :
    ∃ γ : ℝ → L,
      ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧
      (∀ i : Fin (p.n + 1),
        ∀ t ∈ Icc (p.time i.castSucc) (p.time i.succ),
          γ t = p.piece i t) := by
  classical
  let ext : ∀ i : Fin (p.n + 1), ℝ → L := fun i ↦
    Set.IccExtend (p.time_strictMono i.castSucc_lt_succ).le
      ((Icc (p.time i.castSucc) (p.time i.succ)).domRestrict (p.piece i))
  have hext : ∀ i : Fin (p.n + 1), Continuous (ext i) := by
    intro i
    apply (continuousOn_iff_continuous_domRestrict.mp (p.piece_c1 i).continuousOn).comp
      continuous_projIcc
  let g : ∀ k : Fin (p.n + 1), ℝ → L := fun k ↦
    Fin.induction (motive := fun _ ↦ ℝ → L) (ext 0)
      (fun j gj ↦ (Ici (p.time j.succ.castSucc)).piecewise (ext j.succ) gj) k
  have hendpoint : ∀ k : Fin (p.n + 1),
      g k (p.time k.succ) = ext k (p.time k.succ) := by
    intro k
    induction k using Fin.induction with
    | zero =>
        rfl
    | succ j hj =>
        change (Ici (p.time j.succ.castSucc)).piecewise (ext j.succ) (g j.castSucc)
          (p.time j.succ.succ) = ext j.succ (p.time j.succ.succ)
        simp only [Set.piecewise, Set.mem_Ici]
        rw [ite_eq_left (p.time_strictMono j.succ.castSucc_lt_succ).le]
  have hext_eq (i : Fin (p.n + 1)) (t : ℝ)
      (ht : t ∈ Icc (p.time i.castSucc) (p.time i.succ)) :
      ext i t = p.piece i t := by
    simp [ext, Set.IccExtend, Set.projIcc_of_mem _ ht]
  have hjoin (j : Fin p.n) :
      ext j.succ (p.time j.succ.castSucc) =
        g j.castSucc (p.time j.succ.castSucc) := by
    rw [hext_eq j.succ _ ⟨le_rfl, (p.time_strictMono j.succ.castSucc_lt_succ).le⟩]
    have hprev := hendpoint j.castSucc
    rw [hext_eq j.castSucc _
      ⟨(p.time_strictMono j.castSucc.castSucc_lt_succ).le, le_rfl⟩] at hprev
    exact (p.junction j).symm.trans hprev.symm
  have hg : ∀ k : Fin (p.n + 1), ContinuousOn (g k) (Icc 0 1) := by
    intro k
    induction k using Fin.induction with
    | zero => exact (hext 0).continuousOn
    | succ j hj =>
      change ContinuousOn ((Ici (p.time j.succ.castSucc)).piecewise (ext j.succ) (g j.castSucc))
        (Icc 0 1)
      apply ContinuousOn.piecewise (s := Icc 0 1)
      · intro z hz
        have hfront : z = p.time j.succ.castSucc := by
          rw [frontier_Ici] at hz
          simpa [Set.mem_inter_iff] using hz.2
        subst z
        exact hjoin j
      · exact (hext j.succ).continuousOn.mono inter_subset_left
      · exact hj.mono inter_subset_left
  have hpiece : ∀ (k : Fin (p.n + 1)) (i : Fin (p.n + 1)), i ≤ k →
      ∀ t ∈ Icc (p.time i.castSucc) (p.time i.succ), g k t = p.piece i t := by
    intro k
    induction k using Fin.induction with
    | zero =>
      intro i hi t ht
      have hi0 : i = 0 := le_antisymm hi (Fin.zero_le i)
      subst i
      exact hext_eq 0 t ht
    | succ j hj =>
      intro i hi t ht
      change (Ici (p.time j.succ.castSucc)).piecewise (ext j.succ) (g j.castSucc) t = _
      by_cases hij : i = j.succ
      · subst i
        simp only [Set.piecewise, Set.mem_Ici, ite_eq_left ht.1]
        exact hext_eq j.succ t ht
      · have hijle : i ≤ j.castSucc := by
          have hlt : i < j.succ := lt_of_le_of_ne hi hij
          simpa only [Fin.lt_def, Fin.le_def, Fin.val_succ, Fin.val_castSucc,
            Nat.lt_succ_iff] using hlt
        have htime : p.time i.succ ≤ p.time j.succ.castSucc :=
          p.time_strictMono.monotone (by
            apply Fin.le_def.mpr
            change i.val + 1 ≤ j.val + 1
            exact Nat.succ_le_succ (Fin.le_def.mp hijle))
        by_cases hcut : p.time j.succ.castSucc ≤ t
        · have hteq : t = p.time j.succ.castSucc :=
            le_antisymm (ht.2.trans htime) hcut
          subst t
          simp only [Set.piecewise, Set.mem_Ici, ite_eq_left (le_rfl :
            p.time j.succ.castSucc ≤ p.time j.succ.castSucc)]
          exact (hjoin j).trans (hj i hijle _ ht)
        · simp only [Set.piecewise, Set.mem_Ici, ite_eq_right hcut]
          exact hj i hijle t ht
  have hfinal (i : Fin (p.n + 1)) (t : ℝ)
      (ht : t ∈ Icc (p.time i.castSucc) (p.time i.succ)) :
      g (Fin.last p.n) t = p.piece i t := hpiece _ i (Fin.le_last _) t ht
  refine ⟨g (Fin.last p.n), hg _, ?_, ?_, hfinal⟩
  · have ht : (0 : ℝ) ∈ Icc (p.time (0 : Fin (p.n + 1)).castSucc)
        (p.time (0 : Fin (p.n + 1)).succ) := by
      rw [show (0 : Fin (p.n + 1)).castSucc = 0 from rfl, p.time_zero]
      exact ⟨le_rfl, by
        have h := (p.time_strictMono (0 : Fin (p.n + 1)).castSucc_lt_succ).le
        simpa [p.time_zero] using h⟩
    exact (hfinal 0 0 ht).trans p.source
  · have ht : (1 : ℝ) ∈ Icc (p.time (Fin.last p.n).castSucc)
        (p.time (Fin.last p.n).succ) := by
      rw [show (Fin.last p.n).succ = Fin.last (p.n + 1) from rfl, p.time_one]
      exact ⟨by
        simpa only [show (Fin.last p.n).succ = Fin.last (p.n + 1) from rfl,
          p.time_one] using (p.time_strictMono (Fin.last p.n).castSucc_lt_succ).le,
        le_rfl⟩
    exact (hfinal (Fin.last p.n) 1 ht).trans p.target

end HolomorphicAnosov

