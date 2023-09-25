import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.MeanValue
import RMT4.Subdivision

open BigOperators Metric Set Subdivision Topology Filter Nat

structure IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) :=
  F : U → ℂ → ℂ
  S : U → Set ℂ
  mem (z : U) : z.1 ∈ S z
  opn (z : U) : IsOpen (S z)
  sub (z : U) : S z ⊆ U
  dif (z : U) : DifferentiableOn ℂ (F z) (S z)
  eqd (z : U) : (S z).EqOn f (deriv (F z))

lemma IsLocDerivOn.nhd (h : IsLocDerivOn U f) (z : U) : h.S z ∈ 𝓝 z.1 :=
  (h.opn z).mem_nhds (h.mem z)

noncomputable def isLocDerivOn_deriv (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    IsLocDerivOn U (deriv F) where
  F _ := F
  S _ := U
  sub _ := by rfl
  mem z := z.2
  opn _ := hU
  eqd _ := eqOn_refl (deriv F) U
  dif _ := hF

section pintegral

noncomputable def pintegral (hab : a ≤ b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : MapsTo γ (Set.Icc a b) U)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hf : IsLocDerivOn U f) : ℂ :=
  have h1 (t : Set.Icc a b) : ∃ i, hf.S i ∈ 𝓝 (γ t) :=
    let u : U := ⟨γ t, h2 t.2⟩
    ⟨u, hf.nhd u⟩
  let RW := exists_reladapted hab hγ h1
  RW.σ.sumSubAlong (hf.F ∘ RW.I) γ

end pintegral

lemma isLocallyConstant_of_deriv_eq_zero (hU : IsOpen U) (f : ℂ → ℂ) (h : DifferentiableOn ℂ f U)
    (hf : U.EqOn (deriv f) 0) :
    IsLocallyConstant (U.restrict f) := by
  refine (IsLocallyConstant.iff_exists_open _).2 (λ ⟨z, hz⟩ => ?_)
  obtain ⟨ε, L1, L2⟩ := isOpen_iff.1 hU z hz
  refine ⟨ball ⟨z, hz⟩ ε, isOpen_ball, mem_ball_self L1, λ ⟨z', _⟩ hz' => ?_⟩
  refine (convex_ball z ε).is_const_of_fderivWithin_eq_zero (h.mono L2) ?_ hz' (mem_ball_self L1)
  intro x hx
  rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hx)]
  · exact ContinuousLinearMap.ext_ring (hf (L2 hx))
  · exact h.differentiableAt (hU.mem_nhds (L2 hx))

lemma apply_eq_of_path (hab : a ≤ b) (f : ℂ → ℂ) (hf : IsLocallyConstant (U.restrict f))
    (γ : ℝ → ℂ) (hγ : ContinuousOn γ (Set.Icc a b)) (h : MapsTo γ (Set.Icc a b) U) :
    f (γ b) = f (γ a) := by
  haveI : PreconnectedSpace (Set.Icc a b) := isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  have h2 := hf.comp_continuous (hγ.restrict_mapsTo h)
  exact @IsLocallyConstant.apply_eq_of_isPreconnected _ _ _ _ (h2) _ isPreconnected_univ
    ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩ (mem_univ _) (mem_univ _)

lemma sumSubAlong_eq_zero {DW : IsLocDerivOn U 0}
  {RW : reladapted a b DW.S γ} (hγ : ContinuousOn γ (Set.Icc a b)) :
    RW.σ.sumSubAlong (DW.F ∘ RW.I) γ = 0 := by
  simp only [sumSubAlong, sumSub, sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  rw [sub_eq_zero]
  apply apply_eq_of_path (U := DW.S (RW.I k))
  · refine RW.σ.mono hk.le ?_ (Nat.le_succ k)
    simpa only [mem_Iic, add_le_add_iff_right] using Nat.lt_succ.1 hk
  · apply isLocallyConstant_of_deriv_eq_zero (DW.opn _) _ (DW.dif _)
    exact λ _ hz => (DW.eqd (RW.I k) hz).symm
  · apply hγ.mono
    convert RW.σ.Icc_subset (i := k)
    simp only [Subdivision.Icc, Fin.coe_ofNat_eq_mod, Fin.val_succ, Nat.mod_eq_of_lt hk]
  · apply (mapsTo'.2 (RW.sub k)).mono_left
    simpa [Subdivision.Icc, Nat.mod_eq_of_lt hk] using subset_rfl

lemma pintegral_zero : pintegral hab 0 γ h2 hγ hf = 0 := by
  simp only [pintegral, sumSubAlong_eq_zero hγ]

example {hf : IsLocDerivOn U f} {RW₁ RW₂ : reladapted a b hf.S γ} (h : RW₁.σ = RW₂.σ)
    (hγ : ContinuousOn γ (Set.Icc a b)) :
    RW₁.σ.sumSubAlong (hf.F ∘ RW₁.I) γ = RW₂.σ.sumSubAlong (hf.F ∘ RW₂.I) γ := by

  rcases hf with ⟨F, S, Smem, Sopn, Ssub, Sdif, Seqd⟩
  rcases RW₁ with ⟨σ, I₁, hI₁⟩
  rcases RW₂ with ⟨σ', I₂, hI₂⟩
  simp only at hI₁ hI₂ h ⊢
  subst h

  simp only [sumSubAlong, sumSub, sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk

  set ff := F (I₁ k)
  set gg := F (I₂ k)
  set Iuv := σ.Icc k with hIuv

  rw [sub_eq_sub_iff_sub_eq_sub]

  have huv : σ k ≤ σ (k + 1) := by
    refine σ.mono ?_ ?_ k.le_succ
    · exact hk.le
    · apply Nat.succ_le_succ
      exact Nat.lt_succ.1 hk

  set Uf : Set ℂ := S (I₁ ⟨k, hk⟩)
  set Ug : Set ℂ := S (I₂ ⟨k, hk⟩)

  have Uf' : DifferentiableOn ℂ ff Uf := by
    convert Sdif _ ; simp [hk, Nat.mod_eq_of_lt]
  have Uf'' := Uf'.mono (inter_subset_left Uf Ug)

  have Ug' : DifferentiableOn ℂ gg Ug := by
    convert Sdif _ ; simp [hk, Nat.mod_eq_of_lt]
  have Ug'' := Ug'.mono (inter_subset_right Uf Ug)

  set Ufg : Set ℂ := Uf ∩ Ug

  have hfg : IsLocallyConstant (restrict Ufg (ff - gg)) := by
    apply isLocallyConstant_of_deriv_eq_zero
    · exact (Sopn _).inter (Sopn _)
    · exact Uf''.sub Ug''
    · intro z hz
      have e1 : DifferentiableAt ℂ ff z := by
        apply Uf'.differentiableAt
        apply (Sopn _).mem_nhds
        exact hz.1
      have e2 : DifferentiableAt ℂ gg z := by
        apply Ug'.differentiableAt
        apply (Sopn _).mem_nhds
        exact hz.2
      have e3 : deriv (ff - gg) z = deriv ff z - deriv gg z := deriv_sub e1 e2
      rw [e3]
      have e4 : f z = deriv (F (I₁ k)) z := by
        convert Seqd (I₁ ⟨k, hk⟩) ((inter_subset_left Uf Ug) hz)
        simpa using hk
      have e5 : f z = deriv (F (I₂ k)) z := by
        convert Seqd (I₂ ⟨k, hk⟩) ((inter_subset_right Uf Ug) hz)
        simpa using hk
      simp [← e4, ← e5]

  have hIss : Iuv ⊆ Set.Icc a b := σ.Icc_subset

  have hγ1 : ContinuousOn γ Iuv := hγ.mono hIss

  have hγ2 : MapsTo γ Iuv Ufg := by
    have e1 := hI₁ ⟨k, hk⟩
    have e2 := hI₂ ⟨k, hk⟩
    have : σ.Icc  ⟨k, hk⟩ = σ.Icc  ⟨k, hk⟩ := by
      refine congr_arg₂ ?_ ?_ ?_ <;> simp
    rw [this] at e1
    rw [mapsTo']
    convert subset_inter e1 e2
    simp [hk]

  refine apply_eq_of_path huv (ff - gg) hfg γ ?_ ?_
  · convert hγ1 ; simp [hIuv, Subdivision.Icc, Nat.mod_eq_of_lt, hk]
  · convert hγ2 ; simp [hIuv, Subdivision.Icc, Nat.mod_eq_of_lt, hk]

