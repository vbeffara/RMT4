import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.MeanValue
import RMT4.Subdivision

open BigOperators Metric Set Subdivision Topology Filter

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
  let ⟨σ, hσ⟩ := exists_reladapted hab hγ h1
  let RW := hσ.witness
  σ.sumSubAlong (hf.F ∘ RW.I) γ

end pintegral

lemma isLocallyConstant_of_deriv_eq_zero (hU : IsOpen U) (f : ℂ → ℂ) (h : DifferentiableOn ℂ f U)
    (hf : ∀ z ∈ U, deriv f z = 0) :
    IsLocallyConstant (U.restrict f) := by
  refine (IsLocallyConstant.iff_exists_open _).2 (λ ⟨z, hz⟩ => ?_)
  obtain ⟨ε, L1, L2⟩ := isOpen_iff.1 hU z hz
  refine ⟨ball ⟨z, hz⟩ ε, isOpen_ball, mem_ball_self L1, λ ⟨z', _⟩ hz' => ?_⟩
  refine (convex_ball z ε).is_const_of_fderivWithin_eq_zero (h.mono L2) ?_ hz' (mem_ball_self L1)
  intro x hx
  rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hx)]
  · exact ContinuousLinearMap.ext_ring (hf x (L2 hx))
  · exact h.differentiableAt (hU.mem_nhds (L2 hx))

lemma apply_eq_of_path (hab : a ≤ b) (f : ℂ → ℂ) (hf : IsLocallyConstant (U.restrict f))
    (γ : ℝ → ℂ) (hγ : ContinuousOn γ (Set.Icc a b)) (h : MapsTo γ (Set.Icc a b) U) :
    f (γ b) = f (γ a) := by
  haveI : PreconnectedSpace (Set.Icc a b) := isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  have h2 := hf.comp_continuous (hγ.restrict_mapsTo h)
  exact @IsLocallyConstant.apply_eq_of_isPreconnected _ _ _ _ (h2) _ isPreconnected_univ
    ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩ (mem_univ _) (mem_univ _)

lemma sumSubAlong_eq_zero {σ : Subdivision a b} {DW : IsLocDerivOn U 0}
  {RW : reladapted_witness σ DW.S γ} (hγ : ContinuousOn γ (Set.Icc a b)) :
    σ.sumSubAlong (DW.F ∘ RW.I) γ = 0 := by
  simp only [sumSubAlong, sumSub, sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  rw [sub_eq_zero]
  apply apply_eq_of_path (U := DW.S (RW.I k))
  · refine σ.mono hk.le ?_ (Nat.le_succ k)
    simpa only [mem_Iic, add_le_add_iff_right] using Nat.lt_succ.1 hk
  · apply isLocallyConstant_of_deriv_eq_zero (DW.opn _) _ (DW.dif _)
    exact λ _ hz => (DW.eqd (RW.I k) hz).symm
  · apply hγ.mono
    convert σ.Icc_subset (i := k)
    simp only [Subdivision.Icc, Fin.coe_ofNat_eq_mod, Fin.val_succ, Nat.mod_eq_of_lt hk]
  · apply (mapsTo'.2 (RW.hI k)).mono_left
    simpa [Subdivision.Icc, Nat.mod_eq_of_lt hk] using subset_rfl

lemma pintegral_zero : pintegral hab 0 γ h2 hγ hf = 0 := by
  simp only [pintegral, sumSubAlong_eq_zero hγ]