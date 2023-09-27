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

lemma isLocallyConstant_of_deriv_eq_zero (hU : IsOpen U) {f : ℂ → ℂ} (h : DifferentiableOn ℂ f U)
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

lemma apply_eq_of_path (hab : a ≤ b) {f : ℂ → ℂ} (hf : IsLocallyConstant (U.restrict f))
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Set.Icc a b)) (h : MapsTo γ (Set.Icc a b) U) :
    f (γ b) = f (γ a) := by
  haveI : PreconnectedSpace (Set.Icc a b) := isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  have h2 := hf.comp_continuous (hγ.restrict_mapsTo h)
  exact @IsLocallyConstant.apply_eq_of_isPreconnected _ _ _ _ (h2) _ isPreconnected_univ
    ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩ (mem_univ _) (mem_univ _)

lemma sumSubAlong_eq_zero {DW : IsLocDerivOn U 0}
  {RW : reladapted a b DW.S γ} (hγ : ContinuousOn γ (Set.Icc a b)) :
    RW.σ.sumSubAlong (DW.F ∘ RW.I) γ = 0 := by
  refine Subdivision.sum_eq_zero (λ k => (sub_eq_zero.2 ?_))
  apply apply_eq_of_path RW.σ.mono'
  · apply isLocallyConstant_of_deriv_eq_zero (DW.opn _) (DW.dif _)
    exact λ _ hz => (DW.eqd (RW.I k) hz).symm
  · exact hγ.mono RW.σ.Icc_subset
  · exact mapsTo'.2 (RW.sub k)

lemma pintegral_zero : pintegral hab 0 γ h2 hγ hf = 0 := by simp [pintegral, sumSubAlong_eq_zero hγ]

lemma sub_eq_sub_of_deriv_eq_deriv (hab : a ≤ b) (hU : IsOpen U)
    {γ : ℝ → ℂ} (hγ₁ : ContinuousOn γ (Set.Icc a b)) (hγ₂ : MapsTo γ (Set.Icc a b) U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfg : ∀ z ∈ U, deriv f z = deriv g z) :
    f (γ b) - f (γ a) = g (γ b) - g (γ a) := by
  rw [sub_eq_sub_iff_sub_eq_sub]
  change (f - g) (γ b) = (f - g) (γ a)
  refine apply_eq_of_path (U := U) hab ?_ hγ₁ hγ₂
  refine isLocallyConstant_of_deriv_eq_zero hU (hf.sub hg) (λ z hz => ?_)
  have h1 : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hz)
  have h2 : DifferentiableAt ℂ g z := hg.differentiableAt (hU.mem_nhds hz)
  have h3 : deriv (f - g) z = deriv f z - deriv g z := deriv_sub h1 h2
  simp [hfg z hz, h3]

lemma sumSubAlong_eq_of_sigma {hf : IsLocDerivOn U f} {RW₁ RW₂ : reladapted a b hf.S γ}
    (h : RW₁.σ = RW₂.σ) (hγ : ContinuousOn γ (Set.Icc a b)) :
    RW₁.σ.sumSubAlong (hf.F ∘ RW₁.I) γ = RW₂.σ.sumSubAlong (hf.F ∘ RW₂.I) γ := by
  rcases hf with ⟨F, S, _, Sopn, _, Sdif, Seqd⟩
  rcases RW₁ with ⟨σ, I₁, hI₁⟩
  rcases RW₂ with ⟨σ', I₂, hI₂⟩
  subst h
  refine Subdivision.sum_congr (λ k => ?_)
  apply sub_eq_sub_of_deriv_eq_deriv σ.mono' ((Sopn _).inter (Sopn _)) (hγ.mono σ.Icc_subset)
  · simpa only [mapsTo'] using subset_inter (hI₁ k) (hI₂ k)
  · exact (Sdif _).mono (inter_subset_left _ _)
  · exact (Sdif _).mono (inter_subset_right _ _)
  · exact λ z hz => (Seqd _ hz.1).symm.trans (Seqd _ hz.2)
