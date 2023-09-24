import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.MeanValue
import RMT4.Subdivision

open BigOperators Metric Set Subdivision Topology Filter

structure IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) :=
  F : ℂ → ℂ → ℂ
  S : ℂ → Set ℂ
  mem {z : ℂ} (hz : z ∈ U) : z ∈ S z
  opn {z : ℂ} (hz : z ∈ U) : IsOpen (S z)
  sub {z : ℂ} (hz : z ∈ U) : S z ⊆ U
  dif {z : ℂ} (hz : z ∈ U) : DifferentiableOn ℂ (F z) (S z)
  eqd {z : ℂ} (hz : z ∈ U) : (S z).EqOn f (deriv (F z))

lemma IsLocDerivOn.nhd (h : IsLocDerivOn U f) (hz : z ∈ U) : h.S z ∈ 𝓝 z :=
  (h.opn hz).mem_nhds (h.mem hz)

noncomputable def isLocDerivOn_deriv (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    IsLocDerivOn U (deriv F) where
  F _ := F
  S _ := U
  sub _ := by rfl
  mem hz := hz
  opn _ := hU
  eqd _ := eqOn_refl (deriv F) U
  dif _ := hF

section pintegral

noncomputable def pintegral (hab : a ≤ b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : MapsTo γ (Set.Icc a b) U)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hf : IsLocDerivOn U f) : ℂ :=
  have h1 (t : Set.Icc a b) : ∃ i, hf.S i ∈ 𝓝 (γ t) := ⟨γ t, hf.nhd (h2 t.2)⟩
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

example {σ : Subdivision a b} {DW : IsLocDerivOn U f} {RW RW' : reladapted_witness σ DW.S γ} :
    σ.sumSubAlong (DW.F ∘ RW.I) γ = σ.sumSubAlong (DW.F ∘ RW'.I) γ := by
  simp only [sumSubAlong, sumSub, sum]
  apply Finset.sum_congr rfl
  intro k hk
  set φ := (DW.F ∘ RW.I) k
  set ψ := (DW.F ∘ RW'.I) k
  set F := φ - ψ
  set x := γ (σ k)
  set y := γ (σ (k + 1))
  rw [sub_eq_sub_iff_sub_eq_sub]
  change F y = F x
  have h1 := RW.hI k
  have h2 := RW'.hI k
  have h3 := subset_inter h1 h2
  sorry