import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.MeanValue
import RMT4.Subdivision

open BigOperators Metric Set Subdivision Topology Filter

def IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) :=
  ∀ z ∈ U, ∃ F : ℂ → ℂ, ∃ S ∈ 𝓝 z, S.EqOn f (deriv F)

structure locderivon_witness (U : Set ℂ) (f : ℂ → ℂ) :=
  F : ℂ → ℂ → ℂ
  S : ℂ → Set ℂ
  h1 : ∀ z ∈ U, S z ∈ 𝓝 z
  h2 : ∀ z ∈ U, EqOn f (deriv (F z)) (S z)

noncomputable def IsLocDerivOn.witness (h : IsLocDerivOn U f) : locderivon_witness U f := by
  choose! F S H using h
  exact ⟨F, S, λ z hz => (H z hz).1, λ z hz => (H z hz).2⟩

lemma isLocDerivOn_deriv : IsLocDerivOn U (deriv F) := λ _ _ => ⟨F, _, univ_mem, eqOn_refl ..⟩

section pintegral

noncomputable def pintegral (hab : a ≤ b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc a b) ⊆ U)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hf : IsLocDerivOn U f) : ℂ := by
  let DW := hf.witness
  obtain ⟨σ, hσ⟩ := exists_reladapted hab hγ (λ t => ⟨γ t, DW.h1 _ (h2 (mem_image_of_mem _ t.2))⟩)
  obtain RW := hσ.witness
  exact σ.sumSubAlong (DW.F ∘ RW.I) γ

def isPiecewiseDiffAlong (γ : ℝ → ℂ) (σ : Subdivision a b) : Prop :=
  ∀ i, ContDiffOn ℝ 1 γ (σ.Icc i)

noncomputable def piecewiseIntegral (F : ℂ → ℂ) (γ : ℝ → ℂ) (σ : Subdivision a b) : ℂ :=
  σ.sum (λ _ x y => ∫ t in x..y, F (γ t) * deriv γ t)

end pintegral

noncomputable def Path.integral {x y : ℂ} (γ : Path x y) (f : ℂ → ℂ) (hf : IsLocDerivOn U f)
    (hγ : range γ ⊆ U) : ℂ :=
  pintegral zero_le_one f γ.extend ((image_subset_range _ _).trans (γ.extend_range ▸ hγ))
    γ.continuous_extend.continuousOn hf

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

example : pintegral (U := univ) (hab : a ≤ b) (λ _ => 0) γ h1 h2 h3 = 0 := by
  sorry