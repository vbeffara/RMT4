import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.MeanValue
import RMT4.Subdivision

open BigOperators Metric Set Subdivision Topology Filter

def IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) := ∀ z ∈ U, ∃ F : ℂ → ℂ, f =ᶠ[𝓝 z] deriv F

lemma isLocDerivOn_deriv : IsLocDerivOn U (deriv F) := λ _ _ => ⟨F, by rfl⟩

section pintegral

noncomputable def pintegral (hab : a ≤ b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc a b) ⊆ U)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hf : IsLocDerivOn U f) : ℂ := by
  simp only [IsLocDerivOn, Filter.eventuallyEq_iff_exists_mem] at hf
  choose F s hs using hf
  let S (t : Set.Icc a b) := γ ⁻¹' s (γ t) (h2 (mem_image_of_mem _ t.2))
  have h (t : Set.Icc a b) : ∃ i, S i ∈ 𝓝[Set.Icc a b] t.1 := ⟨t, hγ t t.2 (hs _ _).1⟩
  choose σ hσ using exists_adapted' hab h
  choose I _ using hσ
  exact σ.sumSubAlong (λ i => F _ (h2 (mem_image_of_mem _ (I i).2))) γ

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