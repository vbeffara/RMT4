import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RMT4.Subdivision

open Finset BigOperators Metric Set Subdivision

def IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ U, ∃ ε > 0, ∃ F : ℂ → ℂ, EqOn (deriv F) f (ball z ε)

section pintegral

noncomputable def pintegral (hab : a ≤ b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc a b) ⊆ U)
    (hγ : Continuous γ) (hf : IsLocDerivOn U f) : ℂ := by
  choose! ε hε F _ using hf
  set S : Set.Icc a b → Set ℝ := λ t => γ ⁻¹' (ball (γ t) (ε (γ t)))
  have l1 : ∀ i, ↑i ∈ S i := λ ⟨t, ht⟩ => by
    exact mem_preimage.2 (mem_ball_self (hε _ (h2 (mem_image_of_mem _ ht))))
  have l2 : Set.Icc a b ⊆ ⋃ i, S i := λ t ht =>
    Set.mem_iUnion.2 ⟨⟨t, ht⟩, l1 ⟨t, ht⟩⟩
  choose σ hσ using exists_adapted hab (λ i => isOpen_ball.preimage hγ) l2
  choose I _ using hσ
  exact σ.sumSubAlong (λ i => F (γ (I i))) γ

def isPiecewiseDiffAlong (γ : ℝ → ℂ) (σ : Subdivision a b) : Prop :=
  ∀ i < σ.n + 1, ContDiffOn ℝ 1 γ (σ.Icc i)

noncomputable def piecewiseIntegral (F : ℂ → ℂ) (γ : ℝ → ℂ) (σ : Subdivision a b) : ℂ :=
  ∑ i : Fin (σ.n + 1), (∫ t in (σ i.castSucc)..(σ i.succ), F (γ t) * deriv γ t)

lemma isLocDerivOn_deriv : IsLocDerivOn U (deriv F) := by
  intro z _; exact ⟨1, zero_lt_one, F, eqOn_refl _ _⟩

end pintegral