import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RMT4.Subdivision

open Finset BigOperators Metric Set Subdivision Topology

def IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ U, ∃ ε > 0, ∃ F : ℂ → ℂ, EqOn (deriv F) f (ball z ε)

section pintegral

noncomputable def pintegral (hab : a ≤ b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc a b) ⊆ U)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hf : IsLocDerivOn U f) : ℂ := by
  choose! ε hε F _ using hf
  let S (t : Set.Icc a b) := γ ⁻¹' ball (γ t) (ε (γ t))
  have h (t : Set.Icc a b) : ∃ i, S i ∈ 𝓝[Set.Icc a b] t.1 :=
    ⟨t, hγ t t.2 (ball_mem_nhds (γ t) (hε (γ t) (h2 (mem_image_of_mem _ t.2))))⟩
  choose σ hσ using @exists_adapted' _ _ _ S hab h
  choose I _ using hσ
  exact σ.sumSubAlong (λ i => F (γ (I i))) γ

def isPiecewiseDiffAlong (γ : ℝ → ℂ) (σ : Subdivision a b) : Prop :=
  ∀ i < σ.n + 1, ContDiffOn ℝ 1 γ (σ.Icc i)

noncomputable def piecewiseIntegral (F : ℂ → ℂ) (γ : ℝ → ℂ) (σ : Subdivision a b) : ℂ :=
  ∑ i : Fin (σ.n + 1), (∫ t in (σ i.castSucc)..(σ i.succ), F (γ t) * deriv γ t)

lemma isLocDerivOn_deriv : IsLocDerivOn U (deriv F) := by
  intro z _; exact ⟨1, zero_lt_one, F, eqOn_refl _ _⟩

end pintegral