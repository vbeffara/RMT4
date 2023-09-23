import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import RMT4.Subdivision

open BigOperators Metric Set Subdivision Topology Filter

def IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ U, ∃ F : ℂ → ℂ, ∃ s ∈ 𝓝 z, s.EqOn f (deriv F)

section pintegral

noncomputable def pintegral (hab : a ≤ b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc a b) ⊆ U)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hf : IsLocDerivOn U f) : ℂ := by
  choose F s hs using hf
  let S (t : Set.Icc a b) := γ ⁻¹' s (γ t) (h2 (mem_image_of_mem _ t.2))
  have h (t : Set.Icc a b) : ∃ i, S i ∈ 𝓝[Set.Icc a b] t.1 := ⟨t, hγ t t.2 (hs _ _).1⟩
  choose σ hσ using @exists_adapted' _ _ _ S hab h
  choose I _ using hσ
  exact σ.sumSubAlong (λ i => F _ (h2 (mem_image_of_mem _ (I i).2))) γ

def isPiecewiseDiffAlong (γ : ℝ → ℂ) (σ : Subdivision a b) : Prop :=
  ∀ i < σ.n + 1, ContDiffOn ℝ 1 γ (σ.Icc i)

noncomputable def piecewiseIntegral (F : ℂ → ℂ) (γ : ℝ → ℂ) (σ : Subdivision a b) : ℂ :=
  ∑ i : Fin (σ.n + 1), (∫ t in (σ i.castSucc)..(σ i.succ), F (γ t) * deriv γ t)

lemma isLocDerivOn_deriv : IsLocDerivOn U (deriv F) :=
  λ _ _ => ⟨F, univ, univ_mem, eqOn_refl _ _⟩

end pintegral