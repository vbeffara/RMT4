import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open Finset BigOperators Metric Set

lemma exists_div_lt {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) : ∃ n : ℕ, a / (n + 1) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε ha)
  use n
  convert (@strictMono_mul_left_of_pos ℝ _ a ha).lt_iff_lt.2 hn using 1 <;> field_simp; ring

structure subdivision (a b : ℝ) where
  n : ℕ
  toFun : ℕ → ℝ
  first : toFun 0 = a
  last : toFun (n + 1) = b
  subset : ∀ {i}, i ≤ n + 1 → toFun i ∈ Set.Icc a b

namespace subdivision

variable {a b : ℝ} {σ : subdivision a b}

instance : CoeFun (subdivision a b) (λ _ => ℕ → ℝ) := ⟨toFun⟩

def Icc (σ : subdivision a b) (i : Fin (σ.n + 1)) : Set ℝ := Set.Icc (σ i) (σ i.succ)

noncomputable def mesh (σ : subdivision a b) : ℝ := ⨆ i : Fin (σ.n + 1), |σ i.succ - σ i|

lemma le_mesh {i : Fin (σ.n + 1)} : |σ (i + 1) - σ i| ≤ σ.mesh :=
  le_ciSup (f := λ i : Fin (σ.n + 1) => |σ i.succ - σ i|) (finite_range _).bddAbove _

lemma le (σ : subdivision a b) : a ≤ b :=
  (σ.first ▸ σ.subset (zero_le (σ.n + 1))).2

noncomputable def regular (hab : a ≤ b) (n : ℕ) : subdivision a b where
  n := n
  toFun := λ i => a + i * (b - a) / (n + 1)
  first := by simp
  last := by field_simp; ring
  subset := by
    have h0 : 0 ≤ b - a := by linarith
    intro i hi
    have h3 : (i : ℝ) ≤ n + 1 := by norm_cast
    have h4 : b = a + (n + 1) * (b - a) / (n + 1) := by field_simp; ring
    constructor
    · simp; positivity
    · nth_rewrite 2 [h4]; simp; gcongr

@[simp] lemma regular_mesh (hab : a < b) {n : ℕ} :
    (regular hab.le n).mesh = (b - a) / (n + 1) := by
  have : |(b - a) / (↑n + 1)| = (b - a) / (↑n + 1) := by
    rw [abs_eq_self]
    have e1 : 0 ≤ b - a := by linarith
    positivity
  have : ∀ i : Fin (n + 1), |(i + 1) * (b - a) / (n + 1) - i * (b - a) / (n + 1)| =
      (b - a) / (n + 1) := by
    intro i; rw [← this]; congr; field_simp; ring
  simp [mesh, regular, this]

variable {S : ι → Set ℝ}

def adapted (σ : subdivision a b) (S : ι → Set ℝ) : Prop := ∀ k, ∃ i, σ.Icc k ⊆ S i

lemma adapted_of_mesh_lt (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : subdivision a b, σ.mesh < ε → adapted σ S := by
  obtain ⟨ε, hε, l1⟩ := lebesgue_number_lemma_of_metric isCompact_Icc h1 h2
  refine ⟨ε, hε, λ σ hσ j => ?_⟩
  obtain ⟨i, hi⟩ := l1 (σ j.castSucc) (σ.subset j.prop.le)
  have : Set.OrdConnected (ball (σ j.castSucc) ε) := (convex_ball ..).ordConnected
  use i
  refine subset_trans ?_ hi
  refine Set.Icc_subset _ (mem_ball_self hε) ?_
  exact le_mesh.trans_lt hσ

lemma exists_adapted (hab : a < b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ σ : subdivision a b, adapted σ S := by
  obtain ⟨ε, hε, h⟩ := adapted_of_mesh_lt h1 h2
  obtain ⟨n, hn⟩ := exists_div_lt (sub_pos_of_lt hab) hε
  have : (regular hab.le n).mesh = (b - a) / (n + 1) := regular_mesh hab
  exact ⟨regular hab.le n, h _ (by linarith)⟩

def sum (σ : subdivision a b) (f : ℕ → ℝ → ℝ → ℂ) : ℂ :=
  ∑ i in range (σ.n + 1), f i (σ i) (σ (i + 1))

end subdivision

noncomputable def sumSub (σ : subdivision a b) (F : Fin (σ.n + 1) -> ℝ -> ℂ) : ℂ :=
  σ.sum (λ i x y => F i y - F i x)

noncomputable def sumSubAlong (σ : subdivision a b) (F : Fin (σ.n + 1) → ℂ → ℂ)
    (γ : ℝ → ℂ) : ℂ :=
  sumSub σ (λ i => F i ∘ γ)

def IsLocDerivOn (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ U, ∃ ε > 0, ∃ F : ℂ → ℂ, EqOn (deriv F) f (ball z ε)

noncomputable def pintegral (hab : a < b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc a b) ⊆ U)
    (hγ : Continuous γ) (hf : IsLocDerivOn U f) : ℂ := by
  choose! ε hε F _ using hf
  set S : Set.Icc a b → Set ℝ := λ t => γ ⁻¹' (ball (γ t) (ε (γ t)))
  have l1 : ∀ i, ↑i ∈ S i := λ ⟨t, ht⟩ => by
    exact mem_preimage.2 (mem_ball_self (hε _ (h2 (mem_image_of_mem _ ht))))
  have l2 : Set.Icc a b ⊆ ⋃ i, S i := λ t ht =>
    Set.mem_iUnion.2 ⟨⟨t, ht⟩, l1 ⟨t, ht⟩⟩
  choose σ hσ using subdivision.exists_adapted hab (λ i => isOpen_ball.preimage hγ) l2
  choose I _ using hσ
  exact sumSubAlong σ (λ i => F (γ (I i))) γ

def isPiecewiseDiffAlong (γ : ℝ → ℂ) (σ : subdivision a b) : Prop :=
  ∀ i < σ.n + 1, ContDiffOn ℝ 1 γ (σ.Icc i)

noncomputable def piecewiseIntegral (F : ℂ → ℂ) (γ : ℝ → ℂ) (σ : subdivision a b) : ℂ :=
  ∑ i : Fin (σ.n + 1), (∫ t in (σ i.castSucc)..(σ i.succ), F (γ t) * deriv γ t)

lemma isLocDerivOn_deriv : IsLocDerivOn U (deriv F) := by
  intro z _; exact ⟨1, zero_lt_one, F, eqOn_refl _ _⟩

lemma telescopic {σ : subdivision a b} : sumSub σ (λ _ => f) = f b - f a := by
  simp only [sumSub, ← σ.first, ← σ.last]
  apply Finset.sum_range_sub (f := f ∘ σ)