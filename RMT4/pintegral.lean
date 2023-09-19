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
  mono : MonotoneOn toFun (Set.Iic (n + 1))

namespace subdivision

instance : CoeFun (subdivision a b) (λ _ => ℕ → ℝ) := ⟨toFun⟩

lemma subset (σ : subdivision a b) (hi : i ≤ σ.n + 1) : σ i ∈ Set.Icc a b := by
  constructor
  · simpa only [← σ.first] using σ.mono (zero_le (σ.n + 1)) hi (zero_le _)
  · simpa only [← σ.last] using σ.mono hi (le_refl (σ.n + 1)) hi

variable {a b c : ℝ} {n : ℕ} {σ : subdivision a b}

lemma le (σ : subdivision a b) : a ≤ b := σ.first ▸ (σ.subset (zero_le _)).2

def append (f g : ℕ → ℝ) (n : ℕ) (_ : f n = g 0) (i : ℕ) : ℝ := if i ≤ n then f i else g (i - n)

@[simp] lemma append_zero : append f g n h 0 = f 0 := by simp [append]

@[simp] lemma append_of_le (hi : n ≤ i) : append f g n h i = g (i - n) := by
  simp only [append, ite_eq_right_iff]
  intro hi'
  simp [le_antisymm hi' hi, h]

@[simp] lemma append_add : append f g n h (n + m) = g m := by
  rw [append_of_le (n.le_add_right m), Nat.add_sub_cancel_left]

def hAppend (σ : subdivision a b) (τ : subdivision b c) : subdivision a c where
  n := σ.n + 1 + τ.n
  toFun := append σ τ (σ.n + 1) (σ.last.trans τ.first.symm)
  first := by rw [append_zero, σ.first]
  last := by rw [add_assoc _ τ.n, append_add, τ.last]
  mono := by
    intro i hi j hj hij
    simp only [append]
    split_ifs with h'i h'j h'j
    · exact σ.mono h'i h'j hij
    · simp only [not_le] at h'j
      refine (σ.subset h'i).2.trans (τ.subset ?_).1
      simp only [tsub_le_iff_right, Set.mem_Iic] at hj ⊢
      convert hj using 1; abel
    · linarith -- impossible case
    · simp only [not_le] at h'i h'j
      simp only [Set.mem_Iic] at hi hj
      refine τ.mono ?_ ?_ (Nat.sub_le_sub_right hij (σ.n + 1))
      · simp only [ge_iff_le, Set.mem_Iic, tsub_le_iff_right]; convert hi using 1; abel
      · simp only [ge_iff_le, Set.mem_Iic, tsub_le_iff_right]; convert hj using 1; abel

instance {a b c : ℝ} : HAppend (subdivision a b) (subdivision b c) (subdivision a c) := ⟨hAppend⟩

def Icc (σ : subdivision a b) (i : Fin (σ.n + 1)) : Set ℝ := Set.Icc (σ i) (σ i.succ)

noncomputable def mesh (σ : subdivision a b) : ℝ := ⨆ i : Fin (σ.n + 1), |σ i.succ - σ i|

lemma le_mesh {i : Fin (σ.n + 1)} : |σ (i + 1) - σ i| ≤ σ.mesh :=
  le_ciSup (f := λ i : Fin (σ.n + 1) => |σ i.succ - σ i|) (finite_range _).bddAbove _

noncomputable def regular (hab : a ≤ b) (n : ℕ) : subdivision a b where
  n := n
  toFun := λ i => a + i * ((b - a) / (n + 1))
  first := by simp
  last := by field_simp; ring
  mono := λ i _ j _ hij => by
    have : 0 ≤ b - a := by linarith;
    simp; gcongr

@[simp] lemma regular_mesh (hab : a < b) : (regular hab.le n).mesh = (b - a) / (n + 1) := by
  have h1 : 0 ≤ b - a := sub_nonneg.2 hab.le
  have h2 : 0 ≤ (b - a) / (↑n + 1) := div_nonneg h1 n.cast_add_one_pos.le
  have : ∀ i : Fin (n + 1), |(i + 1) * ((b - a) / (n + 1)) - i * ((b - a) / (n + 1))| =
      (b - a) / (n + 1) := λ i => by
    simpa only [add_one_mul (i : ℝ), add_sub_cancel'] using abs_eq_self.2 h2
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

section pintegral

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

end pintegral