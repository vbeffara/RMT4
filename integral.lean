import Mathlib

variable [AddCommMonoid E] [SMul ℝ E]

open List Finset BigOperators

structure subdivision :=
  n : ℕ
  t : ℕ → ℝ
  ht : ∀ i < n, t i < t (i+1)

instance : CoeFun subdivision (λ _ => ℕ → ℝ) := ⟨subdivision.t⟩

namespace subdivision

def le (σ τ : subdivision) : Prop := ∀ i < σ.n, ∃ j < τ.n, σ i = τ j

instance : LE subdivision := ⟨subdivision.le⟩

@[ext] lemma le_ext {σ τ : subdivision} (h1 : σ.n = τ.n) (h2 : ∀ i ∈ Set.Iio σ.n, σ i = τ i) :
    σ = τ := sorry

lemma le_iff {σ τ : subdivision} : σ ≤ τ ↔ σ '' Set.Iio σ.n ⊆ τ '' Set.Iio τ.n := by
  constructor
  · rintro h1 t ⟨i, h2, rfl⟩
    obtain ⟨j, h3, h4⟩ := h1 i h2
    exact h4 ▸ ⟨j, h3, rfl⟩
  · intro h1 i h2
    obtain ⟨j, h3, h4⟩ := h1 ⟨i, h2, rfl⟩
    exact ⟨j, h3, h4.symm⟩

lemma le_refl {σ : subdivision} : σ ≤ σ := by rw [le_iff]

lemma le_trans {σ τ υ : subdivision} (hστ : σ ≤ τ) (hτυ : τ ≤ υ) : σ ≤ υ := by
  rw [le_iff] at hστ hτυ ⊢
  exact hστ.trans hτυ

lemma le_antisymm {σ τ : subdivision} (hστ : σ ≤ τ) (hτσ : τ ≤ σ) : σ = τ := by
  rw [le_iff] at hστ hτσ
  ext i
  cases' i with i hi
  · exact le_antisymm hστ hτσ
  · exact hστ ⟨i, hi, rfl⟩

instance : Preorder subdivision where
  le_refl := λ _ => le_refl
  le_trans := λ _ _ _ => le_trans

instance : PartialOrder subdivision where
  le_antisymm := sorry

end subdivision

def RiemannSum (f : ℝ → E) (σ : subdivision) : E :=
  ∑ i in Iio σ.n, (σ (i+1) - σ i) • f (σ i)

--

@[ext] structure subd :=
  l : List ℝ
  sorted : l.Sorted (· < ·)
  nonempty : 1 < l.length

namespace subd

variable {σ τ : subd}

def le (σ τ : subd) : Prop := σ.l ⊆ τ.l

instance : LE subd := ⟨le⟩

lemma le_refl : σ ≤ σ := List.Subset.refl σ.l

lemma le_trans (hστ : σ ≤ τ) (hτυ : τ ≤ υ) : σ ≤ υ := List.Subset.trans hστ hτυ

lemma le_antisymm (hστ : σ ≤ τ) (hτσ : τ ≤ σ) : σ = τ := by
  ext1
  refine eq_of_perm_of_sorted ?_ σ.sorted τ.sorted
  apply perm_of_nodup_nodup_toFinset_eq σ.sorted.nodup τ.sorted.nodup
  apply subset_antisymm <;> (intro t ht; aesop)

instance : PartialOrder subd where
  le_refl := λ _ => le_refl
  le_trans := λ _ _ _ => le_trans
  le_antisymm := λ _ _ => le_antisymm

end subd

def pairs : List α → List (α × α)
  | [] => []
  | (_ :: []) => []
  | x :: y :: ys => (x, y) :: pairs (y :: ys)

noncomputable def RiemannSum' (f : ℝ → E) (σ : subd) : E :=
  ∑ i in (pairs σ.l).toFinset, (i.2 - i.1) • f i.1