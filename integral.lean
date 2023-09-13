import Mathlib

open List Finset BigOperators Function Metric

namespace Finset

variable [LinearOrder α]

@[simp] lemma min_union {s t : Finset α} : (s ∪ t).min = s.min ⊓ t.min := by
  simp [min_eq_inf_withTop, inf_union]

@[simp] lemma max_union {s t : Finset α} : (s ∪ t).max = s.max ⊔ t.max := by
  simp [max_eq_sup_withBot, sup_union]

@[simp] lemma min_toFinset {l : List α} : l.toFinset.min = l.minimum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, List.minimum_cons]

@[simp] lemma max_toFinset {l : List α} : l.toFinset.max = l.maximum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, List.maximum_cons]

end Finset

def List.pairs (l : List α) : List (α × α) := List.zip l l.tail

section topology

variable {K : Set ℝ} {S : ι → Set ℝ}

lemma bla (hK : IsCompact K) (hS : ∀ i, IsOpen (S i)) (hKS : K ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ x ∈ K, ∃ i, ball x ε ⊆ S i := by
  exact lebesgue_number_lemma_of_metric hK hS hKS

end topology

--

abbrev subd (a b : ℝ) := { s : Finset ℝ // s.min = a ∧ s.max = b }

noncomputable instance : Sup (subd a b) where
  sup := λ s t => ⟨s ∪ t, by simp [s.prop, t.prop]⟩

instance : Membership ℝ (subd a b) := ⟨λ x σ => x ∈ σ.val⟩

namespace subd

variable {a b : ℝ}

noncomputable def ofList (l : List ℝ) (ha : l.minimum = a) (hb : l.maximum = b) : subd a b :=
  ⟨l.toFinset, by simp [ha, hb]⟩

def cast (σ : subd a b) (ha : a = a') (hb : b = b') : subd a' b' := ⟨σ, by simp [ha, hb, σ.prop]⟩

noncomputable def points (σ : subd a b) : List ℝ := σ.val.sort (· ≤ ·)

noncomputable def pairs (σ : subd a b) : Finset (ℝ × ℝ) := σ.points.pairs.toFinset

variable [AddCommMonoid E] [SMul ℝ E]

noncomputable def RiemannSum (f : ℝ → E) (σ : subd a b) : E :=
  ∑ p in σ.pairs, (p.2 - p.1) • f p.1

def adapted (σ : subd a b) (S : ι → Set ℝ) : Prop :=
  ∀ p ∈ pairs σ, ∃ i, Set.Icc p.1 p.2 ⊆ S i

lemma toto (hab : a ≤ b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ σ : subd a b, adapted σ S := by
  obtain ⟨ε, hε, l1⟩ := lebesgue_number_lemma_of_metric isCompact_Icc h1 h2
  sorry

end subd