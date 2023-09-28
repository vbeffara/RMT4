import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Intervals.Basic
import RMT4.to_mathlib

open Set Metric BigOperators Topology Finset Nat

def splice (f g : ℕ → ℝ) (n : ℕ) (i : ℕ) : ℝ := if i ≤ n then f i else g (i - n)

def splice' (f g : ℕ → ℝ) (n : ℕ) (i : ℕ) : ℝ := if n ≤ i then g (i - n) else f i

lemma splice_eq_splice' (h : f n = g 0) : splice f g n = splice' f g n := by
  ext i; by_cases h1 : i ≤ n <;> by_cases h2 : n ≤ i
  · have := le_antisymm h1 h2; subst i; simp [splice, splice', h]
  · simp [splice, splice', h1, h2]
  · simp [splice, splice', h1, h2]
  · linarith

@[simp] lemma splice_zero : splice f g n 0 = f 0 := by simp [splice]

@[simp] lemma splice_of_le (h : f n = g 0) (hi : n ≤ i) : splice f g n i = g (i - n) := by
  rw [splice_eq_splice' h, splice']; simp only [hi, ite_true]

@[simp] lemma splice_add (h : f n = g 0) : splice f g n (n + m) = g m := by
  rw [splice_of_le h (n.le_add_right m), Nat.add_sub_cancel_left]

structure Subdivision (a b : ℝ) where
  n : ℕ
  toFun : Fin (n + 2) → ℝ
  first : toFun 0 = a
  last : toFun (Fin.last _) = b
  mono : Monotone toFun

namespace Subdivision

variable {a b c : ℝ} {n : ℕ} {σ : Subdivision a b}

instance : CoeFun (Subdivision a b) (λ σ => Fin (σ.n + 2) → ℝ) := ⟨toFun⟩

noncomputable def ofList (l : List ℝ) (hl : 2 ≤ l.length) (hl' : l.Sorted (· ≤ ·)):
    Subdivision (l.get ⟨0, (zero_lt_two.trans_le hl)⟩)
      (l.get ⟨l.length - 1, Nat.sub_one_sub_lt (zero_lt_two.trans_le hl)⟩) := by
    let n := l.length - 2
    have l1 : n + 2 = l.length := Nat.sub_add_cancel hl
    have l2 : l.length - 2 + 1 = l.length - 1 := eq_tsub_of_add_eq l1
    refine ⟨n, λ i => l.get (Fin.cast l1 i), rfl, by simp [Fin.cast, l2], ?_⟩
    exact Monotone.comp hl'.get_mono (λ i j => id)

noncomputable def ofFinset (s : Finset ℝ) (hs : 2 ≤ s.card) :
    Subdivision
      (s.min' (Finset.card_pos.1 (zero_lt_two.trans_le hs)))
      (s.max' (Finset.card_pos.1 (zero_lt_two.trans_le hs))) :=
  let l := s.sort (· ≤ ·)
  have l0 := Finset.card_pos.1 (zero_lt_two.trans_le hs)
  have l1 : 2 ≤ List.length l := by rwa [Finset.length_sort]
  have l2 : 0 < l.length := zero_lt_two.trans_le l1
  have l3 : l.get ⟨_, l2⟩ = s.min' l0 := by simp [Finset.min'_eq_sorted_zero] ; rfl
  have l4 : l.length - 1 < l.length := Nat.sub_one_sub_lt l2
  have l5 : l.get ⟨_, l4⟩ = s.max' l0 := by simp [Finset.max'_eq_sorted_last] ;  rfl
  l3 ▸ l5 ▸ ofList l l1 (Finset.sort_sorted _ _)

noncomputable def toFinset (σ : Subdivision a b) : Finset ℝ := Finset.image σ univ

lemma subset {σ : Subdivision a b} {i : Fin (σ.n + 2)} : σ i ∈ Set.Icc a b := by
  constructor
  · simpa only [← σ.first] using σ.mono (Fin.zero_le _)
  · simpa only [← σ.last] using σ.mono (Fin.le_last _)

lemma le (σ : Subdivision a b) : a ≤ b := by
  simpa only [← σ.first, ← σ.last] using σ.mono (Fin.zero_le _)

lemma mono' (σ : Subdivision a b) {i : Fin (σ.n + 1)} : σ i.castSucc ≤ σ i.succ :=
  Fin.monotone_iff_le_succ.1 σ.mono i

-- def hsplice (σ : Subdivision a b) (τ : Subdivision b c) : Subdivision a c where
--   n := σ.n + 1 + τ.n
--   toFun := splice σ τ (σ.n + 1)
--   first := by rw [splice_zero, σ.first]
--   last := by rw [add_assoc _ τ.n, splice_add (σ.last.trans τ.first.symm), τ.last]
--   mono i hi j hj hij := by
--     have hb : σ (σ.n + 1) = τ 0 := σ.last.trans τ.first.symm
--     have hh : τ.n + 1 + (σ.n + 1) = σ.n + 1 + τ.n + 1 := by abel
--     cases' le_total i (σ.n + 1) with h1 h1 <;> cases' le_total j (σ.n + 1) with h2 h2
--     · simpa [splice, h1, h2] using σ.mono h1 h2 hij
--     · rw [splice, splice_eq_splice' hb, splice']
--       simp only [h1, h2, ite_true]
--       refine (σ.subset h1).2.trans (τ.subset ?_).1
--       simpa only [tsub_le_iff_right, hh]
--     · rw [(by linarith : i = j)]
--     · simp only [splice_eq_splice' hb, splice', h1, h2, ite_true]
--       refine τ.mono ?_ ?_ (Nat.sub_le_sub_right hij (σ.n + 1)) <;>
--         simpa only [Set.mem_Iic, tsub_le_iff_right, hh]

-- instance {a b c : ℝ} : HAppend (Subdivision a b) (Subdivision b c) (Subdivision a c) := ⟨hsplice⟩

def Icc (σ : Subdivision a b) (i : Fin (σ.n + 1)) : Set ℝ := Set.Icc (σ i.castSucc) (σ i.succ)

lemma Icc_subset : σ.Icc i ⊆ Set.Icc a b := Set.Icc_subset_Icc subset.1 subset.2

def length (σ : Subdivision a b) (i : Fin (σ.n + 1)) : ℝ := σ i.succ - σ i.castSucc

noncomputable def lengths (σ : Subdivision a b) : Finset ℝ := Finset.image σ.length Finset.univ

noncomputable def mesh (σ : Subdivision a b) : ℝ := σ.lengths.max' (Finset.univ_nonempty.image _)

lemma le_mesh {i : Fin (σ.n + 1)} : σ i.succ - σ i.castSucc ≤ σ.mesh := by
  apply le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

noncomputable def regular (hab : a ≤ b) (n : ℕ) : Subdivision a b where
  n := n
  toFun i := a + i * ((b - a) / (n + 1))
  first := by simp
  last := by field_simp; ring
  mono i j hij := by
    have : 0 ≤ b - a := sub_nonneg_of_le hab
    have : 0 ≤ (b - a) / (↑n + 1) := by positivity
    simp ; gcongr ; exact hij

@[simp] lemma regular_mesh (hab : a ≤ b) : (regular hab n).mesh = (b - a) / (n + 1) := by
  have (i x : ℝ) : (i + 1) * x - i * x = x := by ring
  simp [mesh, lengths, length, regular, this, Finset.image_const, Finset.univ_nonempty]

variable {S : ι → Set ℝ}

structure adapted (σ : Subdivision a b) (S : ι → Set ℝ) :=
  I : Fin (σ.n + 1) → ι
  hI k : σ.Icc k ⊆ S (I k)

lemma adapted_of_mesh_lt (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : Subdivision a b, σ.mesh < ε → Nonempty (adapted σ S) := by
  obtain ⟨ε, hε, l1⟩ := lebesgue_number_lemma_of_metric isCompact_Icc h1 h2
  refine ⟨ε, hε, λ σ hσ => ?_⟩
  choose I hI using l1
  refine ⟨λ j => I (σ j.castSucc) σ.subset, λ j => ?_⟩
  have hi := hI (σ j.castSucc) σ.subset
  have : Set.OrdConnected (ball (σ j.castSucc) ε) := (convex_ball ..).ordConnected
  refine subset_trans ?_ hi
  refine Set.Icc_subset _ (mem_ball_self hε) ?_
  simp
  convert (le_mesh (i := j)).trans_lt hσ using 1
  refine abs_eq_self.2 (sub_nonneg.2 (σ.mono ?_))
  rw [Fin.le_def]
  simp

lemma adapted_of_mesh_le (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : Subdivision a b, σ.mesh ≤ ε → Nonempty (adapted σ S) := by
  obtain ⟨ε, hε, h⟩ := adapted_of_mesh_lt h1 h2
  refine ⟨ε / 2, by positivity, λ σ hσ => h σ (by linarith)⟩

structure adapted_subdivision (a b : ℝ) (S : ι → Set ℝ) :=
  σ : Subdivision a b
  h : adapted σ S

noncomputable def exists_adapted (hab : a ≤ b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    adapted_subdivision a b S := by
  choose ε hε h using adapted_of_mesh_le h1 h2
  choose n hn using exists_div_lt (sub_nonneg_of_le hab) hε
  have : (regular hab n).mesh = (b - a) / (n + 1) := regular_mesh hab
  exact ⟨_, (h (regular hab n) (by linarith)).some⟩

noncomputable def exists_adapted' (hab : a ≤ b) (h : ∀ t : Set.Icc a b, ∃ i, S i ∈ 𝓝[Set.Icc a b] t.1) :
    adapted_subdivision a b S := by
  choose I hI using h
  choose S' h1 h2 using λ t => (nhdsWithin_basis_open t.1 (Set.Icc a b)).mem_iff.1 (hI t)
  have : Set.Icc a b ⊆ ⋃ t, S' t := λ t ht => mem_iUnion.2 ⟨⟨t, ht⟩, (h1 ⟨t, ht⟩).1⟩
  obtain ⟨σ, hσ1, hσ2⟩ := exists_adapted hab (λ t => (h1 t).2) this
  exact ⟨σ, I ∘ hσ1, λ k => (Set.subset_inter (hσ2 k) σ.Icc_subset).trans (h2 (hσ1 k))⟩

structure reladapted (a b : ℝ) (S : ι → Set ℂ) (γ : ℝ → ℂ) :=
  σ : Subdivision a b
  I : Fin (σ.n + 1) → ι
  sub k : γ '' σ.Icc k ⊆ S (I k)

noncomputable def exists_reladapted {S : ι → Set ℂ} (hab : a ≤ b) (hγ : ContinuousOn γ (Set.Icc a b))
    (h : ∀ t : Set.Icc a b, ∃ i, S i ∈ 𝓝 (γ t.1)) : reladapted a b S γ := by
  choose I hI using h
  obtain ⟨σ, K, hK⟩ := exists_adapted' hab (λ t => ⟨t, hγ _ t.2 (hI t)⟩)
  exact ⟨σ, I ∘ K, λ k => image_subset_iff.2 (hK k)⟩

section sum

def sum (σ : Subdivision a b) (f : Fin (σ.n + 1) → ℝ → ℝ → ℂ) : ℂ :=
  ∑ i : _, f i (σ i.castSucc) (σ i.succ)

noncomputable abbrev sumSub (σ : Subdivision a b) (F : Fin (σ.n + 1) -> ℝ -> ℂ) : ℂ :=
  σ.sum (λ i x y => F i y - F i x)

noncomputable abbrev sumSubAlong (σ : Subdivision a b) (F : Fin (σ.n + 1) → ℂ → ℂ)
    (γ : ℝ → ℂ) : ℂ :=
  sumSub σ (λ i => F i ∘ γ)

lemma sum_eq_zero (h : ∀ i, F i (σ i.castSucc) (σ i.succ) = 0) : σ.sum F = 0 :=
  Finset.sum_eq_zero (λ i _ => h i)

lemma sum_congr {F G : Fin (σ.n + 1) → ℝ → ℝ → ℂ}
    (h : ∀ i, F i (σ i.castSucc) (σ i.succ) = G i (σ i.castSucc) (σ i.succ)) : σ.sum F = σ.sum G :=
  Finset.sum_congr rfl (λ i _ => h i)

end sum

end Subdivision
