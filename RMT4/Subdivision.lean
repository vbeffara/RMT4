import Mathlib.Tactic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Set.Intervals.Basic

open Set Metric BigOperators Topology

lemma exists_div_lt {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) : ∃ n : ℕ, a / (n + 1) < ε := by
  cases ha.eq_or_lt with
  | inl h => simp [← h, hε]
  | inr h =>
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε h)
    use n
    convert (@strictMono_mul_left_of_pos ℝ _ a h).lt_iff_lt.2 hn using 1 <;> field_simp; ring

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
  toFun : ℕ → ℝ
  first : toFun 0 = a
  last : toFun (n + 1) = b
  mono : MonotoneOn toFun (Set.Iic (n + 1))

namespace Subdivision

variable {a b c : ℝ} {n : ℕ} {σ : Subdivision a b}

instance : CoeFun (Subdivision a b) (λ _ => ℕ → ℝ) := ⟨toFun⟩

lemma subset (σ : Subdivision a b) (hi : i ≤ σ.n + 1) : σ i ∈ Set.Icc a b := by
  constructor
  · simpa only [← σ.first] using σ.mono (zero_le (σ.n + 1)) hi (zero_le _)
  · simpa only [← σ.last] using σ.mono hi (le_refl (σ.n + 1)) hi

lemma le (σ : Subdivision a b) : a ≤ b := σ.first ▸ (σ.subset (zero_le _)).2

def hsplice (σ : Subdivision a b) (τ : Subdivision b c) : Subdivision a c where
  n := σ.n + 1 + τ.n
  toFun := splice σ τ (σ.n + 1)
  first := by rw [splice_zero, σ.first]
  last := by rw [add_assoc _ τ.n, splice_add (σ.last.trans τ.first.symm), τ.last]
  mono i hi j hj hij := by
    have hb : σ (σ.n + 1) = τ 0 := σ.last.trans τ.first.symm
    have hh : τ.n + 1 + (σ.n + 1) = σ.n + 1 + τ.n + 1 := by abel
    cases' le_total i (σ.n + 1) with h1 h1 <;> cases' le_total j (σ.n + 1) with h2 h2
    · simpa [splice, h1, h2] using σ.mono h1 h2 hij
    · rw [splice, splice_eq_splice' hb, splice']
      simp only [h1, h2, ite_true]
      refine (σ.subset h1).2.trans (τ.subset ?_).1
      simpa only [tsub_le_iff_right, hh]
    · rw [(by linarith : i = j)]
    · simp only [splice_eq_splice' hb, splice', h1, h2, ite_true]
      refine τ.mono ?_ ?_ (Nat.sub_le_sub_right hij (σ.n + 1)) <;>
        simpa only [Set.mem_Iic, tsub_le_iff_right, hh]

instance {a b c : ℝ} : HAppend (Subdivision a b) (Subdivision b c) (Subdivision a c) := ⟨hsplice⟩

def Icc (σ : Subdivision a b) (i : Fin (σ.n + 1)) : Set ℝ := Set.Icc (σ i) (σ i.succ)

lemma Icc_subset {i} : σ.Icc i ⊆ Set.Icc a b :=
  Set.Icc_subset_Icc (σ.subset Fin.is_le').1 (σ.subset (Fin.is_le _)).2

noncomputable def mesh (σ : Subdivision a b) : ℝ := ⨆ i : Fin (σ.n + 1), (σ i.succ - σ i)

lemma le_mesh {i : Fin (σ.n + 1)} : σ (i + 1) - σ i ≤ σ.mesh :=
  le_ciSup (f := λ i : Fin (σ.n + 1) => σ i.succ - σ i) (finite_range _).bddAbove _

noncomputable def regular (hab : a ≤ b) (n : ℕ) : Subdivision a b where
  n := n
  toFun i := a + i * ((b - a) / (n + 1))
  first := by simp
  last := by field_simp; ring
  mono i _ j _ hij := by
    have : 0 ≤ b - a := by linarith;
    simp; gcongr

@[simp] lemma regular_mesh (hab : a ≤ b) : (regular hab n).mesh = (b - a) / (n + 1) := by
  have (i) : (i + 1) * ((b - a) / (n + 1)) - i * ((b - a) / (n + 1)) = (b - a) / (n + 1) :=
    by field_simp; ring
  simp [mesh, regular, this]

variable {S : ι → Set ℝ}

structure adapted_witness (σ : Subdivision a b) (S : ι → Set ℝ) :=
  I : Fin (σ.n + 1) → ι
  hI : ∀ k, σ.Icc k ⊆ S (I k)

def adapted (σ : Subdivision a b) (S : ι → Set ℝ) : Prop := ∀ k, ∃ i, σ.Icc k ⊆ S i

noncomputable def adapted.witness (h : adapted σ S) : adapted_witness σ S := by
  choose I hI using h
  exact ⟨I, hI⟩

lemma adapted_of_mesh_lt (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : Subdivision a b, σ.mesh < ε → adapted σ S := by
  obtain ⟨ε, hε, l1⟩ := lebesgue_number_lemma_of_metric isCompact_Icc h1 h2
  refine ⟨ε, hε, λ σ hσ j => ?_⟩
  obtain ⟨i, hi⟩ := l1 (σ j.castSucc) (σ.subset j.prop.le)
  have : Set.OrdConnected (ball (σ j.castSucc) ε) := (convex_ball ..).ordConnected
  use i
  refine subset_trans ?_ hi
  refine Set.Icc_subset _ (mem_ball_self hε) ?_
  simp
  convert (le_mesh (i := j)).trans_lt hσ using 1
  refine abs_eq_self.2 (sub_nonneg.2 (σ.mono j.prop.le ?_ (Nat.le_succ _)))
  simpa using Nat.lt_succ.1 j.prop

lemma adapted_of_mesh_le (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : Subdivision a b, σ.mesh ≤ ε → adapted σ S := by
  obtain ⟨ε, hε, h⟩ := adapted_of_mesh_lt h1 h2
  refine ⟨ε / 2, by positivity, λ σ hσ => h σ (by linarith)⟩

noncomputable def exists_adapted (hab : a ≤ b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    { σ : Subdivision a b // adapted σ S } := by
  choose ε hε h using adapted_of_mesh_le h1 h2
  choose n hn using exists_div_lt (sub_nonneg_of_le hab) hε
  have : (regular hab n).mesh = (b - a) / (n + 1) := regular_mesh hab
  exact ⟨regular hab n, h _ (by linarith)⟩

noncomputable def exists_adapted' (hab : a ≤ b) (h : ∀ t : Set.Icc a b, ∃ i, S i ∈ 𝓝[Set.Icc a b] t.1) :
    { σ : Subdivision a b // adapted σ S } := by
  choose I hI using h
  choose S' h1 h2 using λ t => (nhdsWithin_basis_open t.1 (Set.Icc a b)).mem_iff.1 (hI t)
  have : Set.Icc a b ⊆ ⋃ t, S' t := λ t ht => mem_iUnion.2 ⟨⟨t, ht⟩, (h1 ⟨t, ht⟩).1⟩
  obtain ⟨σ, hσ⟩ := exists_adapted hab (λ t => (h1 t).2) this
  choose t ht using hσ
  exact ⟨σ, λ k => ⟨I (t k), (subset_inter (ht k) σ.Icc_subset).trans (h2 (t k))⟩⟩

def reladapted (σ : Subdivision a b) (S : ι → Set ℂ) (γ : ℝ → ℂ) : Prop :=
  ∀ k, ∃ i, γ '' σ.Icc k ⊆ S i

structure reladapted_witness (σ : Subdivision a b) (S : ι → Set ℂ) (γ : ℝ → ℂ) :=
  I : Fin (σ.n + 1) → ι
  hI : ∀ k, γ '' σ.Icc k ⊆ S (I k)

lemma reladapted.witness {S : ι → Set ℂ} (h : reladapted σ S γ) : reladapted_witness σ S γ := by
  choose I hI using h
  exact ⟨I, hI⟩

noncomputable def exists_reladapted {S : ι → Set ℂ} (hab : a ≤ b) (hγ : ContinuousOn γ (Set.Icc a b))
    (h : ∀ t : Set.Icc a b, ∃ i, S i ∈ 𝓝 (γ t.1)) :
    { σ : Subdivision a b // reladapted σ S γ } := by
  choose I hI using h
  let S' (t : Set.Icc a b) := γ ⁻¹' S (I t)
  have h1 (t : Set.Icc a b) : ∃ i, S' i ∈ 𝓝[Set.Icc a b] t.1 := ⟨t, hγ _ t.2 (hI t)⟩
  obtain ⟨σ, hσ⟩ := exists_adapted' hab h1
  refine ⟨σ, λ k => ?_⟩
  obtain ⟨t, ht⟩ := hσ k
  refine ⟨I t, image_subset_iff.2 ht⟩

def sum (σ : Subdivision a b) (f : ℕ → ℝ → ℝ → ℂ) : ℂ :=
  ∑ i in Finset.range (σ.n + 1), f i (σ i) (σ (i + 1))

noncomputable def sumSub (σ : Subdivision a b) (F : Fin (σ.n + 1) -> ℝ -> ℂ) : ℂ :=
  σ.sum (λ i x y => F i y - F i x)

noncomputable def sumSubAlong (σ : Subdivision a b) (F : Fin (σ.n + 1) → ℂ → ℂ)
    (γ : ℝ → ℂ) : ℂ :=
  sumSub σ (λ i => F i ∘ γ)

lemma telescopic : sumSub σ (λ _ => f) = f b - f a := by
  simpa only [← σ.first, ← σ.last] using Finset.sum_range_sub (f ∘ σ) _

end Subdivision