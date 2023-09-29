import Mathlib.Tactic
import RMT4.to_mathlib

open Set Function List Topology BigOperators Nat

abbrev Subdivision (a b : ℝ) := Finset (Ioo a b)

namespace Subdivision

variable {a b : ℝ} {σ : Subdivision a b}

section basic

def cast (σ : Subdivision a b) (ha : a = a') (hb : b = b') : Subdivision a' b' := ha ▸ hb ▸ σ

def size (σ : Subdivision a b) : ℕ := Finset.card σ

noncomputable def toList (σ : Subdivision a b) : List ℝ :=
  a :: (Finset.sort (· ≤ ·) σ).map Subtype.val ++ [b]

@[simp] lemma toList_length : σ.toList.length = σ.size + 2 := by simp [toList, size]

lemma toList_sorted (hab : a ≤ b) : σ.toList.Sorted (· ≤ ·) := by
  simp only [toList, cons_append, sorted_cons, mem_append, Finset.mem_sort, List.mem_singleton]
  constructor
  · intro t ht ; cases ht with
    | inl h => obtain ⟨u₁, _, rfl⟩ := List.mem_map.1 h ; exact u₁.prop.1.le
    | inr h => linarith
  . simp [Sorted, pairwise_append] ; constructor
    · apply (Finset.sort_sorted _ _).map ; exact fun _ _ => id
    · rintro t ⟨h₁, h₂⟩ _ ; exact h₂.le

noncomputable def toFun (σ : Subdivision a b) : Fin (σ.size + 2) → ℝ :=
  σ.toList.get ∘ Fin.cast toList_length.symm

noncomputable instance : CoeFun (Subdivision a b) (λ σ => Fin (σ.size + 2) → ℝ) := ⟨toFun⟩

noncomputable abbrev x (σ : Subdivision a b) (i : Fin (σ.size + 1)) : ℝ := σ i.castSucc

noncomputable abbrev y (σ : Subdivision a b) (i : Fin (σ.size + 1)) : ℝ := σ i.succ

lemma mono (hab : a ≤ b) : Monotone σ.toFun :=
  (toList_sorted hab).get_mono.comp (λ _ _ => id)

lemma mono' (hab : a ≤ b) {i : Fin (σ.size + 1)} : σ.x i ≤ σ.y i :=
  Fin.monotone_iff_le_succ.1 (σ.mono hab) i

@[simp] lemma first : σ 0 = a := rfl

@[simp] lemma last : σ (Fin.last _) = b := by convert List.get_last _ ; simp

lemma toList_subset (hab : a ≤ b) (ht : t ∈ σ.toList) : t ∈ Icc a b := by
  simp [toList] at ht
  rcases ht with rfl | ⟨h, _⟩ | rfl
  · exact left_mem_Icc.2 hab
  · exact ⟨h.1.le, h.2.le⟩
  · exact right_mem_Icc.2 hab

lemma subset (hab : a ≤ b) : σ i ∈ Icc a b :=
  toList_subset hab (by simpa [toFun] using List.get_mem _ _ _)

end basic

section pieces

def piece (σ : Subdivision a b) (i : Fin (σ.size + 1)) : Set ℝ := Icc (σ.x i) (σ.y i)

lemma piece_subset (hab : a ≤ b) : σ.piece i ⊆ Icc a b :=
  Icc_subset_Icc (subset hab).1 (subset hab).2

noncomputable def length (σ : Subdivision a b) (i : Fin (σ.size + 1)) : ℝ := σ.y i - σ.x i

noncomputable def lengths (σ : Subdivision a b) : Finset ℝ := Finset.univ.image σ.length

noncomputable def mesh (σ : Subdivision a b) : ℝ := σ.lengths.max' (Finset.univ_nonempty.image _)

lemma le_mesh {i : Fin (σ.size + 1)} : σ.y i - σ.x i ≤ σ.mesh := by
  apply Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end pieces

namespace regular

noncomputable def aux (a b : ℝ) (n i : ℕ) : ℝ := a + i * ((b - a) / (n + 1))

@[simp] lemma aux_zero : aux a b n 0 = a := by simp [aux]

@[simp] lemma aux_last : aux a b n (n + 1) = b := by field_simp [aux] ; ring

lemma aux_mono (hab : a < b) : StrictMono (aux a b n) := by
  have := sub_pos.2 hab
  intro i j hij
  simp only [aux, add_lt_add_iff_left]
  gcongr ; simp [hij]

lemma aux_mem_Ioo (hab : a < b) (h : i < n) : aux a b n (i + 1) ∈ Ioo a b := by
  constructor
  · convert aux_mono hab (succ_pos i) ; simp
  · convert aux_mono hab (succ_lt_succ h) ; simp

noncomputable def list (a b : ℝ) (n : ℕ) : List ℝ :=
  (List.range n).map (λ i => aux a b n (i + 1))

lemma list_sorted (hab : a < b) : (list a b n).Sorted (· < ·) :=
  (pairwise_lt_range n).map _ (λ _ _ hij => aux_mono hab (succ_lt_succ hij))

lemma list_mem_Ioo (hab : a < b) : ∀ x ∈ list a b n, x ∈ Ioo a b := by
  simp only [list, mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact λ i hi => aux_mem_Ioo hab hi

noncomputable def list' (hab : a < b) (n : ℕ) : List (Ioo a b) :=
  (list a b n).pmap Subtype.mk (list_mem_Ioo hab)

lemma list'_sorted (hab : a < b) : (list' hab n).Sorted (· < ·) :=
  (list_sorted hab).pmap _ (λ _ _ _ _ => id)

noncomputable def _root_.Subdivision.regular (hab : a < b) (n : ℕ) : Subdivision a b :=
  (list' hab n).toFinset

@[simp] lemma size : (regular hab n).size = n := by
  simp [regular, Subdivision.size, toFinset_card_of_nodup, (list'_sorted hab).nodup]
  simp [list', list]

@[simp] lemma eq_aux (hab : a < b) {i : Fin _} :
    List.get (a :: (map Subtype.val (list' hab n) ++ [b])) i = aux a b n i := by
  apply Fin.cases (motive := λ i => _ = _) (by simp)
  intro i
  simp only [List.get, add_eq, add_zero, Fin.eta, length_cons, Fin.val_succ]
  by_cases i < (map Subtype.val (list' hab n)).length
  · rcases i with ⟨i, hi⟩
    simp only [List.get_append i h, get_map]
    simp [list', List.get_pmap, list]
  · simp only [List.get_last h]
    convert aux_last.symm
    rcases i with ⟨i, h'i⟩
    simp [list', list] at h h'i
    linarith

@[simp] lemma eq (hab : a < b) {i} : regular hab n i = aux a b n i := by
  rcases i with ⟨i, hi⟩
  have l1 : Finset.sort (· ≤ ·) (List.toFinset (list' hab n)) = list' hab n := by
    apply List.Sorted.toFinset_sort
    exact list'_sorted hab
  have l3 : i < (a :: (map Subtype.val (list' hab n) ++ [b])).length := by
    simpa [list', list] using hi
  have l2 : List.get (a :: (map Subtype.val (list' hab n) ++ [b])) ⟨_, l3⟩ = aux a b n i := by
    exact eq_aux hab
  simp only [toFun, regular, toList, cons_append, length_cons, comp_apply]
  convert l2
  simp [toFinset_card_of_nodup, (list'_sorted hab).nodup]

@[simp] lemma length_eq (hab : a < b) {i : Fin _} :
    length (regular hab n) i = (b - a) / (n + 1) := by
  have (i x : ℝ) : (i + 1) * x - i * x = x := by ring
  simp [length, aux, this, x, y]

@[simp] lemma lengths_eq (hab : a < b) : lengths (regular hab n) = { (b - a) / (n + 1) } := by
  have : length (regular hab n) = λ (i : Fin _) => (b - a) / (n + 1) := by ext; simp
  rw [lengths, this]
  apply Finset.image_const Finset.univ_nonempty

@[simp] lemma mesh_eq (hab : a < b) : (regular hab n).mesh = (b - a) / (n + 1) := by
  simp [mesh, hab]

end regular

section adapted

variable {S : ι → Set ℝ}

structure adapted (σ : Subdivision a b) (S : ι → Set ℝ) :=
  I : Fin (σ.size + 1) → ι
  hI k : σ.piece k ⊆ S (I k)

lemma adapted_of_mesh_lt (hab : a ≤ b) (h1 : ∀ i, IsOpen (S i)) (h2 : Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : Subdivision a b, σ.mesh < ε → Nonempty (adapted σ S) := by
  obtain ⟨ε, hε, l1⟩ := lebesgue_number_lemma_of_metric isCompact_Icc h1 h2
  refine ⟨ε, hε, λ σ hσ => ?_⟩
  choose I hI using l1
  refine ⟨λ j => I (σ.x j) (σ.subset hab), λ j => ?_⟩
  have : Set.OrdConnected (Metric.ball (σ.x j) ε) := (convex_ball ..).ordConnected
  refine subset_trans ?_ (hI (σ.x j) (σ.subset hab))
  refine Set.Icc_subset _ (Metric.mem_ball_self hε) ?_
  simp only [Metric.mem_ball]
  convert (le_mesh (i := j)).trans_lt hσ using 1
  refine abs_eq_self.2 (sub_nonneg.2 (σ.mono hab ?_))
  simp [Fin.le_def]

lemma adapted_of_mesh_le (hab : a ≤ b) (h1 : ∀ i, IsOpen (S i)) (h2 : Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : Subdivision a b, σ.mesh ≤ ε → Nonempty (adapted σ S) := by
  obtain ⟨ε, hε, h⟩ := adapted_of_mesh_lt hab h1 h2
  refine ⟨ε / 2, by positivity, λ σ hσ => h σ (by linarith)⟩

structure adapted_subdivision (a b : ℝ) (S : ι → Set ℝ) :=
  σ : Subdivision a b
  h : adapted σ S

noncomputable def exists_adapted (hab : a < b) (h1 : ∀ i, IsOpen (S i)) (h2 : Icc a b ⊆ ⋃ i, S i) :
    adapted_subdivision a b S := by
  choose ε hε h using adapted_of_mesh_le hab.le h1 h2
  choose n hn using exists_div_lt (sub_nonneg_of_le hab.le) hε
  have : (regular hab n).mesh = (b - a) / (n + 1) := by simp
  exact ⟨_, (h (regular hab n) (by linarith)).some⟩

noncomputable def exists_adapted' (hab : a < b) (h : ∀ t : Icc a b, ∃ i, S i ∈ 𝓝[Icc a b] t.1) :
    adapted_subdivision a b S := by
  choose I hI using h
  choose S' h1 h2 using λ t => (nhdsWithin_basis_open t.1 (Icc a b)).mem_iff.1 (hI t)
  have : Icc a b ⊆ ⋃ t, S' t := λ t ht => mem_iUnion.2 ⟨⟨t, ht⟩, (h1 ⟨t, ht⟩).1⟩
  obtain ⟨σ, hσ1, hσ2⟩ := exists_adapted hab (λ t => (h1 t).2) this
  exact ⟨σ, I ∘ hσ1, λ k => (Set.subset_inter (hσ2 k) (σ.piece_subset hab.le)).trans (h2 (hσ1 k))⟩

structure reladapted (a b : ℝ) (S : ι → Set ℂ) (γ : ℝ → ℂ) :=
  σ : Subdivision a b
  I : Fin (σ.size + 1) → ι
  sub k : γ '' σ.piece k ⊆ S (I k)

noncomputable def exists_reladapted {S : ι → Set ℂ} (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (h : ∀ t : Icc a b, ∃ i, S i ∈ 𝓝 (γ t.1)) : reladapted a b S γ := by
  choose I hI using h
  obtain ⟨σ, K, hK⟩ := exists_adapted' hab (λ t => ⟨t, hγ _ t.2 (hI t)⟩)
  exact ⟨σ, I ∘ K, λ k => image_subset_iff.2 (hK k)⟩

end adapted

section sum

noncomputable def sum (σ : Subdivision a b) (f : Fin (σ.size + 1) → ℝ → ℝ → ℂ) : ℂ :=
  ∑ i : _, f i (σ.x i) (σ.y i)

noncomputable abbrev sumSub (σ : Subdivision a b) (F : Fin (σ.size + 1) → ℝ → ℂ) : ℂ :=
  σ.sum (λ i x y => F i y - F i x)

noncomputable abbrev sumSubAlong (σ : Subdivision a b) (F : Fin (σ.size + 1) → ℂ → ℂ)
    (γ : ℝ → ℂ) : ℂ :=
  sumSub σ (λ i => F i ∘ γ)

lemma sum_eq_zero (h : ∀ i, F i (σ.x i) (σ.y i) = 0) : σ.sum F = 0 :=
  Finset.sum_eq_zero (λ i _ => h i)

lemma sum_congr (h : ∀ i, F i (σ.x i) (σ.y i) = G i (σ.x i) (σ.y i)) :
    σ.sum F = σ.sum G :=
  Finset.sum_congr rfl (λ i _ => h i)

end sum

end Subdivision
