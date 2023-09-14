import Mathlib

open List Finset BigOperators Function Metric WithBot

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

namespace List

def pairs (l : List α) : List (α × α) := List.zip l l.tail

def progression (a δ : ℝ) : ℕ → List ℝ
| 0 => [a]
| n+1 => a :: List.progression (a + δ) δ n

lemma minimum_progression (h : 0 ≤ δ) : (progression a δ n).minimum = a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [progression, minimum_cons, ih, h]

lemma toto (h : 0 ≤ δ) : ∀ x ∈ progression a δ n, a ≤ x := by
  induction n generalizing a with
  | zero => simp [progression]
  | succ n ih =>
    simp [progression]
    intro x hx
    linarith [ih x hx]

lemma maximum_progression (h : 0 ≤ δ) : (progression a δ n).maximum = a + n * δ := by
  induction n generalizing a with
  | zero => simp [progression]
  | succ n ih =>
    simp only [progression, maximum_cons, ih, Nat.cast_succ]
    have e1 : (1 : WithBot ℝ) = ((1 : ℕ) : ℝ) := by norm_cast
    have e2 : (n : WithBot ℝ) = (n : ℝ) := by norm_cast
    have e3 : 0 ≤ (n : ℝ) := n.cast_nonneg
    convert max_eq_right ?_ using 1
    · simp only [e1, e2, ← WithBot.coe_mul, ← WithBot.coe_add, WithBot.coe_eq_coe]
      ring
    · simp only [e1, e2, ← WithBot.coe_mul, ← WithBot.coe_add, WithBot.coe_le_coe]
      nlinarith [e3]

noncomputable def prog (a h : ℝ) : ℕ → List ℝ
| 0 => [a]
| n + 1 => a :: prog (a + h) h n

lemma prog_length : (prog a h n).length = n + 1 := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih => simp [prog, ih]

lemma prog_ne_nil : prog a h n ≠ [] := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih => simp [prog, ih]

lemma List.Sorted.map [Preorder α] [Preorder β] {l : List α} {f : α → β}
  (h : l.Sorted (· ≤ ·)) (hf : Monotone f) : (l.map f).Sorted (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp at h
    simp [ih h.2]
    intro a' ha'
    exact hf (h.1 a' ha')

lemma prog_le (hh : 0 ≤ h) (hx : x ∈ prog a h n) : a ≤ x := by
  induction n generalizing a with
  | zero => simp [prog] at hx; linarith
  | succ n ih =>
    simp [prog] at hx
    cases hx with
    | inl h => linarith
    | inr h => linarith [ih h]

lemma prog_sorted (hh : 0 ≤ h) : (prog a h n).Sorted (· ≤ ·) := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih =>
    simp [prog, ih]
    intro b hb
    linarith [prog_le hh hb]

lemma prog_sorted' (hh : 0 < h) : (prog a h n).Sorted (· < ·) := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih =>
    simp [prog, ih]
    intro b hb
    linarith [prog_le hh.le hb]

lemma prog_last : (prog a h n).getLast prog_ne_nil = a + n * h := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih => simp [prog, getLast_cons prog_ne_nil, ih]; ring

lemma prog_sub (hh : 0 ≤ h) : (prog a h n).pairs.map (λ p => |p.2 - p.1|) = List.replicate n h := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih =>
    simp [pairs, prog]
    cases' n with n
    · simp [hh]
    · simp [hh]; exact ih (a := a + h)

end List

--

abbrev subd (a b : ℝ) := { s : Finset ℝ // s.min = a ∧ s.max = b }

structure subdivides (s : Finset ℝ) (a b : ℝ) : Prop where
  nonempty : s.Nonempty
  min : s.min' nonempty = a
  max : s.max' nonempty = b

namespace subd

variable {a b : ℝ} {n : ℕ} {σ : subd a b}

noncomputable def ofList (l : List ℝ) (ha : l.minimum = a) (hb : l.maximum = b) : subd a b :=
  ⟨l.toFinset, by simp [ha, hb]⟩

noncomputable def regular (h : a ≤ b) (hn : 0 < n) : subd a b :=
  have h1 : 0 ≤ (b - a) / n := (div_nonneg (sub_nonneg_of_le h) (Nat.cast_nonneg n))
  have h2 : minimum (progression a ((b - a) / n) n) = a := minimum_progression h1
  have h3 : maximum (progression a ((b - a) / n) n) = b := by
    rw [maximum_progression h1]
    norm_cast
    rw [← WithBot.coe_add]
    field_simp [mul_comm, hn]
  ofList (List.progression a ((b - a) / n) n) h2 h3

end subd

-----------------------------

structure List.subdivides (l : List ℝ) (a b : ℝ) : Prop where
  nonempty : l ≠ []
  sorted : l.Sorted (· ≤ ·)
  -- nodup : l.Nodup
  first : l.head nonempty = a
  last : l.getLast nonempty = b

lemma List.Sorted.head_le {l : List ℝ} (hl : l.Sorted (· ≤ ·)) (hx : x ∈ l) :
    l.head (ne_nil_of_mem hx) ≤ x := by
  match l with
  | a :: as => cases hx with
    | head => rfl
    | tail e1 h => exact (sorted_cons.1 hl).1 _ h

lemma List.Sorted.le_last {l : List ℝ} (hl : l.Sorted (· ≤ ·)) (hx : x ∈ l) :
    x ≤ l.getLast (ne_nil_of_mem hx) := by
  induction l with
  | nil => cases hx
  | cons a as ih => cases hx with
    | head => match as with
      | [] => rfl
      | b :: bs => simpa only [getLast_cons_cons] using (sorted_cons.1 hl).1 _ (getLast_mem _)
    | tail e h => match as with
      | [] => cases h
      | _ :: _ => exact ih (sorted_cons.1 hl).2 h

lemma List.Sorted.head_le_last {l : List ℝ} (hl : l.Sorted (· ≤ ·)) (h : l ≠ []) :
    l.head h ≤ l.getLast h := by
  exact hl.le_last (head_mem h)

abbrev subdivision (a b : ℝ) := { l : List ℝ // l.subdivides a b }

namespace subdivision

variable {a b x : ℝ} {σ : subdivision a b} {l : List ℝ} {f : ℝ → ℝ}

lemma le (σ : subdivision a b) : a ≤ b := by
  convert σ.prop.sorted.head_le_last σ.prop.nonempty <;> simp [σ.prop.first, σ.prop.last]

instance : Membership ℝ (subdivision a b) := ⟨λ x σ => x ∈ σ.val⟩

-- noncomputable instance : Sup (subdivision a b) where
--   sup := by
--     intro σ τ
--     refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
--     · exact (σ.val.toFinset ∪ τ.val.toFinset).sort (· ≤ ·)
--     · apply ne_nil_of_mem (a := a); simp [← σ.prop.first, head_mem]
--     · apply Finset.sort_sorted
--     · apply Finset.sort_nodup
--     all_goals {sorry}

def bot_of_eq : subdivision a a := ⟨[a], by simp, by simp, /-by simp,-/ rfl, rfl⟩

def bot_of_lt (hab : a < b) : subdivision a b :=
⟨[a, b], by simp, by simp [hab.le], /-by simp [hab.ne],-/ rfl, rfl⟩

def cast (σ : subdivision a b) (ha : a = a') (hb : b = b') : subdivision a' b' :=
  ⟨σ, σ.prop.nonempty, σ.prop.sorted, /-σ.prop.nodup,-/ ha ▸ σ.prop.first, hb ▸ σ.prop.last⟩

noncomputable instance [le : Fact (a ≤ b)] : Bot (subdivision a b) :=
  ⟨if h : a = b then cast bot_of_eq rfl h else bot_of_lt (lt_of_le_of_ne le.out h)⟩

noncomputable def regular' (a b : ℝ) (n : ℕ) : List ℝ := prog a ((b - a) / (n + 1)) (n + 1)

lemma regular'_length : (regular' a b n).length = n + 2 := by simp [regular', prog_length]

noncomputable def regular (h : a < b) (n : ℕ) : subdivision a b where
  val := regular' a b n
  property := ⟨
    by apply length_pos.mp; simp [regular'_length],
    by
      have : 0 < b - a := by linarith
      exact List.prog_sorted (div_pos this (Nat.cast_add_one_pos n)).le,
    /-by
      have : 0 < b - a := by linarith
      have := List.prog_sorted' (a := a) (n := n + 1) (div_pos this (Nat.cast_add_one_pos n))
      exact this.nodup,-/
    rfl,
    by convert prog_last using 1; field_simp; ring⟩

lemma one_lt_length (hab : a < b) : 1 < (σ : List ℝ).length := by
  rcases σ with ⟨l, h1, h2, /-h3,-/ h4, h5⟩ ; match l with
  | [_] => linarith [h4.symm.trans h5]
  | _ :: _ :: l => simp

noncomputable def pairs (σ : subdivision a b) : List (ℝ × ℝ) := (σ : List ℝ).pairs

lemma pos_length_pairs (hab : a < b) : 0 < σ.pairs.length := by
  simp [pairs, List.pairs, one_lt_length hab]

lemma subset (hx : x ∈ σ) : x ∈ Set.Icc a b := by
  rcases σ with ⟨l, h1, h2, /-h3,-/ h4, h5⟩
  exact ⟨h4 ▸ h2.head_le hx, h5 ▸ h2.le_last hx⟩

noncomputable def mesh (σ : subdivision a b) : ℝ :=
  if h : a < b
  then (σ.pairs.map (λ p => |p.2 - p.1|)).maximum_of_length_pos (by simpa using pos_length_pairs h)
  else 0

lemma maximum_replicate : maximum (replicate (n + 1) a) = a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [replicate_succ, maximum_cons, ih, max_self]

lemma regular_mesh (hab : a < b) : (regular hab n).mesh = (b - a) / (n + 1) := by
  have : 0 ≤ (b - a) / (↑n + 1) := (div_pos (by linarith) (Nat.cast_add_one_pos n)).le
  simp only [mesh, hab, pairs, regular, regular', prog_sub this, Nat.add_eq, add_zero, dite_true]
  simp only [maximum_of_length_pos, maximum_replicate, unbot_coe]

lemma le_mesh (hab : a < b) (hp : p ∈ σ.pairs) : |p.2 - p.1| ≤ σ.mesh := by
  have h1 : |p.2 - p.1| ∈ σ.pairs.map (λ p => |p.2 - p.1|) :=
    List.mem_map_of_mem (λ p : ℝ × ℝ => |p.2 - p.1|) hp
  have h2 : 0 < (List.map (fun p => |p.snd - p.fst|) (pairs σ)).length := by
    simpa using pos_length_pairs hab
  simp only [mesh, hab]
  simpa only [← coe_maximum_of_length_pos h2, coe_le_coe] using le_maximum_of_mem' h1

def adapted (σ : subdivision a b) (S : ι → Set ℝ) : Prop :=
  ∀ p ∈ σ.pairs, ∃ i, Set.Icc p.1 p.2 ⊆ S i

lemma adapted_of_mesh_lt (hab : a < b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ {σ : subdivision a b}, σ.mesh < ε → adapted σ S := by
  obtain ⟨ε, hε, l1⟩ := lebesgue_number_lemma_of_metric isCompact_Icc h1 h2
  refine ⟨ε, hε, λ hσ p hp => ?_⟩
  have : Set.OrdConnected (ball p.1 ε) := (convex_ball ..).ordConnected
  obtain ⟨i, hi⟩ := l1 p.1 (subset (List.mem_zip hp).1)
  exact ⟨i, subset_trans (Set.Icc_subset _ (mem_ball_self hε) ((le_mesh hab hp).trans_lt hσ)) hi⟩

lemma exists_div_lt {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε): ∃ n : ℕ, a / (n + 1) < ε := by
  have e1 : 0 < ε / a := div_pos hε ha
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt e1
  use n
  convert (@strictMono_mul_left_of_pos ℝ _ a ha).lt_iff_lt.2 hn using 1 <;> field_simp; ring

lemma exists_adapted (hab : a < b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ σ : subdivision a b, adapted σ S := by
  obtain ⟨ε, hε, h⟩ := adapted_of_mesh_lt hab h1 h2
  obtain ⟨n, hn⟩ := exists_div_lt (sub_pos_of_lt hab) hε
  have : (regular hab n).mesh = (b - a) / (n + 1) := regular_mesh hab
  refine ⟨regular hab n, h (by linarith)⟩

variable [AddCommMonoid E] [SMul ℝ E]

noncomputable def RS (f : ℝ → E) (σ : subdivision a b) : E :=
  (σ.pairs.map (λ p => (p.2 - p.1) • f p.1)).sum

end subdivision