import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic

open List BigOperators Metric Set

namespace List

def pairs (l : List α) : List (α × α) := zip l l.tail

def prog (a h : ℝ) : ℕ → List ℝ
| 0     => [a]
| n + 1 => a :: prog (a + h) h n

namespace prog

@[simp] lemma length : (prog a h n).length = n + 1 := by
  induction n generalizing a <;> simp [prog, *]

@[simp] lemma ne_nil : prog a h n ≠ [] := by cases n <;> simp [prog]

lemma le (hh : 0 ≤ h) (hx : x ∈ prog a h n) : a ≤ x := by
  induction n generalizing a with
  | zero => simp [prog] at hx; linarith
  | succ n ih =>
    simp [prog] at hx
    cases hx with
    | inl h => linarith
    | inr h => linarith [ih h]

lemma sorted (hh : 0 ≤ h) : (prog a h n).Sorted (· ≤ ·) := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih =>
    simp [prog, ih]
    intro b hb
    linarith [prog.le hh hb]

@[simp] lemma last : (prog a h n).getLast hnil = a + n * h := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih => simp [prog, getLast_cons, ih]; ring

lemma sub (hh : 0 ≤ h) : (prog a h n).pairs.map (λ p => |p.2 - p.1|) = List.replicate n h := by
  induction n generalizing a with
  | zero => simp [prog]
  | succ n ih =>
    simp [pairs, prog]
    cases' n with n
    · simp [hh]
    · simp [hh]; exact ih (a := a + h)

end prog

noncomputable def regular (a b : ℝ) (n : ℕ) : List ℝ := prog a ((b - a) / (n + 1)) (n + 1)

@[simp] lemma regular_length : (regular a b n).length = n + 2 := by simp [regular]

namespace Sorted

lemma head_le {l : List ℝ} (hl : l.Sorted (· ≤ ·)) (hx : x ∈ l) :
    l.head (ne_nil_of_mem hx) ≤ x := by
  match l with
  | a :: as => cases hx with
    | head => rfl
    | tail e1 h => exact rel_of_sorted_cons hl _ h

lemma le_last {l : List ℝ} (hl : l.Sorted (· ≤ ·)) (hx : x ∈ l) :
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

lemma head_le_last {l : List ℝ} (hl : l.Sorted (· ≤ ·)) (h : l ≠ []) :
    l.head h ≤ l.getLast h := by
  exact hl.le_last (head_mem h)

end Sorted

structure subdivides (l : List ℝ) (a b : ℝ) : Prop where
  nonempty : l ≠ []
  sorted : l.Sorted (· ≤ ·)
  first : l.head nonempty = a
  last : l.getLast nonempty = b

end List

abbrev subdivision (a b : ℝ) := { l : List ℝ // l.subdivides a b }

namespace subdivision

variable {a b x : ℝ} {σ : subdivision a b} {l : List ℝ} {f : ℝ → ℝ}

lemma le (σ : subdivision a b) : a ≤ b := by
  convert σ.prop.sorted.head_le_last σ.prop.nonempty <;> simp [σ.prop.first, σ.prop.last]

instance : Membership ℝ (subdivision a b) := ⟨λ x σ => x ∈ σ.val⟩

-- noncomputable instance : Sup (subdivision a b) where
--   sup := by
--     intro σ τ
--     refine ⟨σ.val.merge (· ≤ ·) τ.val, ?_, ?_, ?_, ?_⟩
--     · sorry
--     · exact σ.prop.sorted.merge τ.prop.sorted
--     · sorry
--     · sorry

def bot_of_self : subdivision a a := ⟨[a], by simp, by simp, rfl, rfl⟩

def bot_of_lt (hab : a < b) : subdivision a b :=
⟨[a, b], by simp, by simp [hab.le], rfl, rfl⟩

def cast (σ : subdivision a b) (ha : a = a') (hb : b = b') : subdivision a' b' :=
  ⟨σ, σ.prop.nonempty, σ.prop.sorted, ha ▸ σ.prop.first, hb ▸ σ.prop.last⟩

noncomputable instance [le : Fact (a ≤ b)] : Bot (subdivision a b) :=
  ⟨if h : a = b then cast bot_of_self rfl h else bot_of_lt (lt_of_le_of_ne le.out h)⟩

noncomputable def regular (hab : a ≤ b) (n : ℕ) : subdivision a b where
  val := List.regular a b n
  property := ⟨
    by apply length_pos.mp; simp,
    by
      have : 0 ≤ b - a := by linarith;
      exact List.prog.sorted (by positivity),
    rfl,
    by convert prog.last using 1; field_simp; ring⟩

lemma one_lt_length (hab : a < b) : 1 < (σ : List ℝ).length := by
  rcases σ with ⟨l, h1, h2, h4, h5⟩ ; match l with
  | [_] => linarith [h4.symm.trans h5]
  | _ :: _ :: l => simp

noncomputable def pairs (σ : subdivision a b) : List (ℝ × ℝ) := (σ : List ℝ).pairs

lemma pos_length_pairs (hab : a < b) : 0 < σ.pairs.length := by
  simp [pairs, List.pairs, one_lt_length hab]

noncomputable def fst (σ : subdivision a b) (i : Fin σ.pairs.length) : ℝ := (σ.pairs.get i).1

noncomputable def snd (σ : subdivision a b) (i : Fin σ.pairs.length) : ℝ := (σ.pairs.get i).2

def Icc (i : Fin σ.pairs.length) : Set ℝ := Set.Icc (σ.fst i) (σ.snd i)

lemma subset {i : Fin σ.pairs.length} : σ.fst i ∈ Set.Icc a b := by
  have hx : σ.fst i ∈ σ := by simpa only [fst, pairs, List.pairs, get_zip] using List.get_mem ..
  rcases σ with ⟨l, h1, h2, h4, h5⟩
  exact ⟨h4 ▸ h2.head_le hx, h5 ▸ h2.le_last hx⟩

noncomputable def mesh (σ : subdivision a b) : ℝ :=
  if h : a < b
  then (σ.pairs.map (λ p => |p.2 - p.1|)).maximum_of_length_pos (by simpa using pos_length_pairs h)
  else 0

noncomputable def mesh' (σ : subdivision a b) : ℝ :=
  if a < b
  then ⨆ i, |σ.snd i - σ.fst i|
  else 0

@[simp] lemma maximum_replicate : maximum (replicate (n + 1) a) = a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [replicate_succ, maximum_cons, ih, max_self]

@[simp] lemma regular_mesh (hab : a < b) : (regular hab.le n).mesh = (b - a) / (n + 1) := by
  have : 0 ≤ b - a := by linarith
  have : 0 ≤ (b - a) / (↑n + 1) := by positivity
  simp only [mesh, hab, pairs, regular, List.regular, prog.sub this, dite_true]
  simp only [maximum_of_length_pos, maximum_replicate, WithBot.unbot_coe]

lemma le_mesh (hab : a < b) (hp : p ∈ σ.pairs) : |p.2 - p.1| ≤ σ.mesh := by
  have h1 : |p.2 - p.1| ∈ σ.pairs.map (λ p => |p.2 - p.1|) :=
    List.mem_map_of_mem (λ p : ℝ × ℝ => |p.2 - p.1|) hp
  have h2 : 0 < (List.map (fun p => |p.snd - p.fst|) (pairs σ)).length := by
    simpa using pos_length_pairs hab
  simp only [mesh, hab]
  simpa only [← coe_maximum_of_length_pos h2, WithBot.coe_le_coe] using le_maximum_of_mem' h1

lemma le_mesh' (hab : a < b) : |σ.snd i - σ.fst i| ≤ σ.mesh' := by
  sorry

def adapted (σ : subdivision a b) (S : ι → Set ℝ) : Prop := ∀ k, ∃ i, σ.Icc k ⊆ S i

lemma adapted_of_mesh_lt (hab : a < b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ ε > 0, ∀ σ : subdivision a b, σ.mesh < ε → adapted σ S := by
  obtain ⟨ε, hε, l1⟩ := lebesgue_number_lemma_of_metric isCompact_Icc h1 h2
  refine ⟨ε, hε, λ σ hσ j => ?_⟩
  set p := σ.pairs.get j
  have hp : p ∈ σ.pairs := get_mem ..
  have : Set.OrdConnected (ball (σ.fst j) ε) := (convex_ball ..).ordConnected
  obtain ⟨i, hi⟩ := l1 p.1 σ.subset
  exact ⟨i, subset_trans (Set.Icc_subset _ (mem_ball_self hε) ((le_mesh hab hp).trans_lt hσ)) hi⟩

lemma exists_div_lt {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) : ∃ n : ℕ, a / (n + 1) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε ha)
  use n
  convert (@strictMono_mul_left_of_pos ℝ _ a ha).lt_iff_lt.2 hn using 1 <;> field_simp; ring

lemma exists_adapted (hab : a < b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ σ : subdivision a b, adapted σ S := by
  obtain ⟨ε, hε, h⟩ := adapted_of_mesh_lt hab h1 h2
  obtain ⟨n, hn⟩ := exists_div_lt (sub_pos_of_lt hab) hε
  have : (regular hab.le n).mesh = (b - a) / (n + 1) := regular_mesh hab
  exact ⟨regular hab.le n, h _ (by linarith)⟩

noncomputable def RS [AddCommMonoid E] [SMul ℝ E] (σ : subdivision a b) (f : ℝ → E) : E :=
  ∑ i, (σ.snd i - σ.fst i) • f (σ.fst i)

end subdivision

def ContDiffAlong (f : ℝ → ℝ) (σ : subdivision a b) : Prop := ∀ i, ContDiffOn ℝ 1 f (σ.Icc i)

def PiecewiseContDiff (f : ℝ → ℝ) (a b : ℝ) : Prop := ∃ σ : subdivision a b, ContDiffAlong f σ

section pintegral

noncomputable def sumSub (σ : subdivision a b) (F : Fin σ.pairs.length -> ℝ -> ℂ) : ℂ :=
  ∑ i, (F i (σ.pairs.get i).2 - F i (σ.pairs.get i).1)

noncomputable def sumSubAlong (σ : subdivision a b) (F : Fin σ.pairs.length → ℂ → ℂ)
    (γ : ℝ → ℂ) : ℂ :=
  sumSub σ (λ i => F i ∘ γ)

variable {f : ℂ → ℂ} {U : Set ℂ}

noncomputable def pintegral (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc 0 1) ⊆ U)
    (hγ : Continuous γ) (IsLocDeriv : ∀ z ∈ U, ∃ ε > 0, ∃ F : ℂ → ℂ, EqOn (deriv F) f (ball z ε))
    : ℂ := by
  choose! ε hε F _ using IsLocDeriv
  set S : Set.Icc (0 : ℝ) 1 → Set ℝ := λ t => γ ⁻¹' (ball (γ t) (ε (γ t)))
  have l1 : ∀ i, ↑i ∈ S i := λ ⟨t, ht⟩ => by
    exact mem_preimage.2 (mem_ball_self (hε _ (h2 (mem_image_of_mem _ ht))))
  have l2 : Set.Icc 0 1 ⊆ ⋃ i, S i := λ t ht =>
    Set.mem_iUnion.2 ⟨⟨t, ht⟩, l1 ⟨t, ht⟩⟩
  choose σ hσ using subdivision.exists_adapted (by linarith) (λ i => isOpen_ball.preimage hγ) l2
  choose I _ using hσ
  exact sumSubAlong σ (λ i => F (γ (I i))) γ

end pintegral