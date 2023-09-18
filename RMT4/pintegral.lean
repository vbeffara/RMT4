import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic

open List BigOperators Metric Set

lemma exists_div_lt {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) : ∃ n : ℕ, a / (n + 1) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε ha)
  use n
  convert (@strictMono_mul_left_of_pos ℝ _ a ha).lt_iff_lt.2 hn using 1 <;> field_simp; ring

structure subdivision (a b : ℝ) where
  n : ℕ
  toFun : Fin (n + 2) → ℝ
  mono : Monotone toFun
  first : toFun ⟨0, Nat.succ_pos (n+1)⟩ = a
  last : toFun (Fin.last (n+1)) = b

namespace subdivision

variable {a b : ℝ} {σ : subdivision a b}

instance : CoeFun (subdivision a b) (λ σ => Fin (σ.n + 2) → ℝ) := ⟨toFun⟩

def zero (σ : subdivision a b) : Fin (σ.n + 2) := ⟨0, Nat.succ_pos (σ.n + 1)⟩

def Icc (σ : subdivision a b) (i : Fin (σ.n + 1)) : Set ℝ := Set.Icc (σ i.castSucc) (σ i.succ)

noncomputable def mesh (σ : subdivision a b) : ℝ :=
  ⨆ i : Fin (σ.n + 1), |σ i.succ - σ i.castSucc|

lemma le_mesh {i : Fin (σ.n + 1)} : |σ i.succ - σ i.castSucc| ≤ σ.mesh :=
  le_ciSup (f := λ i => |σ (Fin.succ i) - σ (Fin.castSucc i)|) (finite_range _).bddAbove _

lemma le (σ : subdivision a b) : a ≤ b := by
  convert ← σ.mono (zero σ).le_last
  · exact σ.first
  · exact σ.last

lemma subset {σ : subdivision a b} {i} : σ i ∈ Set.Icc a b := by
  refine ⟨?_, ?_⟩
  · simp only [← σ.first]
    apply σ.mono
    simp only [Fin.mk_zero, Fin.zero_le]
  · simp only [← σ.last]
    apply σ.mono
    apply Fin.le_last

noncomputable def regular (hab : a ≤ b) (n : ℕ) : subdivision a b where
  n := n
  toFun := λ i => a + i * (b - a) / (n + 1)
  mono := by
    intro i j ij
    dsimp only
    gcongr
    · linarith
    · norm_cast
  first := by simp
  last := by field_simp; ring

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
  obtain ⟨i, hi⟩ := l1 (σ j.castSucc) σ.subset
  have : Set.OrdConnected (ball (σ j.castSucc) ε) := (convex_ball ..).ordConnected
  exact ⟨i, subset_trans (Set.Icc_subset _ (mem_ball_self hε) (le_mesh.trans_lt hσ)) hi⟩

lemma exists_adapted (hab : a < b) (h1 : ∀ i, IsOpen (S i)) (h2 : Set.Icc a b ⊆ ⋃ i, S i) :
    ∃ σ : subdivision a b, adapted σ S := by
  obtain ⟨ε, hε, h⟩ := adapted_of_mesh_lt h1 h2
  obtain ⟨n, hn⟩ := exists_div_lt (sub_pos_of_lt hab) hε
  have : (regular hab.le n).mesh = (b - a) / (n + 1) := regular_mesh hab
  exact ⟨regular hab.le n, h _ (by linarith)⟩

end subdivision

noncomputable def sumSub (σ : subdivision a b) (F : Fin (σ.n + 1) -> ℝ -> ℂ) : ℂ :=
  ∑ i, (F i (σ i.castSucc) - F i (σ i.succ))

noncomputable def sumSubAlong (σ : subdivision a b) (F : Fin (σ.n + 1) → ℂ → ℂ)
    (γ : ℝ → ℂ) : ℂ :=
  sumSub σ (λ i => F i ∘ γ)

noncomputable def pintegral (hab : a < b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : (γ '' Set.Icc a b) ⊆ U)
    (hγ : Continuous γ) (IsLocDeriv : ∀ z ∈ U, ∃ ε > 0, ∃ F : ℂ → ℂ, EqOn (deriv F) f (ball z ε))
    : ℂ := by
  choose! ε hε F _ using IsLocDeriv
  set S : Set.Icc a b → Set ℝ := λ t => γ ⁻¹' (ball (γ t) (ε (γ t)))
  have l1 : ∀ i, ↑i ∈ S i := λ ⟨t, ht⟩ => by
    exact mem_preimage.2 (mem_ball_self (hε _ (h2 (mem_image_of_mem _ ht))))
  have l2 : Set.Icc a b ⊆ ⋃ i, S i := λ t ht =>
    Set.mem_iUnion.2 ⟨⟨t, ht⟩, l1 ⟨t, ht⟩⟩
  choose σ hσ using subdivision.exists_adapted hab (λ i => isOpen_ball.preimage hγ) l2
  choose I _ using hσ
  exact sumSubAlong σ (λ i => F (γ (I i))) γ
