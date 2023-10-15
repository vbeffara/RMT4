import Mathlib.Topology.Covering
import Mathlib.Topology.PathConnected

set_option pp.proofs.withType false

open Set

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : Icc (0:ℝ) 1 → X}
  {A : E}

instance : PreconnectedSpace (Icc (0:ℝ) 1) :=
  isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc

def Icct (t : Icc (0:ℝ) 1) : Set (Icc (0:ℝ) 1) := { s | s ≤ t }

@[simp] lemma Icct_one : Icct 1 = univ := by ext x ; simpa [Icct] using x.prop.2

def goods (f : E → X) (γ : Icc (0:ℝ) 1 → X) (A : E) : Set (Icc (0:ℝ) 1) :=
  { t | ∃ Γ : Icc (0:ℝ) 1 → E, ContinuousOn Γ (Icct t) ∧ Γ 0 = A ∧ ∀ s ≤ t, f (Γ s) = γ s }

lemma goods_nonempty (hγ : γ 0 = f A): Set.Nonempty (goods f γ A) := by
  refine ⟨0, λ _ => A, continuousOn_const, rfl, ?_⟩
  rintro ⟨s, h1, h2⟩ (h3 : s ≤ 0)
  simp [le_antisymm h3 h1, hγ]

lemma goods_open (hf : IsCoveringMap f) : IsOpen (goods f γ A) := by
  rw [isOpen_iff_mem_nhds]
  intro t ⟨Γ, h1, h2, h3⟩
  let B := Γ t
  let b := γ t
  have l1 : f B = b := h3 t le_rfl
  let T := (hf b).toTrivialization
  let z := T B
  let δ (s : Icc (0:ℝ) 1) : E := T.invFun (γ s, (T B).2)
  let Δ (s : Icc (0:ℝ) 1) : E := if s ≤ t then Γ s else δ s
  have l2 : ContinuousOn Δ (Icct t ∪ γ ⁻¹' T.baseSet) := by
    apply ContinuousOn.if
    · rintro a ⟨ha1, ha2⟩
      have := @frontier_le_subset_eq (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) _ _ _ id (λ _ => t) _
        continuous_id continuous_const
      have := this ha2
      simp at this
      rw [this]
      sorry
    · sorry
    · sorry
  sorry

theorem lift (hf : IsCoveringMap f) (hγ : Continuous γ) (hγ0 : γ 0 = f A) :
    ∃ Γ : Icc (0:ℝ) 1 → E, Continuous Γ ∧ Γ 0 = A ∧ ∀ t, f (Γ t) = γ t := by
  let s : Set (Icc (0:ℝ) 1) := goods f γ A
  suffices : goods f γ A  = univ
  · obtain ⟨Γ, h1, h2, h3⟩ := this.symm ▸ mem_univ 1
    refine ⟨Γ, ?_, h2, λ s => h3 s s.2.2⟩
    simpa [continuous_iff_continuousOn_univ] using h1
  have l1 : Set.Nonempty s := goods_nonempty hγ0
  suffices : IsClopen s
  · exact (isClopen_iff.1 this).resolve_left <| Nonempty.ne_empty l1
  constructor
  · exact goods_open hf
  · sorry
