import Mathlib.Topology.Covering
import Mathlib.Topology.PathConnected

set_option autoImplicit false
set_option pp.proofs.withType false

open Set Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : Icc (0:ℝ) 1 → X}
  {A : E} {s t : Icc (0:ℝ) 1}

instance : PreconnectedSpace (Icc (0:ℝ) 1) :=
  isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc

def Icct (t : Icc (0:ℝ) 1) : Set (Icc (0:ℝ) 1) := { s | s ≤ t }

lemma Icct_subset {s t : Icc 0 1} (h : s ∈ Icct t) : Icct s ⊆ Icct t :=
  λ s' (hs' : s' ≤ s) => hs'.trans h

@[simp] lemma Icct_one : Icct 1 = univ := by ext x ; simpa [Icct] using x.prop.2

def goods (f : E → X) (γ : Icc (0:ℝ) 1 → X) (A : E) : Set (Icc (0:ℝ) 1) :=
  { t | ∃ Γ : Icc (0:ℝ) 1 → E, ContinuousOn Γ (Icct t) ∧ Γ 0 = A ∧ ∀ s ≤ t, f (Γ s) = γ s }

lemma goods_nonempty (hγ : γ 0 = f A) : Set.Nonempty (goods f γ A) := by
  refine ⟨0, λ _ => A, continuousOn_const, rfl, ?_⟩
  rintro ⟨s, h1, h2⟩ (h3 : s ≤ 0)
  simp [le_antisymm h3 h1, hγ]

lemma goods_directed {t : Icc 0 1} (ht : t ∈ goods f γ A) : Icct t ⊆ goods f γ A := by
  obtain ⟨Γ, h1, h2, h3⟩ := ht
  intro s hs
  refine ⟨Γ, ?_, h2, ?_⟩
  · exact ContinuousOn.mono h1 <| Icct_subset hs
  · intro s' hs' ; exact h3 s' (hs'.trans hs)

lemma goods_extendable (hf : IsCoveringMap f) (hγ : Continuous γ) (ht : t ∈ goods f γ A)
    (ht' : t < 1) (hh : 0 < t) : ∃ t' : Icc 0 1, t < t' ∧ t' ∈ goods f γ A := by
  obtain ⟨Γ, h1, h2, h3⟩ := ht
  obtain ⟨_, T, l5⟩ := hf (γ t)
  have l1 : f (Γ t) = γ t := h3 t le_rfl
  have l2 : T.baseSet ∈ 𝓝 (γ t) := T.open_baseSet.mem_nhds l5
  have l4 : γ ⁻¹' T.baseSet ∈ 𝓝 t := ContinuousAt.preimage_mem_nhds hγ.continuousAt l2
  obtain ⟨⟨t1,t2⟩, ⟨hi1, hi2⟩, hi3⟩ := nhds_basis_Ioo' ⟨_, hh⟩ ⟨_, ht'⟩ |>.mem_iff.1 l4
  have l10 : Set.Nonempty (Ioo t t2) := nonempty_Ioo.2 hi2
  obtain ⟨t', hi4, hi5⟩ := l10
  let δ (s : Icc (0:ℝ) 1) : E := T.invFun (γ s, (T (Γ t)).2)
  let Δ (s : Icc (0:ℝ) 1) : E := if s ≤ t then Γ s else δ s
  refine ⟨t', hi4, Δ, ?_, ?_, ?_⟩
  · apply ContinuousOn.if
    · intro a ⟨ha1, ha2⟩
      have : frontier {a | a ≤ t} ⊆ {t} := frontier_le_subset_eq continuous_id continuous_const
      have : a = t := by simpa using this ha2
      subst a
      have k1 : Γ t ∈ T.source := by simpa [T.source_eq, l1] using mem_of_mem_nhds l4
      have k2 : (T (Γ t)).1 = f (Γ t) := T.proj_toFun _ k1
      have k3 : T.invFun (T (Γ t)) = Γ t := T.left_inv' k1
      simp_rw [← l1, ← k2, Prod.eta, k3]
    · have : closure {a | a ≤ t} = {a | a ≤ t} := closure_le_eq continuous_id continuous_const
      apply h1.mono
      simp [Icct, this]
    · have : ContinuousOn δ (γ ⁻¹' T.baseSet) := by
        apply T.continuous_invFun.comp
        · exact Continuous.continuousOn (by simp [hγ, continuous_const])
        · intro u hu ; simpa [T.target_eq] using hu
      apply this.mono
      refine subset_trans ?_ hi3
      have : closure {a | t < a} ⊆ {a | t ≤ a} := by
        apply closure_lt_subset_le continuous_const continuous_id
      simp [this, Icct]
      intro u ⟨e1, e2⟩
      specialize this e2
      simp at *
      constructor
      · exact hi1.trans_le this
      · exact e1.trans_lt hi5
  · have : 0 ≤ t := t.2.1 ; simp [this, h2]
  · intro v hv
    by_cases l6 : v ≤ t
    · simp [l6, h3]
    · simp only [l6, ite_false]
      have l23 : γ v ∈ T.baseSet := by
        apply hi3
        constructor
        · simp at l6
          trans t
          exact hi1
          exact l6
        · apply hv.trans_lt hi5
      rw [← T.proj_toFun]
      · have l7 : (γ v, (T (Γ t)).snd) ∈ T.target := by simp [T.target_eq, l23]
        have := T.right_inv' l7
        simp at this ⊢
        simp [this]
      · apply T.map_target'
        simp [T.target_eq, l23]

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
