import Mathlib.Topology.Covering
import Mathlib.Topology.PathConnected

set_option autoImplicit false
set_option pp.proofs.withType false

open Set Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : Icc (0:ℝ) 1 → X}
  {A : E} {s t t₁ t₂ : Icc (0:ℝ) 1}

instance : PreconnectedSpace (Icc (0:ℝ) 1) :=
  isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc

def Icct (t : Icc (0:ℝ) 1) : Set (Icc (0:ℝ) 1) := { s | s ≤ t }

lemma Icct_subset {s t : Icc 0 1} (h : s ∈ Icct t) : Icct s ⊆ Icct t :=
  λ s' (hs' : s' ≤ s) => hs'.trans h

@[simp] lemma Icct_one : Icct 1 = univ := by ext x ; simpa [Icct] using x.prop.2

def good (f : E → X) (γ : Icc (0:ℝ) 1 → X) (A : E) (t : Icc (0:ℝ) 1) : Prop :=
  ∃ Γ : Icc (0:ℝ) 1 → E, ContinuousOn Γ (Icct t) ∧ Γ 0 = A ∧ ∀ s ≤ t, f (Γ s) = γ s

lemma good_zero (hγ : γ 0 = f A) : good f γ A 0 := by
  refine ⟨λ _ => A, continuousOn_const, rfl, ?_⟩
  rintro ⟨s, h1, h2⟩ (h3 : s ≤ 0)
  simp [le_antisymm h3 h1, hγ]

lemma good_mono (h2 : good f γ A t₂) (h12 : t₁ ≤ t₂) : good f γ A t₁ := by
  obtain ⟨Γ, h1, h2, h3⟩ := h2
  exact ⟨Γ, ContinuousOn.mono h1 <| Icct_subset h12, h2, λ s' hs' => h3 s' (hs'.trans h12)⟩

lemma good_extend (h1 : good f γ A t₁) {T : Trivialization (f ⁻¹' {γ t}) f}
    (h : MapsTo γ (Icc t₁ t₂) T.baseSet) (hγ : Continuous γ) : good f γ A t₂ := by
  wlog h12 : t₁ < t₂ ; exact good_mono h1 <| not_lt.mp h12
  obtain ⟨Γ, h1, h2, h3⟩ := h1
  have l1 : f (Γ t₁) = γ t₁ := h3 t₁ le_rfl
  have l5 : γ t₁ ∈ T.baseSet  := h ⟨le_rfl, h12.le⟩
  have l2 : T.baseSet ∈ 𝓝 (γ t₁) := T.open_baseSet.mem_nhds l5
  have l4 : γ ⁻¹' T.baseSet ∈ 𝓝 t₁ := ContinuousAt.preimage_mem_nhds hγ.continuousAt l2
  let δ (s : Icc (0:ℝ) 1) : E := T.invFun (γ s, (T (Γ t₁)).2)
  let Δ (s : Icc (0:ℝ) 1) : E := if s ≤ t₁ then Γ s else δ s
  refine ⟨Δ, ?_, ?_, ?_⟩
  · apply ContinuousOn.if
    · intro a ⟨ha1, ha2⟩
      have : frontier {a | a ≤ t₁} ⊆ {t₁} := frontier_le_subset_eq continuous_id continuous_const
      have : a = t₁ := by simpa using this ha2
      subst a
      have k1 : Γ t₁ ∈ T.source := by simpa [T.source_eq, l1] using mem_of_mem_nhds l4
      have k2 : (T (Γ t₁)).1 = f (Γ t₁) := T.proj_toFun _ k1
      have k3 : T.invFun (T (Γ t₁)) = Γ t₁ := T.left_inv' k1
      simp_rw [← l1, ← k2, Prod.eta, k3]
    · have : closure {a | a ≤ t₁} = {a | a ≤ t₁} := closure_le_eq continuous_id continuous_const
      apply h1.mono
      simp [Icct, this]
    · have : ContinuousOn δ (γ ⁻¹' T.baseSet) := by
        apply T.continuous_invFun.comp
        · exact Continuous.continuousOn (by simp [hγ, continuous_const])
        · intro u hu ; simpa [T.target_eq] using hu
      apply this.mono
      have : closure {a | t₁ < a} ⊆ {a | t₁ ≤ a} := by
        apply closure_lt_subset_le continuous_const continuous_id
      rintro v ⟨hv1, hv2⟩
      simp only [not_le] at hv2
      exact h ⟨this hv2, hv1⟩
  · have : 0 ≤ t₁ := t₁.2.1 ; simp [this, h2]
  · intro v hv
    by_cases l6 : v ≤ t₁
    · simp [l6, h3]
    · simp only [l6, ite_false]
      have l23 : γ v ∈ T.baseSet := h ⟨not_le.1 l6 |>.le, hv⟩
      have : LocalEquiv.invFun T.toLocalEquiv (γ v, (T (Γ t₁)).snd) ∈ T.source := by
        apply T.map_target'
        simp [T.target_eq, l23]
      rw [← T.proj_toFun _ this]
      have l7 : (γ v, (T (Γ t₁)).snd) ∈ T.target := by simp [T.target_eq, l23]
      have := T.right_inv' l7
      simp at this ⊢
      simp [this]

def goods (f : E → X) (γ : Icc (0:ℝ) 1 → X) (A : E) : Set (Icc (0:ℝ) 1) := { t | good f γ A t }

example (hf : IsCoveringMap f) (hγ : Continuous γ) (hγ0 : γ 0 = f A) : goods f γ A ∈ 𝓝 0 := by
  obtain ⟨_, T, h⟩ := hf (f A)
  have l1 : T.baseSet ∈ 𝓝 (γ 0) := hγ0.symm ▸ T.open_baseSet.mem_nhds h
  have l2 : γ ⁻¹' T.baseSet ∈ 𝓝 0 := ContinuousAt.preimage_mem_nhds hγ.continuousAt l1
  rw [Metric.mem_nhds_iff] at l2
  obtain ⟨ε, hε, h⟩ := l2
  simp only [nhds_induced, Icc.coe_zero, Filter.mem_comap] at l2

  sorry

lemma goods_extendable (hf : IsCoveringMap f) (hγ : Continuous γ) (ht : t ∈ goods f γ A)
    (ht' : t < 1) (hh : 0 < t) : ∃ t' : Icc 0 1, t < t' ∧ t' ∈ goods f γ A := by
  obtain ⟨_, T, l5⟩ := hf (γ t)
  have l2 : T.baseSet ∈ 𝓝 (γ t) := T.open_baseSet.mem_nhds l5
  have l4 : γ ⁻¹' T.baseSet ∈ 𝓝 t := ContinuousAt.preimage_mem_nhds hγ.continuousAt l2
  obtain ⟨⟨t1, t2⟩, ⟨hi1, hi2⟩, hi3⟩ := nhds_basis_Ioo' ⟨_, hh⟩ ⟨_, ht'⟩ |>.mem_iff.1 l4
  obtain ⟨t', hi4, hi5⟩ := nonempty_Ioo.2 hi2
  have {{v}} (hv : v ∈ Icc t t') : γ v ∈ T.baseSet := hi3 ⟨hi1.trans_le hv.1, hv.2.trans_lt hi5⟩
  refine ⟨t', hi4, good_extend ht this hγ⟩

lemma goods_open (hf : IsCoveringMap f) : IsOpen (goods f γ A) := by
  rw [isOpen_iff_mem_nhds]
  sorry

theorem lift (hf : IsCoveringMap f) (hγ : Continuous γ) (hγ0 : γ 0 = f A) :
    ∃ Γ : Icc (0:ℝ) 1 → E, Continuous Γ ∧ Γ 0 = A ∧ ∀ t, f (Γ t) = γ t := by
  let s : Set (Icc (0:ℝ) 1) := goods f γ A
  suffices : goods f γ A  = univ
  · obtain ⟨Γ, h1, h2, h3⟩ := this.symm ▸ mem_univ 1
    refine ⟨Γ, ?_, h2, λ s => h3 s s.2.2⟩
    simpa [continuous_iff_continuousOn_univ] using h1
  have l1 : Set.Nonempty s := ⟨0, good_zero hγ0⟩
  suffices : IsClopen s
  · exact (isClopen_iff.1 this).resolve_left <| Nonempty.ne_empty l1
  constructor
  · exact goods_open hf
  · sorry
