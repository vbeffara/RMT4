import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Covering

set_option autoImplicit false
set_option pp.proofs.withType false

open Set Topology Metric unitInterval

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : I → X} {A : E}
  {s t t₁ t₂ : I}

lemma Icct_subset {s t : I} (h : s ∈ Iic t) : Iic s ⊆ Iic t := Iic_subset_Iic.mpr h

@[simp] lemma Icct_one : Iic (1 : I) = univ := by ext x ; simpa [Iic] using x.prop.2

def good (f : E → X) (γ : I → X) (A : E) (t : I) : Prop :=
  ∃ Γ : I → E, ContinuousOn Γ (Iic t) ∧ Γ 0 = A ∧ ∀ s ≤ t, f (Γ s) = γ s

lemma good_zero (hγ : γ 0 = f A) : good f γ A 0 := by
  refine ⟨λ _ => A, continuousOn_const, rfl, ?_⟩
  rintro ⟨s, h1, h2⟩ (h3 : s ≤ 0)
  simp [le_antisymm h3 h1, hγ]

lemma good_mono (h2 : good f γ A t₂) (h12 : t₁ ≤ t₂) : good f γ A t₁ := by
  obtain ⟨Γ, h1, h2, h3⟩ := h2
  refine ⟨Γ, ContinuousOn.mono h1 <| Icct_subset h12, h2, λ s' hs' => h3 s' (hs'.trans h12)⟩

lemma good_extend (h1 : good f γ A t₁) {T : Trivialization (f ⁻¹' {γ t}) f}
    (h : MapsTo γ (uIcc t₁ t₂) T.baseSet) (hγ : Continuous γ) : good f γ A t₂ := by
  wlog h12 : t₁ < t₂ ; exact good_mono h1 <| not_lt.mp h12
  obtain ⟨Γ, h1, h2, h3⟩ := h1
  have l1 : f (Γ t₁) = γ t₁ := h3 t₁ le_rfl
  have l5 : γ t₁ ∈ T.baseSet  := h ⟨inf_le_left, le_sup_left⟩
  have l2 : T.baseSet ∈ 𝓝 (γ t₁) := T.open_baseSet.mem_nhds l5
  have l4 : γ ⁻¹' T.baseSet ∈ 𝓝 t₁ := ContinuousAt.preimage_mem_nhds hγ.continuousAt l2
  let δ (s : I) : E := T.invFun (γ s, (T (Γ t₁)).2)
  let Δ (s : I) : E := if s ≤ t₁ then Γ s else δ s
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
      simp [Iic, this]
    · have : ContinuousOn δ (γ ⁻¹' T.baseSet) := by
        apply T.continuous_invFun.comp
        · exact Continuous.continuousOn (by simp [hγ, continuous_const])
        · intro u hu ; simpa [T.target_eq] using hu
      apply this.mono
      have : closure {a | t₁ < a} ⊆ {a | t₁ ≤ a} := by
        apply closure_lt_subset_le continuous_const continuous_id
      rintro v ⟨hv1, hv2⟩
      simp only [not_le] at hv2
      refine h ⟨inf_le_left.trans <| this hv2, (show v ≤ t₂ from hv1).trans le_sup_right⟩
  · have : 0 ≤ t₁ := t₁.2.1 ; simp [this, h2]
  · intro v hv
    by_cases l6 : v ≤ t₁
    · simp [l6, h3]
    · simp only [l6, ite_false]
      have l23 : γ v ∈ T.baseSet :=
        h ⟨inf_le_left.trans <| not_le.1 l6 |>.le, hv.trans le_sup_right⟩
      have : LocalEquiv.invFun T.toLocalEquiv (γ v, (T (Γ t₁)).snd) ∈ T.source := by
        apply T.map_target'
        simp [T.target_eq, l23]
      rw [← T.proj_toFun _ this]
      have l7 : (γ v, (T (Γ t₁)).snd) ∈ T.target := by simp [T.target_eq, l23]
      have := T.right_inv' l7
      simp at this ⊢
      simp [this]

def goods (f : E → X) (γ : I → X) (A : E) : Set I := { t | good f γ A t }

lemma good_nhds (hf : IsCoveringMap f) (hγ : Continuous γ) (h : good f γ A t) :
    goods f γ A ∈ 𝓝 t := by
  obtain ⟨_, T, h4⟩ := hf (γ t)
  have l1 : T.baseSet ∈ 𝓝 (γ t) := T.open_baseSet.mem_nhds h4
  have l2 : γ ⁻¹' T.baseSet ∈ 𝓝 t := ContinuousAt.preimage_mem_nhds hγ.continuousAt l1
  rw [Metric.mem_nhds_iff] at l2 ⊢
  obtain ⟨ε, hε, l3⟩ := l2
  refine ⟨ε, hε, ?_⟩
  intro u hu
  have l4 : uIcc t u ⊆ ball t ε := by
    suffices uIcc t.1 u.1 ⊆ ball t.1 ε by intro v ; apply this
    simpa only [segment_eq_uIcc] using (convex_ball t.1 ε).segment_subset (mem_ball_self hε) hu
  have l5 : MapsTo γ (uIcc t u) T.baseSet := λ v hv => l3 (l4 hv)
  exact good_extend h l5 hγ

lemma good_compl_nhds (hf : IsCoveringMap f) (hγ : Continuous γ) (h : ¬ good f γ A t) :
    (goods f γ A)ᶜ ∈ 𝓝 t := by
  obtain ⟨_, T, h4⟩ := hf (γ t)
  have l1 : T.baseSet ∈ 𝓝 (γ t) := T.open_baseSet.mem_nhds h4
  have l2 : γ ⁻¹' T.baseSet ∈ 𝓝 t := ContinuousAt.preimage_mem_nhds hγ.continuousAt l1
  rw [Metric.mem_nhds_iff] at l2 ⊢
  obtain ⟨ε, hε, l3⟩ := l2
  refine ⟨ε, hε, ?_⟩
  intro u hu
  have l4 : uIcc t u ⊆ ball t ε := by
    suffices uIcc t.1 u.1 ⊆ ball t.1 ε by intro v ; apply this
    simpa only [segment_eq_uIcc] using (convex_ball t.1 ε).segment_subset (mem_ball_self hε) hu
  have l5 : MapsTo γ (uIcc t u) T.baseSet := λ v hv => l3 (l4 hv)
  rw [uIcc_comm] at l5
  simp
  intro h'
  exact h <| @good_extend E X _ _ f γ A t u t h' T l5 hγ

lemma goods_open (hf : IsCoveringMap f) (hγ : Continuous γ) : IsOpen (goods f γ A) := by
  simpa only [isOpen_iff_mem_nhds] using λ a ha => good_nhds hf hγ ha

lemma goods_compl_open (hf : IsCoveringMap f) (hγ : Continuous γ) : IsOpen (goods f γ A)ᶜ := by
  simpa only [isOpen_iff_mem_nhds] using λ a ha => good_compl_nhds hf hγ ha

theorem lift (hf : IsCoveringMap f) (hγ : Continuous γ) (hγ0 : γ 0 = f A) :
    ∃ Γ : I → E, Continuous Γ ∧ Γ 0 = A ∧ ∀ t, f (Γ t) = γ t := by
  let s : Set I := goods f γ A
  suffices goods f γ A = univ by
    obtain ⟨Γ, h1, h2, h3⟩ := this.symm ▸ mem_univ 1
    refine ⟨Γ, ?_, h2, λ s => h3 s s.2.2⟩
    simpa [continuous_iff_continuousOn_univ] using h1
  have l1 : Set.Nonempty s := ⟨0, good_zero hγ0⟩
  suffices IsClopen s from (isClopen_iff.1 this).resolve_left <| Nonempty.ne_empty l1
  constructor
  · exact goods_open hf hγ
  · exact ⟨goods_compl_open hf hγ⟩
