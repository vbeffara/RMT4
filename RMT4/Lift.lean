import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Covering

set_option autoImplicit false
set_option pp.proofs.withType false

open Set Topology Metric unitInterval

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : C(I, X)} {A : E}
  {s t t₁ t₂ : I}

instance : Top I := ⟨1⟩
instance : OrderTop I := by refine ⟨λ _ => le_one'⟩

def good (f : E → X) (γ : C(I, X)) (A : E) (t : I) : Prop :=
  ∃ Γ : I → E, ContinuousOn Γ (Iic t) ∧ Γ 0 = A ∧ ∀ s ≤ t, f (Γ s) = γ s

lemma good_zero (hγ : γ 0 = f A) : good f γ A 0 := by
  refine ⟨λ _ => A, continuousOn_const, rfl, ?_⟩
  rintro ⟨s, h1, h2⟩ (h3 : s ≤ 0)
  simp [le_antisymm h3 h1, hγ]

lemma good_mono (h2 : good f γ A t₂) (h12 : t₁ ≤ t₂) : good f γ A t₁ := by
  obtain ⟨Γ, h1, h2, h3⟩ := h2
  refine ⟨Γ, ContinuousOn.mono h1 <| Iic_subset_Iic.mpr h12, h2, λ s' hs' => h3 s' (hs'.trans h12)⟩

lemma good_extend (h1 : good f γ A t₁) {T : Trivialization (f ⁻¹' {γ t}) f}
    (h : MapsTo γ (uIcc t₁ t₂) T.baseSet) : good f γ A t₂ := by
  obtain ⟨Γ, h1, h2, h3⟩ := h1
  have l2 : T.baseSet ∈ 𝓝 (γ t₁) := T.open_baseSet.mem_nhds <| h ⟨inf_le_left, le_sup_left⟩
  have l3 : γ ⁻¹' T.baseSet ∈ 𝓝 t₁ := γ.continuous_toFun.continuousAt.preimage_mem_nhds l2
  let δ (s : I) : E := T.invFun (γ s, (T (Γ t₁)).2)
  let Δ (s : I) : E := if s ≤ t₁ then Γ s else δ s
  refine ⟨Δ, ?_, ?_, ?_⟩
  · apply ContinuousOn.if
    · have k1 : Γ t₁ ∈ T.source := by simpa [T.source_eq, h3 t₁ le_rfl] using mem_of_mem_nhds l3
      have k2 : (T (Γ t₁)).1 = f (Γ t₁) := T.proj_toFun _ k1
      have k3 : T.invFun (T (Γ t₁)) = Γ t₁ := T.left_inv' k1
      intro a ha
      have k4 : a = t₁ := by simpa using (frontier_le_subset_eq continuous_id continuous_const) ha.2
      simp_rw [k4, ← h3 t₁ le_rfl, ← k2, Prod.eta, k3]
    · refine h1.mono <| (inter_subset_right _ _).trans (?_ : closure (Iic t₁) ⊆ Iic t₁)
      simpa only [closure_Iic] using subset_rfl
    · have : ContinuousOn δ (γ ⁻¹' T.baseSet) := by
        apply T.continuous_invFun.comp
        · apply Continuous.continuousOn
          simp only [continuous_prod_mk, continuous_const, and_true]
          exact γ.continuous_toFun
        · intro u hu ; simpa [T.target_eq] using hu
      apply this.mono
      rintro v ⟨hv1, hv2⟩
      simp only [not_le] at hv2
      have : closure (Ioi t₁) ⊆ Ici t₁ := closure_lt_subset_le continuous_const continuous_id
      refine h ⟨inf_le_left.trans <| this hv2, (show v ≤ t₂ from hv1).trans le_sup_right⟩
  · simp [show 0 ≤ t₁ from t₁.2.1, h2]
  · intro v hv
    by_cases l6 : v ≤ t₁
    · simp only [LocalEquiv.invFun_as_coe, LocalHomeomorph.coe_coe_symm, l6, ite_true, h3]
    · simp only [l6, ite_false]
      have : γ v ∈ T.baseSet := h ⟨inf_le_left.trans <| not_le.1 l6 |>.le, hv.trans le_sup_right⟩
      have l7 : T.invFun (γ v, (T (Γ t₁)).snd) ∈ T.source :=
        T.map_target' <| by simp only [T.target_eq, mem_prod, this, mem_univ, and_self]
      rw [← T.proj_toFun _ l7]
      have : T (T.invFun (γ v, (T (Γ t₁)).snd)) = (γ v, (T (Γ t₁)).snd) :=
        T.right_inv' <| by simp only [T.target_eq, mem_prod, this, mem_univ, and_self]
      simp only [LocalEquiv.invFun_as_coe, LocalHomeomorph.coe_coe_symm] at this
      simp [this]

def goods (f : E → X) (γ : C(I, X)) (A : E) : Set I := { t | good f γ A t }

lemma good_nhds (hf : IsCoveringMap f) (h : good f γ A t) :
    goods f γ A ∈ 𝓝 t := by
  obtain ⟨_, T, h4⟩ := hf (γ t)
  have l1 : T.baseSet ∈ 𝓝 (γ t) := T.open_baseSet.mem_nhds h4
  have l2 : γ ⁻¹' T.baseSet ∈ 𝓝 t :=
    ContinuousAt.preimage_mem_nhds γ.continuous_toFun.continuousAt l1
  rw [Metric.mem_nhds_iff] at l2 ⊢
  obtain ⟨ε, hε, l3⟩ := l2
  refine ⟨ε, hε, ?_⟩
  intro u hu
  have l4 : uIcc t u ⊆ ball t ε := by
    suffices uIcc t.1 u.1 ⊆ ball t.1 ε by intro v ; apply this
    simpa only [segment_eq_uIcc] using (convex_ball t.1 ε).segment_subset (mem_ball_self hε) hu
  have l5 : MapsTo γ (uIcc t u) T.baseSet := λ v hv => l3 (l4 hv)
  exact good_extend h l5

lemma good_compl_nhds (hf : IsCoveringMap f) (h : ¬ good f γ A t) :
    (goods f γ A)ᶜ ∈ 𝓝 t := by
  obtain ⟨_, T, h4⟩ := hf (γ t)
  have l1 : T.baseSet ∈ 𝓝 (γ t) := T.open_baseSet.mem_nhds h4
  have l2 : γ ⁻¹' T.baseSet ∈ 𝓝 t := γ.continuous_toFun.continuousAt.preimage_mem_nhds l1
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
  exact h <| @good_extend E X _ _ f γ A t u t h' T l5

lemma goods_open (hf : IsCoveringMap f) : IsOpen (goods f γ A) := by
  simpa only [isOpen_iff_mem_nhds] using λ a ha => good_nhds hf ha

lemma goods_compl_open (hf : IsCoveringMap f) : IsOpen (goods f γ A)ᶜ := by
  simpa only [isOpen_iff_mem_nhds] using λ a ha => good_compl_nhds hf ha

theorem lift (hf : IsCoveringMap f) (hγ0 : γ 0 = f A) :
    ∃ Γ : C(I, E), Γ 0 = A ∧ f ∘ Γ = γ := by
  suffices goods f γ A = univ by
    obtain ⟨Γ, h1, h2, h3⟩ := this.symm ▸ mem_univ ⊤
    refine ⟨⟨Γ, ?_⟩, h2, funext <| λ s => h3 s s.2.2⟩
    simpa [continuous_iff_continuousOn_univ] using h1
  have l1 : Set.Nonempty (goods f γ A) := ⟨0, good_zero hγ0⟩
  suffices IsClopen (goods f γ A) from (isClopen_iff.1 this).resolve_left <| Nonempty.ne_empty l1
  exact ⟨goods_open hf, ⟨goods_compl_open hf⟩⟩
