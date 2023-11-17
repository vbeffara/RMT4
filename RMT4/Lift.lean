import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyConstant.Basic
import RMT4.Glue

set_option autoImplicit false
set_option pp.proofs.withType false

open Set Topology Metric unitInterval Filter ContinuousMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {f : E → X} {γ : C(I, X)} {x : X} {A : E} {t t₁ t₂ : I} {Γ Γ₁ Γ₂ : C(I, E)}

lemma isClopen_iff_nhds {E : Type*} [TopologicalSpace E] {s : Set E} :
    IsClopen s ↔ ∀ a, ∀ᶠ b in 𝓝 a, b ∈ s ↔ a ∈ s where
  mp h a := by
    by_cases h3 : a ∈ s
    · simpa [h3] using h.1.mem_nhds h3
    · simpa only [h3, iff_false] using h.2.isOpen_compl.mem_nhds h3
  mpr h := by
    constructor
    · simpa [isOpen_iff_mem_nhds] using λ a ha => by simpa [ha] using h a
    · exact ⟨by simpa [isOpen_iff_mem_nhds] using λ a ha => by simpa only [ha, iff_false] using h a⟩

instance : Zero (Iic t) := ⟨0, nonneg'⟩
instance : ZeroLEOneClass I := ⟨nonneg'⟩

def reachable (f : E → X) (γ : C(I, X)) (A : E) (t : I) : Prop :=
  ∃ Γ : C(Iic t, E), Γ 0 = A ∧ ∀ s, f (Γ s) = γ s

lemma reachable_zero (hγ : γ 0 = f A) : reachable f γ A 0 := by
  refine ⟨⟨λ _ => A, continuous_const⟩, rfl, ?_⟩
  intro ⟨s, (hs : s ≤ 0)⟩ ; simp [le_antisymm hs s.2.1, hγ]

lemma reachable_extend {T : Trivialization (f ⁻¹' {γ t}) f} (h : MapsTo γ (uIcc t₁ t₂) T.baseSet) :
    reachable f γ A t₁ → reachable f γ A t₂ := by
  rintro ⟨Γ, rfl, h2⟩
  let T₁ : Iic t₁ := ⟨t₁, mem_Iic.2 le_rfl⟩
  let δ : C(uIcc t₁ t₂, E) := ⟨λ s => T.invFun ⟨γ s, (T (Γ T₁)).2⟩,
    T.continuous_invFun.comp_continuous (by continuity) (λ t => by simp only [T.mem_target, h t.2])⟩
  have l1 : f (Γ T₁) = γ t₁ := h2 T₁
  have l2 : Γ T₁ ∈ T.source := T.mem_source.2 <| l1 ▸ h left_mem_uIcc
  refine ⟨trans_Iic Γ δ ?_, trans_Iic_of_le nonneg', λ s => ?_⟩
  · simpa only [ContinuousMap.coe_mk, ← l1, ← T.proj_toFun _ l2] using (T.left_inv' l2).symm
  · by_cases H : s ≤ t₁ <;> simp only [trans_Iic, glue_Iic, ContinuousMap.coe_mk, H, dite_true, h2]
    have l5 : γ s ∈ T.baseSet := h ⟨inf_le_left.trans (not_le.1 H).le, le_trans s.2 le_sup_right⟩
    have l6 {z} : (γ s, z) ∈ T.target := T.mem_target.2 l5
    exact (T.proj_toFun _ (T.map_target' l6)).symm.trans <| congr_arg Prod.fst (T.right_inv' l6)

lemma reachable_nhds_iff (hf : IsCoveringMap f) :
    ∀ᶠ t' in 𝓝 t, reachable f γ A t' ↔ reachable f γ A t := by
  obtain ⟨_, T, h4⟩ := hf (γ t)
  have l2 := γ.continuousAt _ |>.preimage_mem_nhds <| T.open_baseSet.mem_nhds h4
  simp only [Filter.Eventually, Metric.mem_nhds_iff] at l2 ⊢
  obtain ⟨ε, hε, l3⟩ := l2
  refine ⟨ε, hε, λ u hu => ?_⟩
  have : segment ℝ t.1 u.1 ⊆ ball t.1 ε := (convex_ball t.1 ε).segment_subset (mem_ball_self hε) hu
  have l5 : uIcc t.1 u.1 ⊆ ball t.1 ε := by rwa [← segment_eq_uIcc]
  have l6 : MapsTo γ (uIcc t u) T.baseSet := λ v hv => l3 (l5 hv)
  exact ⟨reachable_extend <| uIcc_comm t u ▸ l6, reachable_extend l6⟩

theorem lift (hf : IsCoveringMap f) (hγ : γ 0 = f A) : ∃ Γ : C(I, E), Γ 0 = A ∧ f ∘ Γ = γ := by
  have l1 : Set.Nonempty {t | reachable f γ A t} := ⟨0, reachable_zero hγ⟩
  have l2 : IsClopen {t | reachable f γ A t} := isClopen_iff_nhds.2 (λ t => reachable_nhds_iff hf)
  let ⟨Γ, h1, h2⟩ := ((isClopen_iff.1 l2).resolve_left <| Nonempty.ne_empty l1).symm ▸ mem_univ 1
  refine ⟨⟨IicExtend Γ, Γ.2.Iic_extend'⟩, by simpa [IicExtend, projIic] using h1, funext (λs => ?_)⟩
  simp [IicExtend, projIic, s.2.2] ; convert h2 ⟨s, s.2.2⟩ ; simpa using s.2.2

lemma prekey {T : Trivialization (f ⁻¹' {x}) f} [DiscreteTopology (f ⁻¹' {x})] {z : E}
    (h : z ∈ T.source) : ∀ᶠ w in 𝓝 z, T w = (f w, (T z).2) := by
  have l1 : {(T z).2} ∈ 𝓝 (T z).2 := by simp only [nhds_discrete, mem_pure, mem_singleton_iff]
  have l2 : ∀ᶠ w in 𝓝 z, (T w).2 = (T z).2 := continuousAt_snd.comp (T.continuousAt h) l1
  filter_upwards [T.open_source.mem_nhds h, l2] with s hs r2 using Prod.ext (T.coe_fst hs) r2

lemma key {T : Trivialization (f ⁻¹' {x}) f} [DiscreteTopology (f ⁻¹' {x})] (h : Γ t ∈ T.source) :
    ∀ᶠ s in 𝓝 t, T (Γ s) = (f (Γ s), (T (Γ t)).2) := Γ.continuousAt _ (prekey h)

lemma key2 {T : Trivialization (f ⁻¹' {x}) f} [DiscreteTopology (f ⁻¹' {x})] (h : Γ t ∈ T.source) :
    ∀ᶠ s in 𝓝 t, Γ s = T.invFun (f (Γ s), (T (Γ t)).2) := by
  filter_upwards [key h, Γ.continuousAt _ <| T.open_source.mem_nhds h] with s r1 r2
  simpa only [← r1] using (T.left_inv r2).symm

lemma locally_eq (hf : IsCoveringMap f) (h1 : Γ₁ t = Γ₂ t) (h2 : f ∘ Γ₁ =ᶠ[𝓝 t] f ∘ Γ₂) :
    Γ₁ =ᶠ[𝓝 t] Γ₂ := by
  obtain ⟨l1, T, l2⟩ := hf (f (Γ₁ t))
  rw [← T.mem_source] at l2
  filter_upwards [key2 l2, key2 (Γ := Γ₂) (T := T) (h1 ▸ l2), h2] with s r2 r3 (r4 : f _ = f _)
  rw [r2, r3] ; congr

lemma locally_eq_iff (hf : IsCoveringMap f) (h2 : f ∘ Γ₁ =ᶠ[𝓝 t] f ∘ Γ₂) :
    ∀ᶠ s in 𝓝 t, Γ₁ s = Γ₂ s ↔ Γ₁ t = Γ₂ t := by
  obtain ⟨l1, T, l2⟩ := hf (f (Γ₁ t))
  have : f _ = f _ := h2.self_of_nhds
  have l3 : f (Γ₂ t) ∈ T.baseSet := by simp [← show f (Γ₁ t) = f (Γ₂ t) from this, l2]
  rw [← T.mem_source] at l2 l3
  filter_upwards [key2 l2, key2 l3, key l2, key l3, h2] with s r2 r3 r4 r5 (r6 : f _ = f _)
  refine ⟨λ h => ?_, λ h => by { rw [r2, r3] ; congr }⟩
  suffices T (Γ₁ t) = T (Γ₂ t) by rw [← T.left_inv' l2, ← T.left_inv' l3] ; congr 1
  apply Prod.ext (by simpa [T.coe_fst, l2, l3])
  simpa using congr_arg Prod.snd (show (_, _) = (_, _) from (h ▸ r4).symm.trans r5)

theorem lift_unique (hf : IsCoveringMap f) {Γ₁ Γ₂ : C(I, E)} (h0 : Γ₁ 0 = Γ₂ 0)
    (h : f ∘ Γ₁ = f ∘ Γ₂) : Γ₁ = Γ₂ := by
  refine ContinuousMap.ext <| (eq_univ_iff_forall (s := {t | Γ₁ t = Γ₂ t})).1 ?_
  refine isClopen_iff.1 ?_ |>.resolve_left <| Nonempty.ne_empty ⟨0, h0⟩
  exact isClopen_iff_nhds.2 <| λ t => locally_eq_iff hf <| eventually_of_forall <| congrFun h
