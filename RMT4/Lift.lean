import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyConstant.Basic
import RMT4.Glue

set_option autoImplicit false
set_option pp.proofs.withType false

open Set Topology Metric unitInterval Filter ContinuousMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X}

section Lift

variable {γ : C(I, X)} {x : X} {A : E} {t t₁ t₂ : I} {Γ Γ₁ Γ₂ : C(I, E)}

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
-- instance : ZeroLEOneClass I := ⟨nonneg'⟩

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
    T.continuousOn_invFun.comp_continuous (by continuity) (λ t => by simp only [T.mem_target, h t.2])⟩
  have l1 : f (Γ T₁) = γ t₁ := h2 T₁
  have l2 : Γ T₁ ∈ T.source := T.mem_source.2 <| l1 ▸ h left_mem_uIcc
  refine ⟨trans_Iic Γ δ ?_, trans_Iic_of_le nonneg', λ s => ?_⟩
  · simpa only [ContinuousMap.coe_mk, ← l1, ← T.proj_toFun _ l2] using (T.left_inv' l2).symm
  · by_cases H : s ≤ t₁ <;> simp only [trans_Iic, glue_Iic, ContinuousMap.coe_mk, H, dite_true, h2]
    have l5 : γ s ∈ T.baseSet := h ⟨inf_le_left.trans (not_le.1 H).le, le_trans s.2 le_sup_right⟩
    have l6 {z} : (γ s, z) ∈ T.target := T.mem_target.2 l5
    exact (T.proj_toFun _ (T.map_target' l6)).symm.trans <| congr_arg Prod.fst (T.right_inv' l6)

lemma reachable_nhds_iff (hf : IsCoveringMap f) :
    ∀ᶠ t' in 𝓝 t, (reachable f γ A t' ↔ reachable f γ A t) := by
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

theorem IsCoveringMap.eq_of_comp_eq' (hf : IsCoveringMap f) {A : Type*} [TopologicalSpace A]
    [PreconnectedSpace A] {g₁ g₂ : C(A, E)} (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) :
    g₁ = g₂ :=
  ContinuousMap.ext (congrFun <| hf.eq_of_comp_eq g₁.continuous_toFun g₂.continuous_toFun he a ha)

theorem lift_unique (hf : IsCoveringMap f) {Γ₁ Γ₂ : C(I, E)} (h0 : Γ₁ 0 = Γ₂ 0)
    (h : f ∘ Γ₁ = f ∘ Γ₂) : Γ₁ = Γ₂ := by
  exact hf.eq_of_comp_eq' h 0 h0

theorem lift' (hf : IsCoveringMap f) (hγ : γ 0 = f A) : ∃! Γ : C(I, E), Γ 0 = A ∧ f ∘ Γ = γ := by
  obtain ⟨Γ, h⟩ := lift hf hγ
  exact ⟨Γ, h, λ Γ' h' => lift_unique hf (h'.1.trans h.1.symm) (h'.2.trans h.2.symm)⟩

end Lift

section ExtCover

def extcov (hf : IsCoveringMap f) (γ : C(I, E)) : C(I, X) :=
    ⟨f ∘ γ, hf.continuous.comp γ.continuous⟩

theorem extcover (hf : IsCoveringMap f) : IsCoveringMap (extcov hf) := by
  intro ξ
  refine ⟨?_, ?_⟩
  · refine discreteTopology_iff_nhds.mpr ?refine_1.a
    intro ⟨δ, hδ⟩
    simp [extcov, ← ContinuousMap.ext] at hδ
    sorry
  · sorry

end ExtCover

section HomotopyLift

variable {γ : C(I × I, X)} {e : E} {Y : Type*} [TopologicalSpace Y] {p : E → X}

theorem HLL (hp : IsCoveringMap p) (f₀ : C(Y, X)) (F : C(Y × I, X)) (hF : ∀ y, F (y, 0) = f₀ y)
    (g₀ : Y → E) (hg₀ : p ∘ g₀ = f₀) : ∃! G : C(Y × I, E), p ∘ G = F ∧ ∀ y, G (y, 0) = g₀ y := by
  let γ (y : Y) : C(I, X) := ⟨λ t => F (y, t),
    Continuous.comp' (ContinuousMapClass.map_continuous _) (Continuous.Prod.mk _)⟩
  have h1 {y} : γ y 0 = f₀ y := sorry
  have h3 {y} : γ y 0 = p (g₀ y) := sorry
  choose G hG1 hG2 using λ y => @lift' _ _ _ _ p (γ y) (g₀ y) hp h3
  refine ⟨⟨λ yt => G yt.1 yt.2, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · sorry
  · exact funext (λ yt => congr_fun (hG1 yt.1).2 yt.2)
  · exact λ y => (hG1 y).1
  · intro H ⟨hH1, hH2⟩
    ext ⟨y, t⟩
    let Hy : C(I, E) := ⟨λ t => H (y, t), sorry⟩
    have h4 : (p ∘ fun t => H (y, t)) = fun t => F (y, t) := sorry
    simp [← hG2 y Hy ⟨hH2 y, h4⟩]

-- theorem HomLift (hf : IsCoveringMap f) (h0 : γ (0, 0) = f e) :
--     ∃ Γ : C(I × I, E), Γ (0, 0) = e ∧ f ∘ Γ = γ := by
--   -- track starting points
--   let φ : C(I, I × I) := ⟨λ s => (s, 0), continuous_prod_mk.mpr ⟨continuous_id, continuous_const⟩⟩
--   let ζ : C(I, X) := γ.comp φ
--   obtain ⟨Z, ⟨hZ1, hZ2⟩, hZ3⟩ := lift' (γ := ζ) hf h0
--   -- build layers
--   let ψ s : C(I, I × I) := ⟨λ t => (s, t), continuous_prod_mk.mpr ⟨continuous_const, continuous_id⟩⟩
--   let δ s : C(I, X) := γ.comp (ψ s)
--   have l1 {s} : (δ s) 0 = f (Z s) := (congr_fun hZ2 s).symm
--   choose Δ hΔ1 hΔ2 using λ s => @lift' E X _ _ f (δ s) (Z s) hf l1
--   -- finish proof
--   refine ⟨⟨λ st => Δ st.1 st.2, ?_⟩, ?_, ?_⟩
--   ·
--     sorry
--   · simp [(hΔ1 0).1, hZ1]
--   · exact funext <| λ st => congr_fun (hΔ1 st.1).2 st.2

end HomotopyLift
