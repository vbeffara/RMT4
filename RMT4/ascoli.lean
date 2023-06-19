/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Topology.UniformSpace.Equicontinuity

open Set Filter Uniformity Function UniformConvergence

-- open Set Filter UniformSpace function
-- open_locale Filter TopologicalSpace uniform_convergence uniformity

lemma supr_sUnion [CompleteLattice β] {S : Set (Set α)} {p : α → β} :
    (⨆ x ∈ ⋃₀ S, p x) = ⨆ (s ∈ S) (x ∈ s), p x := by
  rw [sUnion_eq_iUnion, iSup_iUnion, ← iSup_subtype'']

lemma infi_sUnion [CompleteLattice β] {S : Set (Set α)} {p : α → β} :
    (⨅ x ∈ ⋃₀ S, p x) = ⨅ (s ∈ S) (x ∈ s), p x := by
  rw [sUnion_eq_iUnion, iInf_iUnion, ← iInf_subtype'']

lemma forall_sUnion {S : Set (Set α)} {p : α → Prop} :
    (∀ x ∈ ⋃₀ S, p x) ↔ ∀ s ∈ S, ∀ x ∈ s, p x := by
  simp_rw [← iInf_Prop_eq, infi_sUnion]

-- lemma TotallyBounded_pi {ι : Type*} {α : ι → Type*} [Π i, UniformSpace (α i)]
--   {t : Set ι} {s : Π i, Set (α i)} (hs : ∀ i ∈ t, TotallyBounded (s i)) :
--   TotallyBounded (t.pi s) :=
-- sorry

lemma cauchy_of_ne_bot [UniformSpace α] {l : Filter α} [hl : NeBot l] :
    Cauchy l ↔ l ×ˢ l ≤ 𝓤 α := by
  simp [Cauchy, hl]

lemma cauchy_pi {α : ι → Type u} [∀ i, UniformSpace (α i)] {l : Filter (∀ i, α i)} [NeBot l] :
    Cauchy l ↔ ∀ i, Cauchy (map (Function.eval i) l) := by
  simp_rw [cauchy_of_ne_bot, prod_map_map_eq, map_le_iff_le_comap, Pi.uniformity, le_iInf_iff]

lemma cauchy_infi {u : ι → UniformSpace α} {l : Filter α} [NeBot l] :
    @Cauchy _ (⨅ i, u i) l ↔ ∀ i, @Cauchy _ (u i) l := by
  have h1 : NeBot l := by assumption
  simp [Cauchy, iInf_uniformity, h1]

lemma cauchy_map_iff_comap {u : UniformSpace β} {f : α → β} {l : Filter α} :
    Cauchy (map f l) ↔ @Cauchy _ (UniformSpace.comap f u) l := by
  simp only [Cauchy, map_neBot_iff, prod_map_map_eq, map_le_iff_le_comap, uniformity_comap]
  rfl

variable [TopologicalSpace X] [UniformSpace α] {F : ι → X → α}
-- [UniformSpace β] {G : ι → β → α}

lemma theorem1 [CompactSpace X] (hF : Equicontinuous F) :
    (UniformFun.uniformSpace X α).comap F = (Pi.uniformSpace (λ _ => α)).comap F := by
  sorry

-- TODO: this is too long
lemma theorem1' {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F =
      (⨅ K ∈ 𝔖, ⨅ x ∈ K, ‹UniformSpace α›.comap (eval x)).comap F := by
  rw [UniformOnFun.uniformSpace]
  simp_rw [UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
  refine iInf_congr (λ K => iInf_congr $ λ hK => ?_)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (h𝔖 K hK)
  simp_rw [theorem1 (hF K hK), @UniformSpace.comap_comap _ _ _ _ F,
            Pi.uniformSpace, UniformSpace.ofCoreEq_toCore, UniformSpace.comap_iInf, iInf_subtype]
  refine iInf_congr (λ x => iInf_congr $ λ hx => congr_arg _ ?_)
  rw [← UniformSpace.comap_comap]
  exact congr_fun (congr_arg _ rfl) _

lemma theorem1'' {𝔖 : Set (Set X)} (hcover : ⋃₀ 𝔖 = univ) (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F = (Pi.uniformSpace (λ _ => α)).comap F := by
  simp [theorem1' h𝔖 hF, Pi.uniformSpace, UniformSpace.ofCoreEq_toCore, ←infi_sUnion, hcover]

lemma ascoli₀ {𝔖 : Set (Set X)} {F : ι → X →ᵤ[𝔖] α} {l : Filter ι} [NeBot l]
    (h1 : ∀ A ∈ 𝔖, IsCompact A)
    (h2 : ∀ A ∈ 𝔖, Equicontinuous (λ i => Set.restrict A (F i)))
    (h3 : ∀ x ∈ ⋃₀ 𝔖, Cauchy (map (eval x ∘ F) l)) :
    Cauchy (map F l) := by
  sorry

lemma ascoli {𝔖 : Set (Set X)} {F : ι → X →ᵤ[𝔖] α}
    (h1 : ∀ A ∈ 𝔖, IsCompact A)
    (h2 : ∀ A ∈ 𝔖, Equicontinuous (λ i => Set.restrict A (F i)))
    (h3 : ∀ x ∈ ⋃₀ 𝔖, TotallyBounded (range (λ i => F i x))) :
    TotallyBounded (range F) := by
  simp_rw [totallyBounded_iff_ultrafilter] at h3 ⊢
  intro f hf
  have : F '' univ ∈ f := by rwa [image_univ, ← Ultrafilter.mem_coe, ← le_principal_iff]
  rw [← Ultrafilter.ofComapInfPrincipal_eq_of_map this]
  set g := Ultrafilter.ofComapInfPrincipal this
  apply ascoli₀ h1 h2
  intro x hx
  apply h3 x hx (g.map (eval x ∘ F))
  exact (le_principal_iff.mpr range_mem_map)
