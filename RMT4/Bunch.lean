import Mathlib.Topology.Basic
import Mathlib.Data.Set.Image
import Mathlib.Topology.MetricSpace.Basic

open Topology Filter Metric TopologicalSpace Set Subtype

structure Bunch (ι α β : Type) [TopologicalSpace α] where
  S : ι → Set α
  F : ι → α → β
  cmp i j : IsOpen { a ∈ S i ∩ S j | F i a = F j a }

namespace Bunch

variable {ι α β : Type} [TopologicalSpace α] {i₁ i₂ i j : ι} {a : α} {b : β} {s t : Set α}

instance : CoeFun (Bunch ι α β) (λ _ => ι → α → β) := ⟨Bunch.F⟩

def space (_ : Bunch ι α β) := α × β

def idx (B : Bunch ι α β) (z : B.space) : Set ι := { i | z.1 ∈ B.S i ∧ B i z.1 = z.2 }

def tile (B : Bunch ι α β) (i : ι) (s : Set α) : Set B.space := (λ x => (x, B i x)) '' s

def range (B : Bunch ι α β) : Set (B.space) := { z | Nonempty (B.idx z) }

def reaches (B : Bunch ι α β) (is : ι × Set α) (z : B.space) := is.1 ∈ B.idx z ∧ is.2 ∈ 𝓝 z.1

lemma opn (B : Bunch ι α β) (i : ι) : IsOpen (B.S i) := by simpa using B.cmp i i

variable {B : Bunch ι α β} {s s₁ s₂ : Set B.space} {z : B.space}

lemma S_mem_nhd (hi : i ∈ B.idx z) : B.S i ∈ 𝓝 z.1 := B.opn i |>.mem_nhds hi.1

lemma eq_of_mem_tile (h : z ∈ B.tile i t) : B i z.1 = z.2 := by
  obtain ⟨x, _, rfl⟩ := h ; rfl

lemma tile_mono {s t : Set α} (h : s ⊆ t) : B.tile i s ⊆ B.tile i t := image_subset _ h

lemma tile_congr {s : Set α} (h : EqOn (B i) (B j) s) : B.tile i s = B.tile j s :=
  image_congr (λ x hx => by rw [h hx])

lemma subset_iff_forall (a : Set α) (b : Set β) (f : α → β) : f '' a ⊆ b ↔ ∀ x ∈ a, f x ∈ b := by
  rw [image_subset_iff] ; rfl

lemma eventuallyEq (hi : a ∈ B.S i) (hj : a ∈ B.S j) (h : B i a = B j a) :
    ∀ᶠ b in 𝓝 a, B i b = B j b :=
  (eventually_and.1 <| (B.cmp i j).mem_nhds ⟨⟨hi, hj⟩, h⟩).2

lemma tile_inter {s₁ s₂ : Set α} (hi₁ : i₁ ∈ B.idx z) (hi₂ : i₂ ∈ B.idx z) (hi : i ∈ B.idx z)
    (h₁ : s₁ ∈ 𝓝 z.1) (h₂ : s₂ ∈ 𝓝 z.1) :
    ∃ s ∈ 𝓝 z.1, B.tile i s ⊆ B.tile i₁ s₁ ∩ B.tile i₂ s₂ := by
  suffices h : ∀ᶠ b in 𝓝 z.1, (b, B i b) ∈ B.tile i₁ s₁ ∩ B.tile i₂ s₂
    by simpa only [eventually_iff_exists_mem, ← subset_iff_forall] using h
  have l1 := eventuallyEq hi₁.1 hi.1 (hi₁.2.trans hi.2.symm)
  have l2 := eventuallyEq hi₂.1 hi.1 (hi₂.2.trans hi.2.symm)
  filter_upwards [h₁, h₂, l1, l2] with b e1 e2 e3 e4
  exact ⟨⟨b, e1, by simp only [e3]⟩, ⟨b, e2, by simp only [e4]⟩⟩

lemma isBasis (hz : z ∈ B.range) :
    IsBasis (λ is => B.reaches is z) (λ is => B.tile is.1 is.2) where
  nonempty := by
    obtain ⟨i, hi⟩ := hz
    refine ⟨⟨i, univ⟩, hi, univ_mem⟩
  inter := by
    rintro i j ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
    obtain ⟨s, hs1, hs2⟩ := tile_inter hi1 hj1 hi1 hi2 hj2
    refine ⟨⟨i.1, s⟩, ⟨⟨hi1, hs1⟩, hs2⟩⟩

def nhd (z : B.space) : Filter B.space := open Classical in
  if h : Nonempty (B.idx z) then (isBasis h).filter else pure z

instance : TopologicalSpace B.space := TopologicalSpace.mkOfNhds nhd

lemma mem_nhd (h : Nonempty (B.idx z)) :
    s ∈ nhd z ↔ ∃ i ∈ B.idx z, ∃ v ∈ 𝓝 z.1, B.tile i v ⊆ s := by
  simp only [nhd, h, dite_true]
  simp [(isBasis h).mem_filter_iff, reaches, and_assoc]

theorem eventually_apply_mem {f : α → β} {t : Set β} :
    (∀ᶠ x in 𝓝 a, f x ∈ t) ↔ (∃ s ∈ 𝓝 a, s ⊆ f ⁻¹' t) :=
  eventually_iff_exists_mem

theorem eventually_mem_iff_tile :
    (∀ᶠ b in 𝓝 a, (b, B j b) ∈ s) ↔ (∃ v ∈ 𝓝 a, tile B j v ⊆ s) := by
  simp [tile, ← eventually_apply_mem]

lemma tile_mem_nhd' {s : Set α} (hi : i ∈ B.idx z) (hs : s ∈ 𝓝 z.1) : B.tile i s ∈ nhd z := by
  have : Nonempty (B.idx z) := ⟨_, hi⟩
  simp only [nhd, this, dite_true]
  simpa only [IsBasis.mem_filter_iff] using ⟨(i, s), ⟨hi, hs⟩, subset_rfl⟩

lemma mem_nhd_open (hz : Nonempty (B.idx z)) (h : s ∈ nhd z) :
    ∃ i ∈ B.idx z, ∃ v ∈ 𝓝 z.1, IsOpen v ∧ B.tile i v ⊆ s := by
  obtain ⟨i, hi1, t, hi3, hi4⟩ := (mem_nhd hz).1 h
  obtain ⟨s', ⟨h1, h2⟩, h3⟩ := nhds_basis_opens' z.1 |>.mem_iff.1 hi3
  exact ⟨i, hi1, s', h1, h2, tile_mono h3 |>.trans hi4⟩

theorem pure_le (z : B.space) : pure z ≤ nhd z := by
  by_cases h : Nonempty (B.idx z)
  · intro s hs
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := (mem_nhd h).1 hs
    exact hi4 ⟨z.1, mem_of_mem_nhds hi3, by simp [hi1.2]⟩
  · simp only [nhd, h, dite_false] ; rfl

theorem nhd_is_nhd (a : space B) (s : Set (space B)) (hs : s ∈ nhd a) :
    ∃ t ∈ nhd a, t ⊆ s ∧ ∀ b ∈ t, s ∈ nhd b := by
  by_cases h : Nonempty (B.idx a)
  · obtain ⟨i, hi1, s₀, hi2, hi3, hi4⟩ := mem_nhd_open h hs
    refine ⟨B.tile i (s₀ ∩ B.S i), ?_, ?_, ?_⟩
    · exact tile_mem_nhd' hi1 <| inter_mem hi2 <| S_mem_nhd hi1
    · exact tile_mono (inter_subset_left _ _) |>.trans hi4
    · rintro b ⟨c, hb1, rfl⟩
      refine mem_of_superset ?_ hi4
      refine tile_mem_nhd' ⟨?_, rfl⟩ ?_
      · exact inter_subset_right _ _ hb1
      · exact hi3.mem_nhds <| inter_subset_left _ _ hb1
  · have hs' := hs
    simp only [nhd, h, dite_false, mem_pure] at hs'
    refine ⟨{a}, ?_, by simp [hs'], ?_⟩
    · simp only [nhd, h, dite_false] ; simp
    · simp [hs]

lemma nhds_eq_nhd : 𝓝 z = nhd z := by
  refine nhds_mkOfNhds _ _ pure_le ?_
  intro a s hs
  obtain ⟨t, h1, _, h3⟩ := nhd_is_nhd a s hs -- TODO simplify `nhd_is_nhd`
  apply eventually_of_mem h1 h3

lemma mem_nhds_tfae (h : Nonempty (B.idx z)) : List.TFAE [
      s ∈ 𝓝 z,
      s ∈ nhd z,
      ∃ i ∈ B.idx z, ∀ᶠ a in 𝓝 z.1, (a, B i a) ∈ s,
      ∃ i ∈ B.idx z, ∃ t ∈ 𝓝 z.1, B.tile i t ⊆ s
    ] := by
  tfae_have 1 ↔ 2 ; simp [nhds_eq_nhd]
  tfae_have 2 ↔ 4 ; exact mem_nhd h
  tfae_have 3 ↔ 4 ; simp [eventually_mem_iff_tile]
  tfae_finish

@[simp] lemma nhds_eq_pure (h : ¬ Nonempty (B.idx z)) : 𝓝 z = pure z := by
  simp only [nhds_eq_nhd, nhd, h, dite_false]

lemma tile_mem_nhd {s : Set α} (hi : i ∈ B.idx z) (hs : s ∈ 𝓝 z.1) : B.tile i s ∈ 𝓝 z := by
  simpa [nhds_eq_nhd] using tile_mem_nhd' hi hs

def p (B : Bunch ι α β) (z : B.space) : α := z.1

lemma discreteTopology : DiscreteTopology (B.p ⁻¹' {a}) := by
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_induced]
  rintro ⟨z₁, z₂⟩ rfl
  by_cases h : Nonempty (B.idx (z₁, z₂))
  · obtain ⟨i, h1, rfl : B i z₁ = z₂⟩ := h
    refine ⟨B.tile i <| B.S i, ?_, ?_⟩
    · exact tile_mem_nhd ⟨h1, rfl⟩ <| S_mem_nhd ⟨h1, rfl⟩
    · rintro x rfl ⟨u, _, rfl⟩ ; rfl
  · refine ⟨{(z₁, z₂)}, ?_, by simp⟩
    simp only [nhds_eq_nhd, nhd, h, dite_false, mem_pure, mem_singleton]

lemma continuous_p : Continuous B.p := by
  rw [continuous_iff_continuousAt] ; intro x s hs
  by_cases h : Nonempty (B.idx x)
  · obtain ⟨i, hi⟩ := h
    apply mem_of_superset <| tile_mem_nhd hi hs
    rintro y ⟨x, hx, rfl⟩ ; exact hx
  · simpa only [nhds_eq_nhd, nhd, h, dite_false, Filter.map_pure, mem_pure] using mem_of_mem_nhds hs

end Bunch

section lift

variable {ι α β γ : Type} [TopologicalSpace α] {B : Bunch ι α β}
  {γ : Type} [TopologicalSpace γ] [PreconnectedSpace γ]

def IsLiftOf (g : γ → B.space) (f : γ → α) : Prop := Continuous g ∧ ∀ x, B.p (g x) = f x

lemma eventually_mem_tile {γ : Type} [TopologicalSpace γ] {f : γ → B.space} {x : γ}
    (hf : ContinuousAt f x) {i : ι} (hi : i ∈ B.idx (f x)) :
    ∀ᶠ y in 𝓝 x, (f y).2 = B.F i (f y).1 := by
  refine eventually_of_mem (hf.preimage_mem_nhds <| B.tile_mem_nhd hi <| B.S_mem_nhd hi) ?_
  exact λ x hx => by simp [B.eq_of_mem_tile hx]

theorem eventually_eq_of_lift {γ : Type} [TopologicalSpace γ] {f : γ → α}
    {g₁ g₂ : γ → Bunch.space B} (h₁ : IsLiftOf g₁ f) (h₂ : IsLiftOf g₂ f) {x : γ}
    (hx : g₁ x = g₂ x) (h1 : Nonempty ↑(Bunch.idx B (g₁ x))) : g₁ =ᶠ[𝓝 x] g₂ := by
  obtain ⟨i1, hi1⟩ := h1
  filter_upwards [eventually_mem_tile (h₁.1.continuousAt) hi1,
    eventually_mem_tile (h₂.1.continuousAt) (hx ▸ hi1)] with y r1 r2
  have r4 : (g₁ y).1 = f y := h₁.2 y
  have r5 : (g₂ y).1 = f y := h₂.2 y
  rw [Prod.ext_iff]
  simp [r1, r2, r4, r5]

theorem eventually_eq_of_lift' {γ : Type} [TopologicalSpace γ] {f : γ → α} {x : γ}
    {g₁ g₂ : γ → Bunch.space B} (h₁ : IsLiftOf g₁ f) (h₂ : IsLiftOf g₂ f) (hx : g₁ x = g₂ x) :
    g₁ =ᶠ[𝓝 x] g₂ := by
  by_cases h1 : Nonempty ↑(Bunch.idx B (g₁ x))
  · obtain ⟨i1, hi1⟩ := h1
    filter_upwards [eventually_mem_tile (h₁.1.continuousAt) hi1,
      eventually_mem_tile (h₂.1.continuousAt) (hx ▸ hi1)] with y r1 r2
    have r4 : (g₁ y).1 = f y := h₁.2 y
    have r5 : (g₂ y).1 = f y := h₂.2 y
    rw [Prod.ext_iff]
    simp [r1, r2, r4, r5]
  · have h2 := h₁.1.tendsto x
    have h3 := h₂.1.tendsto x
    simp [Bunch.nhds_eq_pure h1, Bunch.nhds_eq_pure (hx ▸ h1), tendsto_pure] at h2 h3
    filter_upwards [h2, h3] with y h4 h5
    simp [hx, h4, h5]

theorem isOpen_eq_of_lift {γ : Type} [TopologicalSpace γ] {f : γ → α} {g₁ g₂ : γ → Bunch.space B}
    (h₁ : IsLiftOf g₁ f) (h₂ : IsLiftOf g₂ f) : IsOpen {x | g₁ x = g₂ x} := by
  simpa only [isOpen_iff_eventually] using λ _ => eventually_eq_of_lift' h₁ h₂

lemma lift_congr (f : γ → α) (g₁ g₂ : γ → B.space) (h₁ : IsLiftOf g₁ f) (h₂ : IsLiftOf g₂ f)
    {x₀ : γ} (h₀ : g₁ x₀ = g₂ x₀) : g₁ = g₂ := by
  let s : Set γ := { x | g₁ x = g₂ x }
  have h2 : IsClosed s := by sorry
  have h3 : IsClopen s := ⟨h2, isOpen_eq_of_lift h₁ h₂⟩
  have h4 : s = univ := (isClopen_iff.1 h3).resolve_left <| Nonempty.ne_empty ⟨x₀, h₀⟩
  exact funext (λ x => (h4 ▸ mem_univ x : x ∈ s))
end lift
