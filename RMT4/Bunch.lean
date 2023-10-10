import Mathlib
import RMT4.pintegral
import RMT4.LocallyConstant
import RMT4.to_mathlib

set_option autoImplicit false

open Topology Filter Metric TopologicalSpace Set Subtype

structure Bunch (ι α β : Type) [TopologicalSpace α] where
  F : ι → α → β
  S : ι → Set α
  cov (z : α × β) : ∃ i, z.1 ∈ S i ∧ F i z.1 = z.2
  cmp i j : IsOpen { a ∈ S i ∩ S j | F i a = F j a }

namespace Bunch

variable {ι α β : Type} [TopologicalSpace α] {B : Bunch ι α β} {i₁ i₂ i j : ι} {a : α}

lemma opn : IsOpen (B.S i) := by simpa using B.cmp i i

def space (_ : Bunch ι α β) := α × β

variable {s s₁ s₂ : Set B.space} {z : B.space}

instance : CoeFun (Bunch ι α β) (λ _ => ι → α → β) := ⟨Bunch.F⟩

def idx (B : Bunch ι α β) (z : B.space) := { i | z.1 ∈ B.S i ∧ B i z.1 = z.2 }

def tile (B : Bunch ι α β) (i : ι) (s : Set α) : Set B.space := (λ x => (x, B i x)) '' s

lemma tile_mono {s t : Set α} (h : s ⊆ t) : B.tile i s ⊆ B.tile i t := image_subset _ h

lemma tile_congr {s : Set α} (h : EqOn (B i) (B j) s) : B.tile i s = B.tile j s :=
  image_congr (λ x hx => by rw [h hx])

lemma subset_iff_forall (a : Set α) (b : Set β) (f : α → β) : f '' a ⊆ b ↔ ∀ x ∈ a, f x ∈ b := by
  rw [image_subset_iff] ; rfl

lemma eventuallyEq (hi : a ∈ B.S i) (hj : a ∈ B.S j) (h : B i a = B j a) : ∀ᶠ b in 𝓝 a, B i b = B j b :=
  (eventually_and.1 <| (B.cmp i j).mem_nhds ⟨⟨hi, hj⟩, h⟩).2

lemma tile_inter {s₁ s₂ : Set α} (hi₁ : i₁ ∈ B.idx z) (hi₂ : i₂ ∈ B.idx z) (hi : i ∈ B.idx z)
    (h₁ : s₁ ∈ 𝓝 z.1) (h₂ : s₂ ∈ 𝓝 z.1) :
    ∃ s ∈ 𝓝 z.1, B.tile i s ⊆ B.tile i₁ s₁ ∩ B.tile i₂ s₂ := by
  suffices : ∀ᶠ b in 𝓝 z.1, (b, B i b) ∈ B.tile i₁ s₁ ∩ B.tile i₂ s₂
  · simpa only [eventually_iff_exists_mem, ← subset_iff_forall] using this
  obtain ⟨hi₁, hi'₁⟩ := hi₁
  obtain ⟨hi₂, hi'₂⟩ := hi₂
  have l1 := eventuallyEq hi₁ hi.1 (hi'₁.trans hi.2.symm)
  have l2 := eventuallyEq hi₂ hi.1 (hi'₂.trans hi.2.symm)
  filter_upwards [h₁, h₂, l1, l2] with b e1 e2 e3 e4
  refine ⟨⟨b, e1, by simp only [e3]⟩, ⟨b, e2, by simp only [e4]⟩⟩

def reaches (B : Bunch ι α β) (is : ι × Set α) (z : B.space) := is.1 ∈ B.idx z ∧ is.2 ∈ 𝓝 z.1

lemma isBasis (z : B.space) : IsBasis (λ is => B.reaches is z) (λ is => B.tile is.1 is.2) where
  nonempty := by
    obtain ⟨i, hi⟩ := B.cov z
    refine ⟨⟨i, univ⟩, hi, univ_mem⟩
  inter := by
    rintro i j ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
    obtain ⟨s, hs1, hs2⟩ := tile_inter hi1 hj1 hi1 hi2 hj2
    refine ⟨⟨i.1, s⟩, ⟨⟨hi1, hs1⟩, hs2⟩⟩

def nhd (B : Bunch ι α β) (i : ι) (a : α) : Filter B.space := Filter.map (λ x => (x, B i x)) (𝓝 a)

def nhd' (z : B.space) : Filter B.space := (isBasis z).filter

lemma mem_nhd' : s ∈ nhd' z ↔ ∃ i ∈ B.idx z, ∃ v ∈ 𝓝 z.1, B.tile i v ⊆ s := by
  simp only [nhd', (isBasis z).mem_filter_iff, reaches] ; aesop

lemma mem_nhd_iff : s ∈ nhd B i a ↔ ∀ᶠ x in 𝓝 a, (x, B i x) ∈ s := by rfl

lemma mem_nhd_1 : s ∈ B.nhd i a ↔ ∃ t ∈ 𝓝 a, B.tile i t ⊆ s := by
  simpa [tile, mem_nhd_iff] using eventually_iff_exists_mem

instance : TopologicalSpace B.space := TopologicalSpace.mkOfNhds nhd'

lemma nhd_congr (h1 : a ∈ B.S i ∩ B.S j) (h2 : B i a = B j a) : B.nhd i a = B.nhd j a := by
  apply Filter.map_congr
  apply eventually_of_mem <| B.cmp i j |>.mem_nhds ⟨h1, h2⟩
  rintro x h ; simp only [h.2]

lemma nhd_any (ha : a ∈ B.S i) : s ∈ B.nhd i a ↔ ∃ j, a ∈ B.S j ∧ B i a = B j a ∧ s ∈ B.nhd j a where
  mp h := ⟨i, ha, rfl, h⟩
  mpr := by rintro ⟨j, h1, h2, h3⟩ ; exact (nhd_congr ⟨ha, h1⟩ h2).symm ▸ h3

@[simp] theorem self (x : B.space) : B ↑(B.cov x).choose x.1 = x.2 := (B.cov x).choose_spec.2

theorem pure_le_nhd (z : B.space) : pure z ≤ nhd' z := by
  intro s hs
  simp only [mem_nhd', tile] at hs
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := hs
  apply hi4
  simp only [mem_image]
  refine ⟨z.1, mem_of_mem_nhds hi3, ?_⟩
  rw [hi1.2]
  rfl

theorem nhd_is_nhd (h1 : z.1 ∈ B.S i) (h2 : s ∈ B.nhd i z.1) :
  ∃ t ∈ B.nhd i z.1, t ⊆ s ∧ ∀ w ∈ t,
    w.1 ∈ B.S i ∧ ∀ j, w.1 ∈ B.S j ∧ B j w.1 = B i w.1 → s ∈ B.nhd j w.1 := by
  sorry

theorem nhd_is_nhd' (ha : s ∈ B.nhd (B.cov z).choose z.1) :
    ∃ t ∈ nhd B (B.cov z).choose z.1, t ⊆ s ∧ ∀ w ∈ t, s ∈ nhd B (B.cov w).choose w.fst := by
  sorry

lemma mem_nhds_iff : s ∈ 𝓝 z ↔ ∃ i, ∀ᶠ a in 𝓝 z.1, (a, B i a) ∈ s := by
  rw [nhds_mkOfNhds _ _ pure_le_nhd]
  · sorry
  · sorry

end Bunch
