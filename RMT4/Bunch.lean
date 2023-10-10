import Mathlib
import RMT4.pintegral
import RMT4.LocallyConstant
import RMT4.to_mathlib

set_option autoImplicit false

open Topology Filter Metric TopologicalSpace Set Subtype

variable {ι α β : Type} [TopologicalSpace α] {i₁ i₂ i j : ι} {a : α} {s t : Set α}

structure Bunch (ι α β : Type) [TopologicalSpace α] where
  F : ι → α → β
  S : ι → Set α
  cov (z : α × β) : ∃ i, z.1 ∈ S i ∧ F i z.1 = z.2
  cmp i j : IsOpen { a ∈ S i ∩ S j | F i a = F j a }

instance : CoeFun (Bunch ι α β) (λ _ => ι → α → β) := ⟨Bunch.F⟩

namespace Bunch

lemma opn (B : Bunch ι α β) (i : ι) : IsOpen (B.S i) := by simpa using B.cmp i i

def space (_ : Bunch ι α β) := α × β

def idx (B : Bunch ι α β) (z : B.space) := { i | z.1 ∈ B.S i ∧ B i z.1 = z.2 }

def tile (B : Bunch ι α β) (i : ι) (s : Set α) : Set B.space := (λ x => (x, B i x)) '' s

variable {B : Bunch ι α β} {s s₁ s₂ : Set B.space} {z : B.space}

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

def nhd (z : B.space) : Filter B.space := (isBasis z).filter

instance : TopologicalSpace B.space := TopologicalSpace.mkOfNhds nhd

lemma mem_nhd : s ∈ nhd z ↔ ∃ i ∈ B.idx z, ∃ v ∈ 𝓝 z.1, B.tile i v ⊆ s := by
  simp only [nhd, (isBasis z).mem_filter_iff, reaches] ; aesop

theorem eventually_apply_mem {f : α → β} {t : Set β} :
    (∀ᶠ x in 𝓝 a, f x ∈ t) ↔ (∃ s ∈ 𝓝 a, s ⊆ f ⁻¹' t) :=
  eventually_iff_exists_mem

theorem eventually_mem_iff_tile : (∀ᶠ b in 𝓝 a, (b, B j b) ∈ s) ↔ (∃ v ∈ 𝓝 a, tile B j v ⊆ s) := by
  simp [tile, ← eventually_apply_mem]

lemma nhd_of_mem_tile {s : Set α} (hi : i ∈ B.idx z) (hs : s ∈ 𝓝 z.1) : B.tile i s ∈ nhd z := by
  simpa only [nhd, IsBasis.mem_filter_iff] using ⟨(i, s), ⟨hi, hs⟩, subset_rfl⟩

lemma mem_nhd_open (h : s ∈ nhd z) : ∃ i ∈ B.idx z, ∃ v ∈ 𝓝 z.1, IsOpen v ∧ B.tile i v ⊆ s := by
  obtain ⟨i, hi1, t, hi3, hi4⟩ := mem_nhd.1 h
  obtain ⟨s', ⟨h1, h2⟩, h3⟩ := nhds_basis_opens' z.1 |>.mem_iff.1 hi3
  exact ⟨i, hi1, s', h1, h2, tile_mono h3 |>.trans hi4⟩

theorem pure_le (z : B.space) : pure z ≤ nhd z := by
  intro s hs
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := mem_nhd.1 hs
  exact hi4 ⟨z.1, mem_of_mem_nhds hi3, by simp [hi1.2]⟩

theorem nhd_is_nhd (a : space B) (s : Set (space B)) (hs : s ∈ nhd a) :
    ∃ t ∈ nhd a, t ⊆ s ∧ ∀ b ∈ t, s ∈ nhd b := by
  obtain ⟨i, hi1, s₀, hi2, hi3, hi4⟩ := mem_nhd_open hs
  refine ⟨B.tile i (s₀ ∩ B.S i), ?_, ?_, ?_⟩
  · simp [mem_nhd] -- TODO separate out
    refine ⟨i, hi1, _, ?_, subset_rfl⟩
    apply Filter.inter_mem hi2
    apply B.opn i |>.mem_nhds
    exact hi1.1
  · exact tile_mono (inter_subset_left _ _) |>.trans hi4
  · rintro b ⟨c, hb1, rfl⟩
    refine mem_of_superset ?_ hi4
    refine nhd_of_mem_tile ⟨?_, rfl⟩ ?_
    · exact inter_subset_right _ _ hb1
    · exact hi3.mem_nhds <| inter_subset_left _ _ hb1

lemma mem_nhds_iff : s ∈ 𝓝 z ↔ ∃ i ∈ B.idx z, ∀ᶠ a in 𝓝 z.1, (a, B i a) ∈ s := by
  simp [nhds_mkOfNhds _ _ pure_le nhd_is_nhd, mem_nhd, tile, idx, and_assoc, eventually_apply_mem]

end Bunch
