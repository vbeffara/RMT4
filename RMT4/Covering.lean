import Mathlib
import RMT4.pintegral
import RMT4.LocallyConstant

open Topology Filter Metric TopologicalSpace Set

variable {U : Set ℂ}

def holo_covering (_ : HasLocalPrimitiveOn U f) := U × ℂ

def LocalPrimitiveOn.map (Λ : LocalPrimitiveOn U f) (z : U) (v : ℂ) : U → holo_covering ⟨Λ⟩ :=
  λ w => (w, v + (Λ.F z w - Λ.F z z))

namespace holo_covering

def nhd (Λ : LocalPrimitiveOn U f) (z : holo_covering ⟨Λ⟩) : Filter (holo_covering ⟨Λ⟩) :=
  Filter.map (Λ.map z.1 z.2) (𝓝 z.1)

instance : TopologicalSpace (holo_covering h) := TopologicalSpace.mkOfNhds (nhd h.some)

lemma mem_nhd (Λ : LocalPrimitiveOn U f) (z : holo_covering ⟨Λ⟩) (s : Set (holo_covering ⟨Λ⟩)) :
    s ∈ nhd Λ z ↔ ∃ t ∈ 𝓝 z.1, Λ.map z.1 z.2 '' t ⊆ s := by
  rw [nhd, mem_map_iff_exists_image]

lemma mem_nhd' (Λ : LocalPrimitiveOn U f) (z : holo_covering ⟨Λ⟩) (s : Set (holo_covering ⟨Λ⟩)) :
    s ∈ nhd Λ z ↔ ∀ᶠ w in 𝓝 z.1, Λ.map z.1 z.2 w ∈ s := by
    simp only [eventually_iff, nhd] ; rfl

lemma pure_le_nhd {h : HasLocalPrimitiveOn U f} : pure ≤ nhd (h.some) := by
  intro a
  simp only [nhd, le_map_iff, mem_pure]
  intro s hs
  apply (mem_image _ _ _).2 ⟨a.1, mem_of_mem_nhds hs, by simp [LocalPrimitiveOn.map]⟩

lemma mem_map_iff (Λ : LocalPrimitiveOn U f) (s : Set U) (x y : holo_covering ⟨Λ⟩) :
    y ∈ Λ.map x.1 x.2 '' s ↔ y.1 ∈ s ∧ y = Λ.map x.1 x.2 y.1 where
  mp h := by
    obtain ⟨z, hz, rfl⟩ := (mem_image _ _ _).1 h
    simp [LocalPrimitiveOn.map, hz]
  mpr h := (mem_image _ _ _).2 ⟨y.1, h.1, h.2.symm⟩

lemma main (Λ : LocalPrimitiveOn U f) (s : Set U) (hs : IsConnected s) (hs2 : IsOpen s)
    (x y : holo_covering ⟨Λ⟩) (hy : y ∈ Λ.map x.1 x.2 '' s) :
    EqOn (Λ.map x.1 x.2) (Λ.map y.1 y.2) s := by
  intro u hu
  sorry

lemma nhd_is_nhd [C : LocallyConnectedSpace U] (Λ : LocalPrimitiveOn U f) (z : holo_covering ⟨Λ⟩) :
    ∀ S ∈ nhd Λ z, ∃ T ∈ nhd Λ z, T ⊆ S ∧ ∀ a ∈ T, S ∈ nhd Λ a := by
  intro S hS
  obtain ⟨s, hs1, hs2⟩ := (mem_nhd _ _ _ ).1 hS
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C z.1 s hs1
  refine ⟨Λ.map z.1 z.2 '' t, image_mem_map (ht2.mem_nhds ht3), (image_subset _ ht1).trans hs2, ?_⟩
  intro a ha
  refine (mem_nhd _ _ _).2 ⟨t, ht2.mem_nhds ((mem_map_iff _ _ _ _).1 ha).1, ?_⟩
  intro u hu
  obtain ⟨x, hx1, rfl⟩ := (mem_image _ _ _).1 hu
  rw [← main Λ t ht4 ht2 z a ha hx1]
  exact hs2 (mem_image_of_mem (Λ.map z.1 z.2) (ht1 hx1))

def p (h : HasLocalPrimitiveOn U f) : holo_covering h → U := λ z => z.1

lemma discreteTopology [LocallyConnectedSpace U] (h : HasLocalPrimitiveOn U f) (z : U) :
    DiscreteTopology ↑(p h ⁻¹' {z}) := by
  let Λ := h.some
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_mkOfNhds, nhds_induced, p]
  rintro ⟨z, u⟩ rfl
  rw [nhds_mkOfNhds _ _ pure_le_nhd (nhd_is_nhd _)]
  refine ⟨Λ.map z u '' U.restrict (Λ.S z), ?_, ?_⟩
  · apply image_mem_map
    simp only [nhds_induced]
    exact ⟨_, Λ.nhd z, by rfl⟩
  · rintro ⟨⟨a₁, ha₁⟩, a₂⟩ rfl
    simp [LocalPrimitiveOn.map]
    rintro z hz _ h2
    obtain ⟨h3, h4⟩ := Prod.ext_iff.1 h2
    simp at h3 h4
    simp [LocalPrimitiveOn.map, h3] at h4
    rw [← h4]

theorem isCoveringMap [LocallyConnectedSpace U] (h : HasLocalPrimitiveOn U f) :
    IsCoveringMap (p h) := by
  intro z
  refine ⟨discreteTopology h z, ?_⟩
  sorry

end holo_covering