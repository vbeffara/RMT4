import Mathlib
import RMT4.pintegral
import RMT4.LocallyConstant
import RMT4.to_mathlib

/-
TODO:
- use `Filter.map_congr` for invariance under base point change
- use `Filter.eventually_map` to write everything in terms of filters?
- rewrite `nhd_is_nhd` aas `∀ y ∈ Λ.S x, ∀ᶠ z in 𝓝 y, Λ.FF x (y, Λ.F x y) z = Λ.FF y whatever z`
- use all the functions rather than the `Λ.F x`
-/

open Topology Filter Metric TopologicalSpace Set Subtype

variable {U : Set ℂ} {f : ℂ → ℂ} {Λ : LocalPrimitiveOn U f}

def holo_covering (_ : LocalPrimitiveOn U f) := U × ℂ

abbrev p (Λ : LocalPrimitiveOn U f) : holo_covering Λ → U := Prod.fst

namespace LocalPrimitiveOn

/-- The shift of `Λ.F z` going through a -/
def FF (Λ : LocalPrimitiveOn U f) (z : U) (a : U × ℂ) (w : U) : ℂ := Λ.F z w + (a.2 - Λ.F z a.1)

@[simp] lemma FF_self : LocalPrimitiveOn.FF Λ z (w, u) w = u := by simp [FF]

@[simp] lemma FF_self' : LocalPrimitiveOn.FF Λ z w w.1 = w.2 := FF_self

def map₀ (Λ : LocalPrimitiveOn U f) (z : U) (v : ℂ) (w : ℂ) : ℂ := v + (Λ.F z w - Λ.F z z)

example (w : U) : Λ.map₀ z v w = Λ.FF z (z, v) w := by simp [FF, map₀] ; ring

lemma der₀ (hw : w ∈ Λ.S z) : HasDerivAt (Λ.map₀ z v) (f w) w := by
  simpa using hasDerivAt_const _ _ |>.add (Λ.der z w hw |>.sub<| hasDerivAt_const _ _)

def map (Λ : LocalPrimitiveOn U f) (z : U) (w : U × ℂ) : holo_covering Λ :=
  (w.1, Λ.FF z (z, w.2) w.1)

def comap (Λ : LocalPrimitiveOn U f) (z : U) (w : holo_covering Λ) : U × ℂ :=
  (w.1, Λ.FF z w z)

@[simp] lemma map_self (a : holo_covering Λ) : Λ.map a.1 a = a := by simp [map]

@[simp] lemma comap_self (a : U × ℂ) : Λ.comap a.1 a = a := by simp [comap]

@[simp] lemma map_first : (Λ.map x z).1 = z.1 := rfl

@[simp] lemma comap_first : (Λ.comap x z).1 = z.1 := rfl

@[simp] lemma map_cancel : Λ.comap z (Λ.map z u) = u := by simp [map, comap, FF]

@[simp] lemma map_cancel' : Λ.map z (Λ.comap z w) = w := by simp [map, comap, FF]

def Φ (Λ : LocalPrimitiveOn U f) (z : U) : holo_covering Λ ≃ U × ℂ where
  toFun := Λ.comap z
  invFun := Λ.map z
  left_inv _ := map_cancel'
  right_inv _ := map_cancel

def π (Λ : LocalPrimitiveOn U f) (z : U) : ℂ ≃ p Λ ⁻¹' {z} where
  toFun w := ⟨⟨z, w⟩, rfl⟩
  invFun w := w.val.2
  left_inv _ := rfl
  right_inv := by rintro ⟨w, rfl⟩ ; simp

def ψ (Λ : LocalPrimitiveOn U f) (z : U) : U × ℂ ≃ U × p Λ ⁻¹' {z} :=
  Equiv.prodCongr (Equiv.refl _) (π Λ z)

def Ψ (Λ : LocalPrimitiveOn U f) (z : U) : holo_covering Λ ≃ U × p Λ ⁻¹' {z} :=
  (Φ Λ z).trans (ψ Λ z)

def L (Λ : LocalPrimitiveOn U f) (z : U) : LocalEquiv (holo_covering Λ) (U × p Λ ⁻¹' {z}) :=
  (Ψ Λ z).toLocalEquiv

lemma L_image : (L Λ z).IsImage ((val ⁻¹' Λ.S z) ×ˢ univ) ((val ⁻¹' Λ.S z) ×ˢ univ) := by
  intro ⟨z₁, z₂⟩ ; rw [mem_prod, mem_prod] ; simp [L, Ψ, ψ, Φ]

def _root_.holo_covering.T_LocalEquiv (Λ : LocalPrimitiveOn U f) (z : U) :
    LocalEquiv (holo_covering Λ) (U × p Λ ⁻¹' {z}) := L_image.restr

end LocalPrimitiveOn

namespace holo_covering

def nhd (z : holo_covering Λ) : Filter (holo_covering Λ) :=
  Filter.map (Λ.map z.1 ⟨·, z.2⟩) (𝓝 z.1)

instance : TopologicalSpace (holo_covering Λ) := TopologicalSpace.mkOfNhds nhd

lemma mem_nhd : s ∈ nhd z ↔ ∃ t ∈ 𝓝 z.1, (Λ.map z.1 ⟨·, z.2⟩) '' t ⊆ s := by
  rw [nhd, mem_map_iff_exists_image]

lemma mem_nhd' (h : s ∈ nhd z) : ∃ t ∈ 𝓝 z.1, val '' t ⊆ Λ.S z.1 ∧ (Λ.map z.1 ⟨·, z.2⟩) '' t ⊆ s := by
  obtain ⟨t, l1, l2⟩ := mem_nhd.1 h
  refine ⟨t ∩ val ⁻¹' Λ.S z.1, ?_, ?_, ?_⟩
  · exact Filter.inter_mem l1 <| IsOpen.mem_nhds (isOpen_induced (Λ.opn z.1)) <| Λ.mem z.1
  · exact image_inter_subset _ _ _ |>.trans<| inter_subset_right _ _ |>.trans<|
      image_preimage_subset _ _
  · exact image_subset (Λ.map z.1 ⟨·, z.2⟩) (inter_subset_left _ _) |>.trans l2

lemma pure_le_nhd : pure ≤ nhd (Λ := Λ) := by
  intro a
  simp only [nhd, le_map_iff, mem_pure]
  exact λ s hs => (mem_image _ _ _).2 ⟨a.1, mem_of_mem_nhds hs, Λ.map_self _⟩

lemma mem_map_iff {y : holo_covering Λ} :
    y ∈ (Λ.map u ⟨·, v⟩) '' s ↔ y.1 ∈ s ∧ y.2 = Λ.FF u ⟨u, v⟩ y.1 where
  mp h := by
    obtain ⟨z, hz, rfl⟩ := (mem_image _ _ _).1 h
    simp [LocalPrimitiveOn.map, hz, LocalPrimitiveOn.FF]
  mpr h := by
    refine (mem_image _ _ _).2 ⟨y.1, h.1, ?_⟩
    simp [LocalPrimitiveOn.map, LocalPrimitiveOn.FF, ← h.2]
    apply Prod.ext <;> simp [LocalPrimitiveOn.map, h.2] ; ring_nf
    simp [LocalPrimitiveOn.FF]

lemma image_eq_of_mem_map {s : Set U} {x y : holo_covering Λ} (h : y ∈ (Λ.map x.1 ⟨·, x.2⟩) '' s) :
    y.2 = Λ.FF x.1 x y.1 :=
  (mem_map_iff.1 h).2

lemma eqOn_map₀ (hs : IsPreconnected s) (hs2 : IsOpen s) {x y : holo_covering Λ}
    (hxy : y.2 = Λ.map₀ x.1 x.2 y.1) (hy : y.1.1 ∈ s) (hsx : s ⊆ Λ.S x.1) (hsy : s ⊆ Λ.S y.1) :
    EqOn (Λ.map₀ x.1 x.2) (Λ.map₀ y.1 y.2) s := by
  apply hs.apply_eq_of_hasDeriv_eq hs2 hy (λ z hz => Λ.der₀ (hsx hz)) (λ z hz => Λ.der₀ (hsy hz))
  simp [LocalPrimitiveOn.map₀, hxy]

lemma eqOn_map (hU : IsOpen U) (hs : IsPreconnected s) (hs2 : IsOpen s)
    {x y : holo_covering Λ} (hy : y ∈ (Λ.map x.1 ⟨·, x.2⟩) '' s) (hs3 : val '' s ⊆ Λ.S x.1)
    (hs4 : val '' s ⊆ Λ.S y.1) : EqOn (Λ.map x.1 ⟨·, x.2⟩) (Λ.map y.1 ⟨·, y.2⟩) s := by
  let s₀ : Set ℂ := val '' s
  have hs₀ : IsPreconnected s₀ := hs.image _ continuous_subtype_val.continuousOn
  have hs2₀ : IsOpen s₀ := hU.isOpenMap_subtype_val s hs2
  have key : EqOn (Λ.map₀ x.1 x.2) (Λ.map₀ y.1 y.2) s₀ := by
    obtain ⟨hy1, hy2⟩ := mem_map_iff.1 hy
    refine eqOn_map₀ hs₀ hs2₀ ?_ (mem_image_of_mem val hy1) hs3 hs4
    convert hy2
    simp [LocalPrimitiveOn.map₀, LocalPrimitiveOn.FF] ; ring
  simp [LocalPrimitiveOn.map₀] at key
  intro z hz
  simp [LocalPrimitiveOn.map, LocalPrimitiveOn.FF]
  specialize key (mem_image_of_mem val hz) ; ring_nf at key ⊢
  rw [key]

lemma nhd_is_nhd (hU : IsOpen U) (z : holo_covering Λ) :
    ∀ S ∈ nhd z, ∃ T ∈ nhd z, T ⊆ S ∧ ∀ a ∈ T, S ∈ nhd a := by
  have C := hU.locallyConnectedSpace
  intro S hS
  obtain ⟨s, hs1, hs3, hs2⟩ := mem_nhd' hS
  obtain ⟨t, ht1, ht2, ht3, _⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C z.1 s hs1
  refine ⟨(Λ.map z.1 ⟨·, z.2⟩) '' t, image_mem_map (ht2.mem_nhds ht3), (image_subset _ ht1).trans hs2, ?_⟩
  intro a ha
  have l1 : t ∩ val ⁻¹' Λ.S a.1 ∈ 𝓝 a.1 := by
    apply Filter.inter_mem
    · exact ht2.mem_nhds <| (mem_map_iff.1 ha).1
    · exact isOpen_induced (Λ.opn a.1) |>.mem_nhds (Λ.mem a.1)
  obtain ⟨t₀, l2, l3, l4, l5⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C a.1 _ l1
  refine mem_nhd.2 ⟨t₀, l3.mem_nhds l4, ?_⟩
  intro u hu
  obtain ⟨w, hw, rfl⟩ := (mem_image _ _ _).1 hu
  have key : Λ.map z.1 (w, z.2) = Λ.map a.1 (w, a.2) := by
    refine eqOn_map hU l5.isPreconnected l3 ?_ ?_ ?_ hw
    · simp [mem_map_iff, l4, image_eq_of_mem_map ha, and_self, LocalPrimitiveOn.map]
      sorry
    · exact image_subset _ (l2.trans (inter_subset_left _ _ |>.trans ht1)) |>.trans hs3
    · simpa only [image_subset_iff] using λ _ hx => (inter_subset_right _ _ (l2 hx))
  exact hs2 <| key ▸ mem_image_of_mem _ (ht1 (l2 hw).1)

lemma discreteTopology (hU : IsOpen U) (z : U) : DiscreteTopology ↑(p Λ ⁻¹' {z}) := by
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_mkOfNhds, nhds_induced, p]
  rintro ⟨z, u⟩ rfl
  rw [nhds_mkOfNhds _ _ pure_le_nhd (nhd_is_nhd hU)]
  refine ⟨(Λ.map z ⟨·, u⟩) '' (val ⁻¹' (Λ.S z)), ?_, ?_⟩
  · apply image_mem_map
    simpa only [nhds_induced] using ⟨_, Λ.nhd z, by rfl⟩
  · simp only [mem_map_iff]
    rintro ⟨a₁, a₂⟩ rfl ⟨_, h2⟩
    simp at h2
    simp [h2]

lemma nhds_eq_nhd (hU : IsOpen U) (z : holo_covering Λ) : 𝓝 z = nhd z :=
  nhds_mkOfNhds nhd z pure_le_nhd (nhd_is_nhd hU)

lemma nhds_iff_eventually (hU : IsOpen U) (z : holo_covering Λ) {s : Set (holo_covering Λ)} :
    s ∈ 𝓝 z ↔ ∀ᶠ x in 𝓝 z.1, Λ.map z.1 (x, z.2) ∈ s := by
  rw [nhds_eq_nhd hU, nhd] ; rfl

theorem isOpen_source (Λ : LocalPrimitiveOn U f) (hU : IsOpen U) (z : ↑U) :
    IsOpen (T_LocalEquiv Λ z).source := by
  simp only [isOpen_iff_eventually, T_LocalEquiv, eventually_mem_set]
  intro ⟨a₁, a₂⟩ ha
  simp [LocalPrimitiveOn.L] at ha
  rw [mem_prod] at ha ; simp at ha
  simp only [nhds_eq_nhd hU, nhd, nhds_induced, mem_map, mem_comap]
  refine ⟨Λ.S z, (Λ.opn z) |>.mem_nhds ha, ?_⟩
  exact λ x hx => by
    simp at hx
    simp [LocalPrimitiveOn.L]
    rw [mem_prod]
    simp [hx]

theorem toto_1 (hU : IsOpen U) (hx : x ∈ (T_LocalEquiv Λ z).source) :
    (T_LocalEquiv Λ z).source ∈ 𝓝 x :=
  isOpen_source Λ hU z |>.mem_nhds hx

example (hU : IsOpen U) : ContinuousAt (T_LocalEquiv Λ z.1).toFun z := by
  intro s hs
  simp [T_LocalEquiv, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, mem_nhds_prod_iff, LocalPrimitiveOn.L] at hs
  obtain ⟨u, hu, v, hv, huv⟩ := hs
  simp [nhds_induced] at hu
  obtain ⟨u', hu', hu'2⟩ := hu
  refine Filter.mem_of_superset ?_ huv
  simp [nhds_eq_nhd hU, nhd, nhds_induced]
  refine ⟨u', hu', ?_⟩
  apply hu'2.trans
  intro z' hz
  have := mem_of_mem_nhds hv
  simp [LocalPrimitiveOn.π, LocalPrimitiveOn.Φ, p] at this
  simp [T_LocalEquiv, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, LocalPrimitiveOn.π, LocalPrimitiveOn.Φ, LocalPrimitiveOn.L, hz]
  exact this

def T_LocalHomeomorph (Λ : LocalPrimitiveOn U f) (hU : IsOpen U) (z : U) :
    LocalHomeomorph (holo_covering Λ) (U × p Λ ⁻¹' {z}) where
  toLocalEquiv := T_LocalEquiv Λ z
  open_source := isOpen_source Λ hU z
  open_target := by
    simp [T_LocalEquiv, LocalPrimitiveOn.L]
    exact IsOpen.prod (isOpen_induced (Λ.opn z)) isOpen_univ
  continuous_toFun := sorry
  continuous_invFun := sorry

def T (Λ : LocalPrimitiveOn U f) (hU : IsOpen U) (z : U) : Trivialization (p Λ ⁻¹' {z}) (p Λ) where
  toLocalHomeomorph := T_LocalHomeomorph Λ hU z
  baseSet := val ⁻¹' Λ.S z
  open_baseSet := isOpen_induced (Λ.opn z)
  source_eq := by simp [T_LocalHomeomorph, T_LocalEquiv, LocalPrimitiveOn.L] ; ext ; simp
  target_eq := by simp [T_LocalHomeomorph, T_LocalEquiv, LocalPrimitiveOn.L]
  proj_toFun x _:= rfl

theorem isCoveringMap (hU : IsOpen U) : IsCoveringMap (p Λ) :=
  λ z => ⟨discreteTopology hU z, T Λ hU z, Λ.mem z⟩

end holo_covering
