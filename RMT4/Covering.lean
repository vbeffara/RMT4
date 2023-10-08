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
def FF (Λ : LocalPrimitiveOn U f) (z : U) (a : U × ℂ) (w : ℂ) : ℂ := Λ.F z w + (a.2 - Λ.F z a.1)

@[simp] lemma FF_self : LocalPrimitiveOn.FF Λ z (w, u) w = u := by simp [FF]

@[simp] lemma FF_self' : LocalPrimitiveOn.FF Λ z w w.1 = w.2 := FF_self

lemma FF_deriv (hw : w ∈ Λ.S z) : HasDerivAt (Λ.FF z a) (f w) w := Λ.der z w hw |>.add_const _

def map (Λ : LocalPrimitiveOn U f) (z : U) (w : U × ℂ) : holo_covering Λ := (w.1, Λ.FF z (z, w.2) w.1)

/-- The shear transformation. `Φ z` maps a point `(u, v)` to `(u, w)` where `w` is the value above
  `z` of the translate of `F z` that goes through `(u, v)`, and `(Φ z).symm` maps `(u, w)` to
  `(u, v)` where `v` is the value above `u` of the translate of `F` that goes through `(z, v)`. -/

def Φ (Λ : LocalPrimitiveOn U f) (z : U) : holo_covering Λ ≃ U × ℂ where
  toFun w := (w.1, Λ.FF z w z)
  invFun w := (w.1, Λ.FF z (z, w.2) w.1)
  left_inv _ := by simp [FF]
  right_inv _ := by simp [FF]

@[simp] lemma Φ_first : (Λ.Φ z w).1 = w.1 := rfl

@[simp] lemma Φ_symm_first : ((Λ.Φ z).symm w).1 = w.1 := rfl

@[simp] lemma Φ_self : Λ.Φ a.1 a = a := by simp [Φ]

@[simp] lemma Φ_symm_self : (Λ.Φ a.1).symm a = a := by simp [Φ]

def π (Λ : LocalPrimitiveOn U f) (z : U) : ℂ ≃ p Λ ⁻¹' {z} where
  toFun w := ⟨⟨z, w⟩, rfl⟩
  invFun w := w.val.2
  left_inv _ := rfl
  right_inv := by rintro ⟨w, rfl⟩ ; simp

def ψ (Λ : LocalPrimitiveOn U f) (z : U) : U × ℂ ≃ U × p Λ ⁻¹' {z} :=
  (Equiv.refl _).prodCongr (π Λ z)

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
  Filter.map (λ w => (w, Λ.FF z.1 z w)) (𝓝 z.1)

instance : TopologicalSpace (holo_covering Λ) := TopologicalSpace.mkOfNhds nhd

lemma mem_nhd_1 {z : holo_covering Λ} : s ∈ nhd z ↔ ∀ᶠ u in 𝓝 z.1, ⟨u, Λ.FF z.1 z u⟩ ∈ s :=
  by rfl

lemma mem_nhd_2 {z : holo_covering Λ} : s ∈ nhd z ↔ ∀ᶠ u in 𝓝 z.1, (Λ.Φ z.1).symm (u, z.2) ∈ s :=
  mem_nhd_1

lemma mem_nhd {z : holo_covering Λ} : s ∈ nhd z ↔ ∃ t ∈ 𝓝 z.1, (λ w => ⟨w, Λ.FF z.1 z w⟩) '' t ⊆ s := by
  simpa [mem_nhd_1] using eventually_iff_exists_mem

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
  refine λ s hs => (mem_image _ _ _).2 ⟨a.1, mem_of_mem_nhds hs, ?_⟩
  simp [LocalPrimitiveOn.map]

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

lemma eqOn_F {x y : holo_covering Λ} {s : Set ℂ} (hs : IsOpen s) (hs' : IsPreconnected s)
    (hsx : s ⊆ Λ.S x.1) (hsy : s ⊆ Λ.S y.1) (hys : y.1.1 ∈ s) :
    EqOn (Λ.F x.1 · + (y.2 - Λ.F x.1 y.1)) (Λ.F y.1 · + (y.2 - Λ.F y.1 y.1)) s := by
  have l1 (w) (hw : w ∈ s) : HasDerivAt (Λ.F x.1 · + (y.2 - Λ.F x.1 ↑y.1)) (f w) w :=
    Λ.der x.1 w (hsx hw) |>.add_const _
  have l2 (w) (hw : w ∈ s) : HasDerivAt (Λ.F y.1 · + (y.2 - Λ.F y.1 ↑y.1)) (f w) w :=
    Λ.der y.1 w (hsy hw) |>.add_const _
  exact @IsPreconnected.apply_eq_of_hasDeriv_eq ℂ _ f (Λ.F x.1 · + (y.2 - Λ.F x.1 y.1))
    (Λ.F y.1 · + (y.2 - Λ.F y.1 y.1)) y.1 s hs' hs hys l1 l2 (by ring)

lemma eqOn_FF {x y : holo_covering Λ} {s : Set ℂ} (hs' : IsPreconnected s)
    (hs : IsOpen s) (hsx : s ⊆ Λ.S x.1) (hsy : s ⊆ Λ.S y.1) (hys : y.1.1 ∈ s) :
    EqOn (Λ.FF x.1 y) (Λ.FF y.1 y) s :=
  λ _ hws => eqOn_F hs hs' hsx hsy hys hws

lemma eqOn_map (hU : IsOpen U) {s : Set U} (hs : IsPreconnected s) (hs2 : IsOpen s)
    {x y : holo_covering Λ} (hy : y ∈ (Λ.map x.1 ⟨·, x.2⟩) '' s) (hs3 : val '' s ⊆ Λ.S x.1)
    (hs4 : val '' s ⊆ Λ.S y.1) : EqOn (Λ.map x.1 ⟨·, x.2⟩) (Λ.map y.1 ⟨·, y.2⟩) s := by
  let s₀ : Set ℂ := val '' s
  have hs₀ : IsPreconnected s₀ := hs.image _ continuous_subtype_val.continuousOn
  have hs2₀ : IsOpen s₀ := hU.isOpenMap_subtype_val s hs2
  intro z hz
  simp [LocalPrimitiveOn.map]
  obtain ⟨hy1, hy2⟩ := mem_map_iff.1 hy
  have l2 : z.1 ∈ s₀ := by simp [hz]
  rw [Prod.ext_iff] ; simp
  have := eqOn_FF hs₀ hs2₀ hs3 hs4 (mem_image_of_mem val hy1) l2
  rw [← this] ; simp [LocalPrimitiveOn.FF, hy2]

lemma nhd_is_nhd (hU : IsOpen U) (z : holo_covering Λ) :
    ∀ S ∈ nhd z, ∃ T ∈ nhd z, T ⊆ S ∧ ∀ a ∈ T, S ∈ nhd a := by
  have C := hU.locallyConnectedSpace
  intro S hS
  obtain ⟨s, hs1, hs3, hs2⟩ := mem_nhd' hS
  obtain ⟨t, ht1, ht2, ht3, _⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C z.1 s hs1
  refine ⟨(λ w => (w, Λ.FF z.1 z w)) '' t, image_mem_map (ht2.mem_nhds ht3), (image_subset _ ht1).trans hs2, ?_⟩
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
      simp [LocalPrimitiveOn.FF]
      sorry
    · exact image_subset _ (l2.trans (inter_subset_left _ _ |>.trans ht1)) |>.trans hs3
    · simpa only [image_subset_iff] using λ _ hx => (inter_subset_right _ _ (l2 hx))
  apply hs2
  simp
  exact ⟨w, w.2, ht1 (l2 hw).1, key⟩

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
    simp [hx, LocalPrimitiveOn.map]

theorem toto_1 (hU : IsOpen U) (hx : x ∈ (T_LocalEquiv Λ z).source) :
    (T_LocalEquiv Λ z).source ∈ 𝓝 x :=
  isOpen_source Λ hU z |>.mem_nhds hx

example (hU : IsOpen U) : ContinuousAt (T_LocalEquiv Λ z.1) z := by
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
  simp [T_LocalEquiv, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, LocalPrimitiveOn.π,
    LocalPrimitiveOn.Φ, LocalPrimitiveOn.L, LocalPrimitiveOn.map, LocalPrimitiveOn.FF, hz]
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
