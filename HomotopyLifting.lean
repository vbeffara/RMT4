/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.Covering
import Mathlib.Topology.UnitInterval
/-!

# The Homotopy lifting property of covering maps

Currently, this file only proves uniqueness of lifting, not existence,
but under some more general conditions than covering maps, in order to
apply to situations such as the monodromy theorem for analytic continuations.
-/

open Topology unitInterval

variable {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  {p : C(E,X)}

/-- If every `e : E` has an open neighborhood on which `p : E → X` is injective such that
  `p⁻¹(p(U))\U` is also open, and if `A` is a connected space,
  then two lifts `g₁,g₂ : A → E` of a map `f : A → X` are equal if they agree at one point. -/
theorem ContinuousMap.eq_of_comp_eq [PreconnectedSpace A]
    (hp : ∀ e : E, ∃ U, e ∈ U ∧ IsOpen U ∧ U.InjOn p ∧ IsOpen (p ⁻¹' (p '' U) \ U))
    (g₁ g₂ : C(A,E)) (he : p.comp g₁ = p.comp g₂)
    (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ := by
  have := IsClopen.eq_univ (s := {a | g₁ a = g₂ a}) ⟨?_, ?_⟩ ⟨a, ha⟩
  · ext a; apply this.symm ▸ Set.mem_univ a
  /- Since A is connected and s := {a | g₁ a = g₂ a} inhabited by a,
     we just need to show that s is open and closed. -/
  · refine isOpen_iff_mem_nhds.mpr (fun a ha ↦ mem_nhds_iff.mpr ?_)
    /- Given a point a where g₁ and g₂ agree,
       take an open neighborhood U of g₁(a) = g₂(a) on which p is injective.
       Then g₁ and g₂ agree on the open neighborhood g₁⁻¹(U) ∩ g₂⁻¹(U) of a. -/
    obtain ⟨U, haU, hoU, hi, -⟩ := hp (g₁ a)
    exact ⟨g₁ ⁻¹' U ∩ g₂ ⁻¹' U, fun a' ha ↦ hi ha.1 ha.2 (FunLike.congr_fun he a'),
      (g₁.2.isOpen_preimage _ hoU).inter (g₂.2.isOpen_preimage _ hoU), haU, ha.subst haU⟩
  · simp_rw [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_nhds_iff]
    intro a ha
    /- Given a point a where g₁ and g₂ doesn't agree,
       take an open neighborhood U of g₁(a) on which p is injective such that p⁻¹(p(U))\U is open.
       Then g₁ and g₂ doesn't agree on any point
         in the neighborhood g₁⁻¹(U) ∩ g₂⁻¹(p⁻¹(p(U))\U) of a. -/
    obtain ⟨U, hU₁, hoU, hi, compl_open⟩ := hp (g₁ a)
    have := FunLike.congr_fun he a
    refine ⟨_, fun a' ha' he ↦ ha'.2.2 (he ▸ ha'.1), (g₁.continuous.isOpen_preimage _ hoU).inter
      (g₂.continuous.isOpen_preimage _ compl_open), hU₁, ?_, fun hU₂ ↦ ha (hi hU₁ hU₂ this)⟩
    apply this ▸ Set.mem_image_of_mem p hU₁

theorem lebesgue_number_lemma_unitInterval {ι} {c : ι → Set I} (hc₁ : ∀ i, IsOpen (c i))
    (hc₂ : Set.univ ⊆ ⋃ i, c i) : ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧
      (∀ n, ∃ i, Set.Icc (t n) (t <| n + 1) ⊆ c i) ∧ ∃ n, ∀ m ≥ n, t m = 1 := by
  obtain ⟨δ, δ_pos, ball_subset⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc₁ hc₂
  refine ⟨fun n ↦ Set.projIcc 0 1 zero_le_one (n * (δ/2)), ?_, fun n m hnm ↦ ?_, fun n ↦ ?_, ?_⟩
  · dsimp only; rw [Nat.cast_zero, zero_mul, Set.projIcc_left]; rfl
  · apply Set.monotone_projIcc
    rw [mul_le_mul_right (div_pos δ_pos zero_lt_two)]
    exact_mod_cast hnm
  · obtain ⟨i, hsub⟩ := ball_subset (Set.projIcc 0 1 zero_le_one (n * (δ/2))) trivial
    refine ⟨i, fun x hx ↦ hsub ?_⟩
    rw [Metric.mem_ball]
    apply (abs_eq_self.mpr _).trans_lt
    · apply (sub_le_sub_right _ _).trans_lt
      on_goal 3 => exact hx.2
      refine (max_sub_max_le_max _ _ _ _).trans_lt (max_lt (by rwa [sub_zero]) ?_)
      refine ((le_abs_self _).trans <| abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt ?_ ?_)
      · rwa [sub_self, abs_zero]
      · rw [← sub_mul, Nat.cast_succ, add_sub_cancel', one_mul, abs_lt]
        constructor <;> linarith only [δ_pos]
    · exact sub_nonneg_of_le hx.1
  · refine ⟨Nat.ceil (δ/2)⁻¹, fun n hn ↦ (Set.projIcc_eq_right zero_lt_one).mpr ?_⟩
    rwa [GE.ge, Nat.ceil_le, inv_pos_le_iff_one_le_mul (div_pos δ_pos zero_lt_two)] at hn

instance : BoundedOrder I := Set.Icc.boundedOrder zero_le_one


--instance {α} [TopologicalSpace α] [Preorder α] [CompactIccSpace α] {a b : α} :
--    CompactIccSpace (Set.Icc a b) := by
  -- closed subset of compact space
  -- Ioo, Ioc, Ico, Iio, etc...


/-- If `p : E → X` is a local homeomorphism, and if `g : I × A → E` is a lift of `f : C(I × A, X)`
  continuous on `{0} × A ∪ I × {a}` for some `a : A`, then there exists a neighborhood `N ∈ 𝓝 a`
  and `g' : I × A → E` continuous on `I × N` that agrees with `g` on `{0} × A ∪ I × {a}`.
  The proof follows Hatcher, Proof of Theorem 1.7, p.30.

  This lemma should also be true for an arbitrary space in place of `I` if `A` is locally connected,
  and if `hp` furthermore satisfies the property in `ContinuousMap.eq_of_comp_eq` which guarantees
  uniqueness and therefore well-definedness on the intersections. -/
lemma IsLocallyHomeomorph.exists_lift_nhds {p : E → X} (hp : IsLocallyHomeomorph p)
    {f : C(I × A, X)} {g : I × A → E} (g_lifts : p ∘ g = f)
    (cont_0 : Continuous (g ⟨0, ·⟩)) (a : A) (cont_a : Continuous (g ⟨·, a⟩)) :
    ∃ N ∈ 𝓝 a, ∃ g' : I × A → E, ContinuousOn g' (Set.univ ×ˢ N) ∧ p ∘ g' = f ∧
      (∀ a, g' (0, a) = g (0, a)) ∧ ∀ t, g' (t, a) = g (t, a) := by
  /- For every `e : E`, we can upgrade `p` to a LocalHomeomorph `q e` around `e`. -/
  choose q mem_source hpq using hp
  obtain ⟨t, t_0, t_mono, t_sub, n_max, h_max⟩ := lebesgue_number_lemma_unitInterval
    (fun e ↦ cont_a.isOpen_preimage _ (q e).open_source)
    (fun t _ ↦ Set.mem_iUnion.mpr ⟨g (t, a), mem_source _⟩)
  suffices : ∀ n, ∃ N, a ∈ N ∧ IsOpen N ∧ ∃ g' : I × A → E, ContinuousOn g' (Set.Icc 0 (t n) ×ˢ N) ∧
    p ∘ g' = f ∧ (∀ a, g' (0, a) = g (0, a)) ∧ ∀ t' ≤ t n, g' (t', a) = g (t', a)
  · obtain ⟨N, haN, N_open, hN⟩ := this n_max
    simp_rw [h_max _ le_rfl] at hN
    refine ⟨N, N_open.mem_nhds haN, ?_⟩; convert hN
    · rw [eq_comm, Set.eq_univ_iff_forall]; exact fun t ↦ ⟨bot_le, le_top⟩
    · rw [imp_iff_right]; exact le_top
  refine Nat.rec ⟨_, Set.mem_univ a, isOpen_univ, g, ?_, g_lifts, fun a ↦ rfl, fun _ _ ↦ rfl⟩
    (fun n ⟨N, haN, N_open, g', cont_g', g'_lifts, g'_0, g'_a⟩ ↦ ?_)
  · refine (cont_0.comp continuous_snd).continuousOn.congr (fun ta ⟨ht, _⟩ ↦ ?_)
    rw [t_0, Set.Icc_self, Set.mem_singleton_iff] at ht; rw [← ta.eta, ht]; rfl
  obtain ⟨e, h_sub⟩ := t_sub n
  have : Set.Icc (t n) (t (n+1)) ×ˢ {a} ⊆ f ⁻¹' (q e).target
  · rintro ⟨t0, a'⟩ ⟨ht, ha⟩
    rw [Set.mem_singleton_iff] at ha; dsimp only at ha
    rw [← g_lifts, hpq e, ha]
    exact (q e).map_source (h_sub ht)
  obtain ⟨u, v, -, v_open, hu, hav, huv⟩ := generalized_tube_lemma isClosed_Icc.isCompact
    isCompact_singleton (f.continuous.isOpen_preimage _ (q e).open_target) this
  classical
  refine ⟨_, ?_, v_open.inter <| (cont_g'.comp (Continuous.Prod.mk <| t n).continuousOn
      fun a ha ↦ ⟨?_, ha⟩).preimage_open_of_open N_open (q e).open_source,
    fun ta ↦ if ta.1 ≤ t n then g' ta else if f ta ∈ (q e).target then (q e).symm (f ta) else g ta,
    ContinuousOn.if (fun ta ⟨⟨_, hav, _, ha⟩, hfr⟩ ↦ ?_) (cont_g'.mono fun ta ⟨hta, ht⟩ ↦ ?_) ?_,
    ?_, fun a ↦ ?_, fun t0 htn1 ↦ ?_⟩
  · refine ⟨Set.singleton_subset_iff.mp hav, haN, ?_⟩
    change g' (t n, a) ∈ (q e).source; rw [g'_a _ le_rfl]
    exact h_sub ⟨le_rfl, t_mono n.le_succ⟩
  · rw [← t_0]; exact ⟨t_mono n.zero_le, le_rfl⟩
  · have ht := Set.mem_setOf.mp (frontier_le_subset_eq continuous_fst continuous_const hfr)
    have : f ta ∈ (q e).target := huv ⟨hu (by rw [ht]; exact ⟨le_rfl, t_mono n.le_succ⟩), hav⟩
    rw [if_pos this]
    apply (q e).injOn (by rw [← ta.eta, ht]; exact ha) ((q e).map_target this)
    rw [(q e).right_inv this, ← hpq e]; exact congr_fun g'_lifts ta
  · rw [(isClosed_le continuous_fst continuous_const).closure_eq] at ht
    exact ⟨⟨hta.1.1, ht⟩, hta.2.2.1⟩
  · simp_rw [not_le]; exact (ContinuousOn.congr ((q e).continuous_invFun.comp f.2.continuousOn
      fun _ h ↦ huv ⟨hu ⟨h.2, h.1.1.2⟩, h.1.2.1⟩)
      fun _ h ↦ if_pos <| huv ⟨hu ⟨h.2, h.1.1.2⟩, h.1.2.1⟩).mono
      (Set.inter_subset_inter_right _ <| closure_lt_subset_le continuous_const continuous_fst)
  · ext ta; rw [Function.comp_apply]; split_ifs with _ hv
    · exact congr_fun g'_lifts ta
    · rw [hpq e, (q e).right_inv hv]
    · exact congr_fun g_lifts ta
  · rw [← g'_0]; exact if_pos bot_le
  · dsimp only; split_ifs with htn hf
    · exact g'_a t0 htn
    · apply (q e).injOn ((q e).map_target hf) (h_sub ⟨le_of_not_ge htn, htn1⟩)
      rw [(q e).right_inv hf, ← hpq e]; exact (congr_fun g_lifts _).symm
    · rfl

lemma IsLocallyHomeomorph.continuous_lift {p : E → X} (loc_homeo : IsLocallyHomeomorph p)
    (hp : ∀ e : E, ∃ U, e ∈ U ∧ IsOpen U ∧ U.InjOn p ∧ IsOpen (p ⁻¹' (p '' U) \ U))
    {f : C(I × A, X)} {g : I × A → E} (g_lifts : p ∘ g = f)
    (cont_0 : Continuous (g ⟨0, ·⟩)) (cont_A : ∀ a, Continuous (g ⟨·, a⟩)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro ⟨t, a⟩
  obtain ⟨N, haN, g', cont_g', g'_lifts, g'_0, -⟩ :=
    loc_homeo.exists_lift_nhds g_lifts cont_0 a (cont_A a)
  refine (cont_g'.congr fun ⟨t, a⟩ ⟨_, ha⟩ ↦ ?_).continuousAt (prod_mem_nhds Filter.univ_mem haN)
  refine FunLike.congr_fun (ContinuousMap.eq_of_comp_eq (p := ⟨_, loc_homeo.continuous⟩) hp
    ⟨_, cont_A a⟩ ⟨_, cont_g'.comp_continuous (Continuous.Prod.mk_left a) (fun _ ↦ ⟨trivial, ha⟩)⟩
    ?_ 0 (g'_0 a).symm) t
  ext t; apply congr_fun (g_lifts.trans g'_lifts.symm)

lemma IsCoveringMap.exists_nhds_clopen {p : E → X} (hp : IsCoveringMap p) (e : E) :
    ∃ U, e ∈ U ∧ IsOpen U ∧ U.InjOn p ∧ IsOpen (p ⁻¹' (p '' U) \ U) := by
  obtain ⟨hd, t, ht⟩ := hp (p e)
  refine ⟨t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e).2}, ⟨by rwa [t.source_eq], rfl⟩, t.continuous_toFun
    |>.preimage_open_of_open t.open_source (continuous_snd.isOpen_preimage _ <| isOpen_discrete _),
    fun e₁ h₁ e₂ h₂ he ↦ t.injOn h₁.1 h₂.1 (Prod.ext ?_ <| h₁.2.trans h₂.2.symm), ?_⟩
  · rwa [t.proj_toFun e₁ h₁.1, t.proj_toFun e₂ h₂.1]
  convert t.continuous_toFun.preimage_open_of_open t.open_source
    (continuous_snd.isOpen_preimage _ <| isOpen_discrete {(t e).2}ᶜ) using 1
  ext e₀
  rw [t.source_eq, Set.image_preimage_inter, Set.preimage_inter, ← Set.inter_diff_distrib_left]
  refine ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, ?_, h.2⟩⟩
  let x := (p e₀, (t e).2); have : x ∈ t.target
  · rw [t.target_eq]; exact ⟨h.1, trivial⟩
  refine ⟨t.invFun (p e₀, (t e).2), (congr_arg Prod.snd <| t.right_inv this).trans rfl, ?_⟩
  rw [← t.proj_toFun]
  exacts [congr_arg Prod.fst (t.right_inv this), t.map_target this]
