import Mathlib.Analysis.Complex.OpenMapping
import RMT4.defs
import RMT4.hurwitz
import RMT4.montel
import RMT4.etape2
import RMT4.has_sqrt

open UniformConvergence Topology Filter Set Metric Function

-- open filter function metric set topological_space complex RMT
-- open_locale uniform_convergence topological_space filter

-- variables {U : set ℂ} {z₀ : ℂ} {r : ℝ}

instance : CompleteSpace (ℂ →ᵤ[compacts U] ℂ) := sorry

namespace RMT

lemma tendsto_iff (hU : IsOpen U) {F : ι → ℂ →ᵤ[compacts U] ℂ} {f : ℂ →ᵤ[compacts U] ℂ} :
    Tendsto F l (𝓝 f) ↔ TendstoLocallyUniformlyOn F f l U := by
  simp [UniformOnFun.tendsto_iff_tendstoUniformlyOn, _root_.compacts]
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).symm

-- `𝓗 U` : holomorphic functions on U

def 𝓗 (U : Set ℂ) := {f : ℂ →ᵤ[compacts U] ℂ | DifferentiableOn ℂ f U}

noncomputable def uderiv (f : ℂ →ᵤ[compacts U] ℂ) : ℂ →ᵤ[compacts U] ℂ := deriv f

lemma IsClosed_𝓗 (hU : IsOpen U) : IsClosed (𝓗 U) := by
  refine isClosed_iff_clusterPt.2 (λ f hf => ?_)
  refine @TendstoLocallyUniformlyOn.differentiableOn _ _ _ _ _ _ _ id f hf ?_ ?_ hU
  { simp [← tendsto_iff hU, Tendsto] }
  { simp [eventually_inf_principal, 𝓗]; exact eventually_of_forall (λ g => id) }

lemma ContinuousOn_uderiv (hU : IsOpen U) : ContinuousOn uderiv (𝓗 U) := by
  rintro f hf
  haveI := nhdsWithin_neBot_of_mem hf
  refine (tendsto_iff hU).2 ?_
  refine TendstoLocallyUniformlyOn.deriv ?_ ?_ hU
  { apply (tendsto_iff hU).1
    exact nhdsWithin_le_nhds }
  { rw [eventually_nhdsWithin_iff]
    apply eventually_of_forall
    intro f hf
    exact hf }

-- `𝓜 U` : holomorphic functions to the unit closed ball

def 𝓜 (U : Set ℂ) := {f ∈ 𝓗 U | MapsTo f U (closedBall (0 : ℂ) 1)}

lemma TotallyBounded_𝓜 (hU : IsOpen U) : TotallyBounded (𝓜 U) := by
  suffices : UniformlyBoundedOn ((λ f => f) : 𝓜 U → ℂ →ᵤ[compacts U] ℂ) U
  { simpa [Subtype.range_coe_subtype] using montel hU this (λ f => f.2.1) }
  rintro K ⟨hK1, _⟩
  refine ⟨1, zero_lt_one, ?_⟩
  rintro z hz x ⟨⟨f, hf⟩, rfl⟩
  exact hf.2 (hK1 hz)

lemma IsClosed_𝓜 (hU : IsOpen U) : IsClosed (𝓜 U) := by
  suffices : IsClosed {f : ℂ →ᵤ[compacts U] ℂ | MapsTo f U (closedBall 0 1)}
  { exact (IsClosed_𝓗 hU).inter this }
  simp_rw [MapsTo, setOf_forall]
  refine isClosed_biInter (λ z hz => isClosed_ball.preimage ?_)
  exact ((UniformOnFun.uniformContinuous_eval_of_mem ℂ (compacts U)
    (mem_singleton z) ⟨singleton_subset_iff.2 hz, isCompact_singleton⟩).continuous)

lemma IsCompact_𝓜 (hU : IsOpen U) : IsCompact (𝓜 U) :=
  isCompact_of_totallyBounded_isClosed (TotallyBounded_𝓜 hU) (IsClosed_𝓜 hU)

-- `𝓘 U` : holomorphic injections into the unit ball

def 𝓘 (U : Set ℂ) := {f ∈ 𝓜 U | InjOn f U}

lemma 𝓘_nonempty [good_domain U] : (𝓘 U).Nonempty := by
  obtain ⟨u, hu⟩ := nonempty_compl.mpr (good_domain.ne_univ : U ≠ univ)
  let f : ℂ → ℂ := λ z => z - u
  have f_inj : Injective f := λ _ _ h => sub_left_inj.mp h
  have f_hol : DifferentiableOn ℂ f U := differentiableOn_id.sub (differentiableOn_const u)
  have f_noz : ∀ ⦃z : ℂ⦄, z ∈ U -> f z ≠ 0 := λ z hz f0 => hu (sub_eq_zero.mp f0 ▸ hz)

  obtain ⟨g, g_hol, g_sqf⟩ := good_domain.has_sqrt f f_noz f_hol
  obtain ⟨z₀, hz₀⟩ := (good_domain.is_nonempty : U.Nonempty)

  have gU_nhd : g '' U ∈ 𝓝 (g z₀) := by
    have e1 : U ∈ 𝓝 z₀ := good_domain.is_open.mem_nhds hz₀
    have e2 := g_hol.analyticAt e1
    have f_eq_comp := (good_domain.is_open.eventually_mem hz₀).mono g_sqf
    have dg_nonzero : deriv g z₀ ≠ 0 := by
      have e3 := e2.differentiableAt.deriv_eq_deriv_pow_div_pow zero_lt_two f_eq_comp (f_noz hz₀)
      simp [e3, deriv_sub_const]
      intro h
      have := g_sqf hz₀
      rw [Pi.pow_apply, h, zero_pow zero_lt_two] at this
      exact f_noz hz₀ this
    refine e2.eventually_constant_or_nhds_le_map_nhds.resolve_left (λ h => ?_) (image_mem_map e1)
    simp [EventuallyEq.deriv_eq h] at dg_nonzero

  obtain ⟨r, r_pos, hr⟩ := Metric.mem_nhds_iff.mp gU_nhd
  let gg : RMT.embedding U ((closedBall (- g z₀) (r / 2))ᶜ) :=
  { to_fun := g,
    is_diff := g_hol,
    is_inj := λ z₁ hz₁ z₂ hz₂ hgz => f_inj (by simp [g_sqf _, hz₁, hz₂, hgz]),
    maps_to := λ z hz hgz => by {
      apply f_noz hz
      rw [mem_closed_ball_neg_iff_mem_neg_closed_ball] at hgz
      obtain ⟨z', hz', hgz'⟩ := (closedBall_subset_ball (by linarith)).trans hr hgz
      have hzz' : z = z' := f_inj (by simp [g_sqf hz, g_sqf hz', hgz'])
      simpa [hzz', neg_eq_self_iff, g_sqf hz'] using hgz'.symm } }

  let ggg := (embedding.inv _ (by linarith)).comp gg
  refine ⟨ggg.to_fun, ⟨ggg.is_diff, ?_⟩, ggg.is_inj⟩
  exact λ z hz => ball_subset_closedBall (ggg.maps_to hz)

-- `𝓙 U` : the closure of `𝓘 U`, injections and constants

def 𝓙 (U : Set ℂ) := {f ∈ 𝓜 U | InjOn f U ∨ ∃ w : ℂ, EqOn f (λ _ => w) U}

lemma 𝓘_subset_𝓙 : 𝓘 U ⊆ 𝓙 U := λ _ hf => ⟨hf.1, Or.inl hf.2⟩

lemma IsCompact_𝓙 [good_domain U] : IsCompact (𝓙 U) := by
  have hU : IsOpen U := good_domain.is_open
  refine isCompact_of_isClosed_subset (IsCompact_𝓜 hU) ?_ (λ _ hf => hf.1)
  refine isClosed_iff_clusterPt.2 (λ f hf => ?_)
  set l := 𝓝 f ⊓ 𝓟 (𝓙 U)
  haveI : l.NeBot := hf
  obtain ⟨h1, h2⟩ := tendsto_inf.1 (@tendsto_id _ l)
  rw [tendsto_principal] at h2
  refine ⟨(IsClosed_𝓜 hU).mem_of_tendsto h1 (h2.mono (λ _ h => h.1)), ?_⟩
  by_cases ∃ᶠ f in l, InjOn f U
  case pos =>
    refine (hurwitz_inj hU good_domain.is_preconnected ?_ ((tendsto_iff hU).1 h1) h).symm
    filter_upwards [h2] with g hg using hg.1.1
  case neg =>
    obtain ⟨z₀, hz₀⟩ : U.Nonempty := good_domain.is_nonempty
    have : ∀ z ∈ U, Tendsto (eval z) l (𝓝 (f z)) := by
      refine λ z hz => (map_mono inf_le_left).trans ?_
      exact ((UniformOnFun.uniformContinuous_eval_of_mem ℂ (compacts U)
        (mem_singleton z) ⟨singleton_subset_iff.2 hz, isCompact_singleton⟩).continuous).tendsto f
    refine Or.inr ⟨f z₀, λ z hz => tendsto_nhds_unique ((this z hz).congr' ?_) (this z₀ hz₀)⟩
    filter_upwards [not_frequently.1 h, h2] with f hf1 hf2
    obtain ⟨w, hw⟩ := hf2.2.resolve_left hf1
    exact (hw hz).trans (hw hz₀).symm

-- The proof

noncomputable def obs (z₀ : ℂ) (f : ℂ →ᵤ[compacts U] ℂ) : ℝ := ‖deriv f z₀‖

lemma ContinuousOn_obs (hU : IsOpen U) (hz₀ : z₀ ∈ U) : ContinuousOn (obs z₀) (𝓗 U) := by
  have e1 : z₀ ∈ {z₀} := mem_singleton _
  have e2 : {z₀} ∈ compacts U := ⟨singleton_subset_iff.2 hz₀, isCompact_singleton⟩
  apply continuous_norm.comp_continuousOn
  exact (UniformOnFun.uniformContinuous_eval_of_mem _ _ e1 e2).continuous.comp_continuousOn
    (ContinuousOn_uderiv hU)

theorem main [good_domain U] : ∃ f ∈ 𝓘 U, f '' U = ball (0 : ℂ) 1 := by
  obtain ⟨z₀, hz₀⟩ : U.Nonempty := good_domain.is_nonempty
  have hU : IsOpen U := good_domain.is_open
  have hU' : IsPreconnected U := good_domain.is_preconnected
  have h1 : ContinuousOn (obs z₀) (𝓙 U) := ((ContinuousOn_obs hU hz₀).mono (λ f hf => hf.1.1))
  obtain ⟨f, hf, hfg⟩ := IsCompact_𝓙.exists_forall_ge (𝓘_nonempty.mono 𝓘_subset_𝓙) h1
  have h7 : ¬ ∃ w, EqOn f (λ _ => w) U := by
    obtain ⟨g, hg⟩ : (𝓘 U).Nonempty := 𝓘_nonempty
    specialize hfg g (𝓘_subset_𝓙 hg)
    have := norm_pos_iff.1 ((norm_pos_iff.2 (deriv_ne_zero_of_inj hU hg.1.1 hg.2 hz₀)).trans_le hfg)
    contrapose! this
    obtain ⟨w, hw : EqOn f (λ _ => w) U⟩ := this
    simpa only [deriv_const'] using (hw.eventuallyEq_of_mem (hU.mem_nhds hz₀)).deriv_eq
  have h5 : f ∈ 𝓘 U := ⟨hf.1, hf.2.resolve_right h7⟩
  refine ⟨f, h5, ?_⟩
  have h10 : f '' U ⊆ ball 0 1 := by
    have := ((hf.1.1.analyticOn hU).is_constant_or_isOpen hU').resolve_left h7 U subset_rfl hU
    simpa [interior_closedBall] using this.subset_interior_iff.2 (mapsTo'.1 hf.1.2)
  refine (subset_iff_ssubset_or_eq.1 h10).resolve_left ?_
  contrapose! hfg
  obtain ⟨g, hg⟩ := step_2 U hz₀ ⟨f, hf.1.1, h5.2, mapsTo'.2 h10⟩ hfg
  exact ⟨g.to_fun, 𝓘_subset_𝓙 ⟨⟨g.is_diff, g.maps_to.mono_right ball_subset_closedBall⟩, g.is_inj⟩, hg⟩

end RMT

-- theorem RMT (h1 : IsOpen U) (h2 : is_connected U) (h3 : U ≠ univ) (h4 : has_primitives U) :
--   ∃ f : ℂ → ℂ, (DifferentiableOn ℂ f U) ∧ (InjOn f U) ∧ (f '' U = ball 0 1) :=
-- begin
--   have := (h4.has_logs h1 h2.is_preconnected).has_sqrt,
--   obtain ⟨f, hf, hfU⟩ := @RMT.main U ⟨h1, h2.1, h2.2, h3, this⟩,
--   exact ⟨f, hf.1.1, hf.2, hfU⟩
-- end