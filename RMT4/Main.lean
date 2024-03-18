import RMT4.Spaces
import RMT4.etape2
import RMT4.has_sqrt
import RMT4.Montel

open UniformConvergence Topology Filter Set Metric Function

variable {ι : Type*} {l : Filter ι} {U : Set ℂ} {z₀ : ℂ}

lemma IsCompact_𝓙 [good_domain U] : IsCompact (𝓙 U) := by
  have hU : IsOpen U := good_domain.is_open
  refine (isCompact_𝓜 hU).of_isClosed_subset ?_ (λ _ hf => hf.1)
  refine isClosed_iff_clusterPt.2 (λ f hf => ?_)
  set l := 𝓝 f ⊓ 𝓟 (𝓙 U)
  haveI : l.NeBot := hf
  obtain ⟨h1, h2⟩ := tendsto_inf.1 (@tendsto_id _ l)
  rw [tendsto_principal] at h2
  refine ⟨(IsClosed_𝓜 hU).mem_of_tendsto h1 (h2.mono (λ _ h => h.1)), ?_⟩
  by_cases h : ∃ᶠ f in l, InjOn f U
  case pos =>
    refine (hurwitz_inj hU good_domain.is_preconnected ?_ ((tendsto_𝓒_iff hU).1 h1) h).symm
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

noncomputable def obs (z₀ : ℂ) (f : 𝓒 U) : ℝ := ‖deriv f z₀‖

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

theorem RMT (h1 : IsOpen U) (h2 : IsConnected U) (h3 : U ≠ univ) (h4 : has_primitives U) :
    ∃ f : ℂ → ℂ, (DifferentiableOn ℂ f U) ∧ (InjOn f U) ∧ (f '' U = ball 0 1) := by
  have : good_domain U := ⟨h1, h2.1, h2.2, h3, (h4.has_logs h1 h2.isPreconnected).has_sqrt⟩
  obtain ⟨f, hf : f ∈ 𝓘 U, hfU⟩ := main (U := U)
  exact ⟨f, hf.1.1, hf.2, hfU⟩

#print axioms RMT
