import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping
import RMT4.defs

open Topology Filter Set Function UniformConvergence Metric

variable {U : Set ℂ} {Q : Set ℂ → Set ℂ} {ι : Type*} {l : Filter ι}

-- `𝓒 U` is an alias for `ℂ → ℂ` equipped with compact convergence on `U`

abbrev 𝓒 (U : Set ℂ) := ℂ →ᵤ[compacts U] ℂ

noncomputable def uderiv (f : 𝓒 U) : 𝓒 U := deriv f

lemma tendsto_𝓒_iff (hU : IsOpen U) {F : ι → 𝓒 U} {f : 𝓒 U} :
    Tendsto F l (𝓝 f) ↔ TendstoLocallyUniformlyOn F f l U := by
  simp [UniformOnFun.tendsto_iff_tendstoUniformlyOn, _root_.compacts]
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).symm

-- `𝓗 U` is the space of holomorphic functions on `U`

def 𝓗 (U : Set ℂ) := {f : 𝓒 U | DifferentiableOn ℂ f U}

lemma isClosed_𝓗 (hU : IsOpen U) : IsClosed (𝓗 U) := by
  refine isClosed_iff_clusterPt.2 (λ f hf => ?_)
  refine @TendstoLocallyUniformlyOn.differentiableOn _ _ _ _ _ _ _ id f hf ?_ ?_ hU
  · simp [← tendsto_𝓒_iff hU, Tendsto]
  · simp [eventually_inf_principal, 𝓗]; exact eventually_of_forall (λ g => id)

lemma ContinuousOn_uderiv (hU : IsOpen U) : ContinuousOn uderiv (𝓗 U) := by
  rintro f -
  refine (tendsto_𝓒_iff hU).2 ?_
  refine TendstoLocallyUniformlyOn.deriv ?_ eventually_mem_nhdsWithin hU
  apply (tendsto_𝓒_iff hU).1
  exact nhdsWithin_le_nhds

-- `𝓑 U Q` is the collection of `Q`-bounded holomorphic maps on `U`

def 𝓑 (U : Set ℂ) (Q : Set ℂ → Set ℂ) : Set (𝓒 U) :=
    {f ∈ 𝓗 U | ∀ K ∈ compacts U, MapsTo f K (Q K)}

lemma 𝓑_const {Q : Set ℂ} : 𝓑 U (fun _ => Q) = {f ∈ 𝓗 U | MapsTo f U Q} := by
  simp [𝓑, ← mapsTo_sUnion]

theorem isClosed_𝓑 (hU : IsOpen U) (hQ : ∀ K ∈ compacts U, IsCompact (Q K)) :
    IsClosed (𝓑 U Q) := by
  rw [𝓑, setOf_and] ; apply (isClosed_𝓗 hU).inter
  simp only [setOf_forall, MapsTo]
  apply isClosed_biInter ; intro K hK
  apply isClosed_biInter ; intro z hz
  apply (hQ K hK).isClosed.preimage
  exact ((UniformOnFun.uniformContinuous_eval_of_mem ℂ (compacts U)
    (mem_singleton z) ⟨singleton_subset_iff.2 (hK.1 hz), isCompact_singleton⟩).continuous)

-- `𝓜 U` : holomorphic functions to the unit closed ball

def 𝓜 (U : Set ℂ) := {f ∈ 𝓗 U | MapsTo f U (closedBall (0 : ℂ) 1)}

lemma 𝓜_eq_𝓑 : 𝓜 U = 𝓑 U (fun _ => closedBall 0 1) := 𝓑_const.symm

lemma IsClosed_𝓜 (hU : IsOpen U) : IsClosed (𝓜 U) := by
  suffices h : IsClosed {f : 𝓒 U | MapsTo f U (closedBall 0 1)} by
    exact (isClosed_𝓗 hU).inter h
  simp_rw [MapsTo, setOf_forall]
  refine isClosed_biInter (λ z hz => isClosed_ball.preimage ?_)
  exact ((UniformOnFun.uniformContinuous_eval_of_mem ℂ (compacts U)
    (mem_singleton z) ⟨singleton_subset_iff.2 hz, isCompact_singleton⟩).continuous)

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
      simp [e3, deriv_sub_const, f]
      intro h
      have := g_sqf hz₀
      rw [Pi.pow_apply, h, zero_pow two_ne_zero] at this
      cases f_noz hz₀ this
    refine e2.eventually_constant_or_nhds_le_map_nhds.resolve_left (λ h => ?_) (image_mem_map e1)
    simp [EventuallyEq.deriv_eq h] at dg_nonzero

  obtain ⟨r, r_pos, hr⟩ := Metric.mem_nhds_iff.mp gU_nhd
  let gg : embedding U ((closedBall (- g z₀) (r / 2))ᶜ) :=
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
