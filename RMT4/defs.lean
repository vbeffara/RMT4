import RMT4.to_mathlib
import RMT4.deriv_inj

open Complex Metric Set

variable {u : ℂ} {U V W : Set ℂ}

namespace RMT

def 𝔻 : Set ℂ := ball 0 1

lemma mem_𝔻_iff : u ∈ 𝔻 ↔ ‖u‖ < 1 :=
  mem_ball_zero_iff

lemma neg_in_𝔻 : u ∈ 𝔻 → -u ∈ 𝔻 := by
  simp [𝔻]

lemma sqrt_𝔻_eq_𝔻 : {z : ℂ | z ^ 2 ∈ 𝔻} = 𝔻 := by
  simp [𝔻, ball]

class good_domain (U : Set ℂ) : Prop :=
  (is_open : IsOpen U)
  (is_nonempty : U.Nonempty)
  (is_preconnected : IsPreconnected U)
  (ne_univ : U ≠ univ)
  (has_sqrt : ∀ f : ℂ → ℂ, (∀ z ∈ U, f z ≠ 0) → (DifferentiableOn ℂ f U) →
    ∃ (g : ℂ → ℂ), (DifferentiableOn ℂ g U) ∧ (U.EqOn f (g ^ 2)))

structure embedding (U V : Set ℂ) :=
  (to_fun : ℂ → ℂ)
  (is_diff : DifferentiableOn ℂ to_fun U)
  (is_inj : InjOn to_fun U) -- TODO: rename to `inj_on`
  (maps_to : MapsTo to_fun U V)

instance {U V : Set ℂ} : CoeFun (embedding U V) (λ _ => ℂ → ℂ) := ⟨embedding.to_fun⟩

@[simp] lemma embedding.to_fun_def {U V f d i m z} : @embedding.mk U V f d i m z = f z := rfl

@[simp] lemma embedding.to_fun_eq_coe (f : embedding U V) : f.to_fun = f := rfl

@[simp] def embedding.id (hUV : U = V) : embedding U V where
  to_fun := λ x => x
  is_diff := differentiable_id.differentiableOn
  is_inj := λ _ _ _ _ z => z
  maps_to := λ _ hx => hUV ▸ hx

@[simp] def embedding.comp (f : embedding V W) (g : embedding U V) : embedding U W where
  to_fun := f ∘ g
  is_diff := f.is_diff.comp g.is_diff g.maps_to
  is_inj := f.is_inj.comp g.is_inj g.maps_to
  maps_to := f.maps_to.comp g.maps_to

noncomputable def embedding.sqrt [good_domain U] (f : embedding U V) (hf : ∀ z ∈ U, f z ≠ 0) :
    { g : embedding U {z | z ^ 2 ∈ V} // U.EqOn f (g.to_fun ^ 2) } := by
  choose g g_diff g_sqrt using good_domain.has_sqrt f hf f.is_diff
  refine ⟨⟨g, g_diff, ?_, ?_⟩, g_sqrt⟩
  · exact λ z hz z' hz' h => f.is_inj hz hz' (by simp [g_sqrt hz, g_sqrt hz', h])
  · exact λ z hz => by simpa [g_sqrt hz] using f.maps_to hz

noncomputable def embedding.sqrt' [good_domain U] (f : embedding U 𝔻) (hf : ∀ z ∈ U, f z ≠ 0) :
    { g : embedding U 𝔻 // U.EqOn f (g.to_fun ^ 2) } := by
  let ⟨g, hg⟩ := embedding.sqrt f hf
  exact ⟨(embedding.id sqrt_𝔻_eq_𝔻).comp g, hg⟩

lemma ne_center_of_not_mem_closed_ball {w : ℂ} {r : ℝ} (hr : 0 ≤ r) ⦃z : ℂ⦄ (hz : z ∈ (closedBall w r)ᶜ) :
    z ≠ w := by
  contrapose! hz
  simp [hz, hr]

noncomputable def embedding.inv (w : ℂ) {r : ℝ} (hr : 0 < r) : embedding ((closedBall w r)ᶜ) 𝔻 where
  to_fun := λ z => r / (z - w)
  is_diff := by
    refine (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _)) ?_
    simpa only [sub_ne_zero] using ne_center_of_not_mem_closed_ball hr.le
  is_inj := λ x hx y hy hxy => by
    rw [div_eq_div_iff, eq_comm] at hxy
    · simpa [hr.ne.symm] using hxy
    · simpa only [sub_ne_zero] using ne_center_of_not_mem_closed_ball hr.le hx
    · simpa only [sub_ne_zero] using ne_center_of_not_mem_closed_ball hr.le hy
  maps_to := λ x hx => by
    replace hx : r < abs (x - w) := by simpa [𝔻] using hx
    simp only [𝔻, mem_ball_zero_iff, norm_eq_abs, norm_div]
    refine (@div_lt_one _ _ _ _ (hr.trans hx)).mpr ?_
    convert hx
    simp [hr.le]

lemma embedding.deriv_ne_zero {f : embedding U V} {z : ℂ} (hU : IsOpen U) (hz : z ∈ U) :
  deriv f z ≠ 0 :=
deriv_ne_zero_of_inj hU f.is_diff f.is_inj hz

end RMT
