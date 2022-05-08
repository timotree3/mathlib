/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.conditional_expectation
import probability.stopping

/-!
# Draft
-/

open_locale measure_theory

namespace measure_theory

variables {α E : Type*} {m m₂ mα : measurable_space α} {μ : measure α} [normed_group E]
  [normed_space ℝ E] [complete_space E]

lemma condexp_ae_eq_restrict_zero {s : set α} {f : α → E}
  (hf_int : integrable f μ) (hs : measurable_set[m] s) (hf : f =ᵐ[μ.restrict s] 0) :
  μ[f | m] =ᵐ[μ.restrict s] 0 :=
begin
  by_cases hm : m ≤ mα,
  swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  haveI : sigma_finite ((μ.restrict s).trim hm),
  { rw ← restrict_trim hm _ hs,
    exact restrict.sigma_finite _ s, },
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm _ _ _ _ _,
  { exact λ t ht hμt, integrable_condexp.integrable_on.integrable_on, },
  { exact λ t ht hμt, (integrable_zero _ _ _).integrable_on, },
  { intros t ht hμt,
    rw [measure.restrict_restrict (hm _ ht), set_integral_condexp hm hf_int (ht.inter hs),
      ← measure.restrict_restrict (hm _ ht)],
    refine set_integral_congr_ae (hm _ ht) _,
    filter_upwards [hf] with x hx h using hx, },
  { exact strongly_measurable_condexp.ae_strongly_measurable', },
  { exact strongly_measurable_zero.ae_strongly_measurable', },
end

lemma condexp_L1_congr_ae (hm : m ≤ mα) [sigma_finite (μ.trim hm)] {f g : α → E} (h : f =ᵐ[μ] g) :
  condexp_L1 hm μ f = condexp_L1 hm μ g :=
set_to_fun_congr_ae _ h

lemma condexp_congr_ae {f g : α → E} (h : f =ᵐ[μ] g) : μ[f | m] =ᵐ[μ] μ[g | m] :=
begin
  by_cases hm : m ≤ mα,
  swap, { simp_rw condexp_of_not_le hm, },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw condexp_of_not_sigma_finite hm hμm, },
  haveI : sigma_finite (μ.trim hm) := hμm,
  exact (condexp_ae_eq_condexp_L1 hm f).trans
    (filter.eventually_eq.trans (by rw condexp_L1_congr_ae hm h)
    (condexp_ae_eq_condexp_L1 hm g).symm)
end

lemma indicator_ae_eq_of_restrict_compl_ae_eq_zero {E} [has_zero E] {s : set α} {f : α → E}
  (hs : measurable_set s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
  s.indicator f =ᵐ[μ] f :=
begin
  rw [filter.eventually_eq, ae_restrict_iff' hs.compl] at hf,
  filter_upwards [hf] with x hx,
  by_cases hxs : x ∈ s,
  { simp only [hxs, set.indicator_of_mem], },
  { simp only [hx hxs, pi.zero_apply, set.indicator_apply_eq_zero, eq_self_iff_true,
      implies_true_iff], },
end

/-- Do not use. Auxiliary lemma for `condexp_indicator`. -/
lemma condexp_indicator_aux (hm : m ≤ mα) {s : set α} {f : α → E}
  (hf_int : integrable f μ) (hs : measurable_set[m] s) (hf : f =ᵐ[μ.restrict sᶜ] 0) :
  s.indicator (μ[f | m]) =ᵐ[μ] μ[s.indicator f | m] :=
begin
  have hsf_zero : ∀ g : α → E, g =ᵐ[μ.restrict sᶜ] 0 → s.indicator g =ᵐ[μ] g,
    from λ g, indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs),
  refine (hsf_zero (μ[f | m]) (condexp_ae_eq_restrict_zero hf_int hs.compl hf)).trans _,
  exact condexp_congr_ae (hsf_zero f hf).symm,
end

lemma condexp_indicator {s : set α} {f : α → E}
  (hf_int : integrable f μ) (hs : measurable_set[m] s) :
  μ[s.indicator f | m] =ᵐ[μ] s.indicator (μ[f | m]) :=
begin
  by_cases hm : m ≤ mα,
  swap, { simp_rw [condexp_of_not_le hm, set.indicator_zero'], },
  by_cases hμm : sigma_finite (μ.trim hm),
  swap, { simp_rw [condexp_of_not_sigma_finite hm hμm, set.indicator_zero'], },
  haveI : sigma_finite (μ.trim hm) := hμm,
  -- use `have` to perform what should be the first calc step because of an error I don't
  -- understand
  have : s.indicator (μ[f|m]) =ᵐ[μ] s.indicator (μ[s.indicator f + sᶜ.indicator f|m]),
    by rw set.indicator_self_add_compl s f,
  refine (this.trans _).symm,
  calc s.indicator (μ[s.indicator f + sᶜ.indicator f|m])
      =ᵐ[μ] s.indicator (μ[s.indicator f|m] + μ[sᶜ.indicator f|m]) :
    begin
      have : μ[s.indicator f + sᶜ.indicator f|m] =ᵐ[μ] μ[s.indicator f|m] + μ[sᶜ.indicator f|m],
        from condexp_add (hf_int.indicator (hm _ hs)) (hf_int.indicator (hm _ hs.compl)),
      filter_upwards [this] with x hx,
      classical,
      rw [set.indicator_apply, set.indicator_apply, hx],
    end
  ... = s.indicator (μ[s.indicator f|m]) + s.indicator (μ[sᶜ.indicator f|m]) :
    s.indicator_add' _ _
  ... =ᵐ[μ] s.indicator (μ[s.indicator f|m]) + s.indicator (sᶜ.indicator (μ[sᶜ.indicator f|m])) :
    begin
      refine filter.eventually_eq.rfl.add _,
      have : sᶜ.indicator (μ[sᶜ.indicator f|m]) =ᵐ[μ] μ[sᶜ.indicator f|m],
      { refine (condexp_indicator_aux hm (hf_int.indicator (hm _ hs.compl)) hs.compl _).trans _,
        { exact indicator_ae_eq_restrict_compl (hm _ hs.compl), },
        { rw [set.indicator_indicator, set.inter_self], }, },
      filter_upwards [this] with x hx,
      by_cases hxs : x ∈ s,
      { simp only [hx, hxs, set.indicator_of_mem], },
      { simp only [hxs, set.indicator_of_not_mem, not_false_iff], },
    end
  ... =ᵐ[μ] s.indicator (μ[s.indicator f|m]) :
    by rw [set.indicator_indicator, set.inter_compl_self, set.indicator_empty', add_zero]
  ... =ᵐ[μ] μ[s.indicator f|m] :
    begin
      refine (condexp_indicator_aux hm (hf_int.indicator (hm _ hs)) hs _).trans _,
      { exact indicator_ae_eq_restrict_compl (hm _ hs), },
      { rw [set.indicator_indicator, set.inter_self], },
    end
end

lemma strongly_measurable_todo {E} [topological_space E] [has_zero E] {s : set α} {f : α → E}
  (hs_m : measurable_set[m] s)
  (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t))
  (hf : strongly_measurable[m] f) (hf_zero : ∀ x ∉ s, f x = 0) :
  strongly_measurable[m₂] f :=
begin
  have hs_m₂ : measurable_set[m₂] s,
  { rw ← set.inter_univ s,
    refine hs set.univ _,
    rwa [set.inter_univ], },
  let g_seq_s : ℕ → @simple_func α m₂ E := λ n,
  { to_fun := s.indicator (hf.approx n),
    measurable_set_fiber' := λ x, begin
      classical,
      by_cases hx : x = 0,
      { rw [s.indicator_preimage, hx, pi.zero_def, set.preimage_const, set.mem_singleton_iff,
          set.ite, set.inter_comm],
        simp only [eq_self_iff_true, if_true],
        rw ← set.compl_eq_univ_diff s,
        refine measurable_set.union (hs _ (hs_m.inter _)) hs_m₂.compl,
        exact @simple_func.measurable_set_fiber _ _ m (hf.approx n) _, },
      { rw [s.indicator_preimage, pi.zero_def, set.preimage_const, set.mem_singleton_iff],
        simp only [ne.symm hx, if_false, set.ite_empty_right],
        rw set.inter_comm,
        exact hs _ (hs_m.inter (@simple_func.measurable_set_fiber _ _ m (hf.approx n) x)), },
    end,
    finite_range' := begin
      have : ((set.range (hf.approx n)) ∪ {0}).finite,
        from (@simple_func.finite_range _ _ m (hf.approx n)).union (set.finite_singleton _),
      refine set.finite.subset this (λ x h, _),
      rw [set.mem_union, set.mem_singleton_iff, set.mem_range],
      rw [set.mem_range_indicator, set.mem_image] at h,
      rcases h with h | ⟨x, _, hx⟩,
      { exact or.inr h.left, },
      { exact or.inl ⟨x, hx⟩, },
    end, },
  have hg_eq : ∀ x ∈ s, ∀ n, g_seq_s n x = hf.approx n x,
  { intros x hx n,
    simp only [hx, simple_func.apply_mk, set.indicator_of_mem], },
  have hg_zero : ∀ x ∉ s, ∀ n, g_seq_s n x = 0,
  { intros x hx n,
    simp only [simple_func.apply_mk, hx, set.indicator_of_not_mem, not_false_iff], },
  refine ⟨g_seq_s, λ x, _⟩,
  by_cases hx : x ∈ s,
  { simp_rw hg_eq x hx,
    exact hf.tendsto_approx x, },
  { simp_rw [hg_zero x hx, hf_zero x hx],
    exact tendsto_const_nhds, },
end

lemma ae_strongly_measurable'_todo {E} [topological_space E] [has_zero E] (hm : m ≤ mα)
  {s : set α} {f : α → E}
  (hs_m : measurable_set[m] s) (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t))
  (hf : ae_strongly_measurable' m f μ) (hf_zero : f =ᵐ[μ.restrict sᶜ] 0) :
  ae_strongly_measurable' m₂ f μ :=
begin
  let f' := hf.mk f,
  have h_ind_eq : s.indicator (hf.mk f) =ᵐ[μ] f,
  { refine filter.eventually_eq.trans _
      (indicator_ae_eq_of_restrict_compl_ae_eq_zero (hm _ hs_m) hf_zero),
    filter_upwards [hf.ae_eq_mk] with x hx,
    by_cases hxs : x ∈ s,
    { simp [hxs, hx], },
    { simp [hxs], }, },
  suffices : strongly_measurable[m₂] (s.indicator (hf.mk f)),
    from ae_strongly_measurable'.congr this.ae_strongly_measurable' h_ind_eq,
  have hf_ind : strongly_measurable[m] (s.indicator (hf.mk f)),
    from hf.strongly_measurable_mk.indicator hs_m,
  exact strongly_measurable_todo hs_m hs hf_ind (λ x hxs, set.indicator_of_not_mem hxs _),
end

lemma ae_eq_restrict_iff_indicator_ae_eq {α E} [has_zero E] {m : measurable_space α} {μ : measure α}
  {s : set α} {f g : α → E} (hs : measurable_set s) :
  f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g :=
begin
  rw [filter.eventually_eq, ae_restrict_iff' hs],
  refine ⟨λ h, _, λ h, _⟩; filter_upwards [h] with x hx,
  { by_cases hxs : x ∈ s,
    { simp [hxs, hx hxs], },
    { simp [hxs], }, },
  { intros hxs,
    simpa [hxs] using hx, },
end

/-- TODO
The hypothesis `(hs : ∀ t, measurable_set[m] (s ∩ t) ↔ measurable_set[m₂] (s ∩ t))` means that
under the event `s`, the σ-algebras `m` and `m₂` are the same. -/
lemma condexp_indicator_eq_todo (hm : m ≤ mα) (hm₂ : m₂ ≤ mα) [sigma_finite (μ.trim hm)]
  [sigma_finite (μ.trim hm₂)] {s : set α} {f : α → E}
  (hf_int : integrable f μ) (hs_m : measurable_set[m] s)
  (hs : ∀ t, measurable_set[m] (s ∩ t) ↔ measurable_set[m₂] (s ∩ t)) :
  μ[f | m] =ᵐ[μ.restrict s] μ[f | m₂] :=
begin
  rw ae_eq_restrict_iff_indicator_ae_eq (hm _ hs_m),
  have hs_m₂ : measurable_set[m₂] s,
  { rwa [← set.inter_univ s, ← hs set.univ, set.inter_univ], },
  refine (condexp_indicator hf_int hs_m).symm.trans _,
  refine filter.eventually_eq.trans _ (condexp_indicator hf_int hs_m₂),
  refine ae_eq_of_forall_set_integral_eq_of_sigma_finite' hm₂ _ _ _ _ _,
  { exact λ s hs hμs, integrable_condexp.integrable_on, },
  { exact λ s hs hμs, integrable_condexp.integrable_on, },
  { intros t ht hμt,
    have : ∫ x in t, μ[s.indicator f|m] x ∂μ = ∫ x in s ∩ t, μ[s.indicator f|m] x ∂μ,
    { rw ← integral_add_compl (hm _ hs_m) integrable_condexp.integrable_on,
      suffices : ∫ x in sᶜ, μ[s.indicator f|m] x ∂μ.restrict t = 0,
      { by rw [this, add_zero, measure.restrict_restrict (hm _ hs_m)], },
      rw measure.restrict_restrict (measurable_set.compl (hm _ hs_m)),
      suffices : μ[s.indicator f|m] =ᵐ[μ.restrict sᶜ] 0,
      { rw [set.inter_comm, ← measure.restrict_restrict (hm₂ _ ht)],
        calc ∫ (x : α) in t, μ[s.indicator f|m] x ∂μ.restrict sᶜ
            = ∫ (x : α) in t, 0 ∂μ.restrict sᶜ : begin
              refine set_integral_congr_ae (hm₂ _ ht) _,
              filter_upwards [this] with x hx h using hx,
            end
        ... = 0 : integral_zero _ _, },
      refine condexp_ae_eq_restrict_zero (hf_int.indicator (hm _ hs_m)) hs_m.compl _,
      exact indicator_ae_eq_restrict_compl (hm _ hs_m), },
    have hst_m : measurable_set[m] (s ∩ t) := (hs _).mpr (hs_m₂.inter ht),
    simp_rw [this, set_integral_condexp hm₂ (hf_int.indicator (hm _ hs_m)) ht,
      set_integral_condexp hm (hf_int.indicator (hm _ hs_m)) hst_m,
      integral_indicator (hm _ hs_m), measure.restrict_restrict (hm _ hs_m),
       ← set.inter_assoc, set.inter_self], },
  { have : strongly_measurable[m] (μ[s.indicator f | m]) := strongly_measurable_condexp,
    refine ae_strongly_measurable'_todo hm hs_m (λ t, (hs t).mp) this.ae_strongly_measurable' _,
    refine condexp_ae_eq_restrict_zero (hf_int.indicator (hm _ hs_m)) hs_m.compl _,
    exact indicator_ae_eq_restrict_compl (hm _ hs_m), },
  { exact strongly_measurable_condexp.ae_strongly_measurable', },
end

end measure_theory
