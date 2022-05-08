/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.martingale

/-!
# Draft
-/

namespace probability_theory

section stopping

variables {α : Type*} {τ σ : α → ℕ}

lemma condexp_indicator_stopping_time_eq [sigma_finite_filtration μ 𝒢] {f : α → E}
  (hτ : is_stopping_time 𝒢 τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  {i : ℕ} (hf : integrable f μ) :
  μ[f | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x = i}] μ[f | 𝒢 i] :=
begin
  refine condexp_indicator_eq_todo hτ.measurable_space_le (𝒢.le i) hf (hτ.measurable_set_eq' i)
    (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

lemma condexp_indicator_stopping_time_le [sigma_finite_filtration μ 𝒢] {f : α → E}
  (hτ : is_stopping_time 𝒢 τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  [sigma_finite (μ.trim (hτ.min_const i).measurable_space_le)]
  {i : ℕ} (hf : integrable f μ) :
  μ[f | hτ.measurable_space] =ᵐ[μ.restrict {x | τ x ≤ i}] μ[f | (hτ.min_const i).measurable_space] :=
begin
  refine condexp_indicator_eq_todo hτ.measurable_space_le (hτ.min_const i).measurable_space_le hf
    (hτ.measurable_set_le' i) (λ t, _),
  rw [set.inter_comm _ t],
  sorry,
end

lemma condexp_indicator_todo [sigma_finite_filtration μ 𝒢] {f : ℕ → α → E} (h : martingale f 𝒢 μ)
  (hτ : is_stopping_time 𝒢 τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  {i n : ℕ} (hin : i ≤ n) :
  f i =ᵐ[μ.restrict {x | τ x = i}] μ[f n | hτ.measurable_space] :=
begin
  have hfi_eq_restrict : f i =ᵐ[μ.restrict {x | τ x = i}] μ[f n | 𝒢 i],
    from ae_restrict_of_ae (h.condexp_ae_eq hin).symm,
  refine hfi_eq_restrict.trans _,
  refine condexp_indicator_eq_todo (𝒢.le i) hτ.measurable_space_le (h.integrable n)
    (hτ.measurable_set_eq i) (λ t, _),
  rw [set.inter_comm _ t, is_stopping_time.measurable_set_inter_eq_iff],
end

lemma martingale.stopped_value_eq_of_le_const {f : ℕ → α → E}
  (h : martingale f 𝒢 μ) (hτ : is_stopping_time 𝒢 τ) {n : ℕ} (hτ_le : ∀ x, τ x ≤ n)
  [sigma_finite (μ.trim hτ.measurable_space_le)] :
  stopped_value f τ =ᵐ[μ] μ[f n | hτ.measurable_space] :=
begin
  rw [stopped_value_eq hτ_le],
  swap, apply_instance,
  sorry,
end

lemma martingale.stopped_value_eq_of_le {f : ℕ → α → E}
  (h : martingale f 𝒢 μ) (hτ : is_stopping_time 𝒢 τ) (hσ : is_stopping_time 𝒢 σ) {i : ℕ}
  (hτ_le : ∀ x, τ x ≤ i) (hστ : σ ≤ τ) [sigma_finite (μ.trim hτ.measurable_space_le)]
  [sigma_finite (μ.trim hσ.measurable_space_le)] :
  stopped_value f σ =ᵐ[μ] μ[stopped_value f τ | hσ.measurable_space] :=
begin
  rw [stopped_value_eq hτ_le, stopped_value_eq (λ x, (hστ x).trans (hτ_le x))],
  swap, apply_instance,
  swap, apply_instance,
  sorry,
end

end stopping


end probability_theory
