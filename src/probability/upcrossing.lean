/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import probability.martingale

/-! # Upcrossing lemma -/

open_locale probability_theory measure_theory ennreal nnreal filter big_operators

open measure_theory

namespace probability_theory

variables {ι α β : Type*} {mα : measurable_space α} {μ : measure α}

noncomputable
def sup_norm_Iic [has_le ι] [normed_group β] (f : ι → α → β) (n : ι) : α → ℝ :=
λ x, ⨆ m ≤ n, ∥f m x∥

noncomputable
def sup_norm [normed_group β] (f : ι → α → β) : α → ℝ :=
λ x, ⨆ m, ∥f m x∥

variables {ℱ : filtration ℕ mα} [sigma_finite_filtration μ ℱ]

noncomputable def first_gt_before (f : ℕ → α → ℝ) (c : ℝ) (n : ℕ)
  [decidable_pred (λ x, (∃ (k : ℕ) (H : k ≤ n), c < f k x))] : α → ℕ :=
λ x, if H : ∃ k ≤ n, c < f k x then nat.find H else n + 1

lemma first_gt_before_le_iff {f : ℕ → α → ℝ} {c : ℝ} {i n : ℕ} (hin : i ≤ n) (x : α)
  [decidable_pred (λ x, (∃ (k : ℕ) (H : k ≤ n), c < f k x))] :
  first_gt_before f c n x ≤ i ↔ ∃ k ≤ i, c < f k x :=
begin
  rw first_gt_before,
  dsimp only,
  split_ifs,
  { simp only [nat.find_le_iff, exists_prop],
    split; rintros ⟨k, hk⟩; refine ⟨k, _⟩,
    { exact ⟨hk.1, hk.2.2⟩, },
    { exact ⟨hk.1, hk.1.trans hin, hk.2⟩, }, },
  { have : ¬ n + 1 ≤ i, from λ hni, nat.not_succ_le_self _ (hni.trans hin),
    push_neg at h,
    simp only [this, exists_prop, false_iff, not_exists, not_and, not_lt],
    exact λ k hk, h k (hk.trans hin), },
end

lemma first_gt_before_le_succ {f : ℕ → α → ℝ} {c : ℝ} {n : ℕ} {x : α}
  [decidable_pred (λ x, (∃ (k : ℕ) (H : k ≤ n), c < f k x))] :
  first_gt_before f c n x ≤ n + 1 :=
begin
  rw first_gt_before,
  dsimp only,
  split_ifs,
  { simp only [nat.find_le_iff, exists_prop],
    obtain ⟨k, hkn, hk⟩ := h,
    exact ⟨k, hkn.trans (nat.le_succ n), hkn, hk⟩, },
  { exact le_rfl, },
end

lemma is_stopping_time_first_gt_before (f : ℕ → α → ℝ) (c : ℝ) (n : ℕ) (h : submartingale f ℱ μ)
  [decidable_pred (λ x, (∃ (k : ℕ) (H : k ≤ n), c < f k x))] :
  is_stopping_time ℱ (first_gt_before f c n) :=
begin
  have : ∀ i ≤ n, {x | first_gt_before f c n x ≤ i} = ⋃ k ≤ i, {x | c < f k x},
  { intros i hin,
    ext1 x,
    rw [set.mem_set_of_eq, first_gt_before_le_iff hin x],
    simp_rw set.mem_Union,
    refl, },
  refine (λ i, _),
  cases le_or_lt i n with hin hin,
  { rw this i hin,
    refine measurable_set.bUnion (set.countable_encodable _) (λ j hji, _),
    refine @measurable_set_lt _ _ _ _ _ (ℱ i) _ _ _ _ _ (@measurable_const _ _ _(ℱ i) _) _,
    exact (h.adapted j).measurable.mono (ℱ.mono hji) le_rfl, },
  { convert measurable_set.univ,
    ext1 x,
    simp only [eq_iff_iff, iff_true],
    exact first_gt_before_le_succ.trans hin, },
end

lemma sup_norm_Iic_gt_iff_first_gt_before_le {f : ℕ → α → ℝ} {c : ℝ} {n : ℕ} {x : α}
  [decidable_pred (λ x, (∃ (k : ℕ) (H : k ≤ n), c < f k x))]
  (hf_nonneg : ∀ n, 0 ≤ f n) :
  c < sup_norm_Iic f n x ↔ first_gt_before f c n x ≤ n :=
begin
  rw first_gt_before_le_iff le_rfl,
  rw sup_norm_Iic,
  simp,
  sorry,
end

lemma of_real_integral_eq_lintegral_of_real {f : α → ℝ} (hfi : integrable f μ) (f_nn : 0 ≤ f) :
  ennreal.of_real (∫ x, f x ∂μ) = ∫⁻ x, ennreal.of_real (f x) ∂μ :=
calc ennreal.of_real (∫ x, f x ∂μ) = ennreal.of_real ∫ x, ∥f x∥ ∂μ :
  by { congr, ext1 x, rw [real.norm_eq_abs, abs_eq_self.mpr (f_nn x)], }
... = ∫⁻ x, ∥f x∥₊ ∂μ : of_real_integral_norm_eq_lintegral_nnnorm hfi
... = ∫⁻ x, ennreal.of_real (f x) ∂μ :
  by { congr, ext1 x, rw [← of_real_norm_eq_coe_nnnorm, real.norm_eq_abs,
                          abs_eq_self.mpr (f_nn x)] }

lemma todo {f : ℕ → α → ℝ} (h : submartingale f ℱ μ) (hf_nonneg : ∀ n, 0 ≤ f n)
  (c : ℝ) (n : ℕ) :
  (ennreal.of_real c) * μ {x | c < sup_norm_Iic f n x}
    ≤ ennreal.of_real (∫ x in {x | c < sup_norm_Iic f n x}, f n x ∂μ) :=
begin
  classical,
  let τ : α → ℕ := first_gt_before f c n,
  have hτ_stop : is_stopping_time ℱ τ,
    from is_stopping_time_first_gt_before f c n h,
  have : ∀ i ≤ n, {x | τ x ≤ i} = ⋃ k ≤ i, {x | c < f k x},
  { intros i hin,
    ext1 x,
    rw [set.mem_set_of_eq, first_gt_before_le_iff hin x],
    simp_rw set.mem_Union,
    refl, },
  have : {x : α | c < sup_norm_Iic f n x} = ⋃ k ≤ n, {x | τ x = k},
  { ext1 x,
    have : c < sup_norm_Iic f n x ↔ τ x ≤ n,
      from sup_norm_Iic_gt_iff_first_gt_before_le hf_nonneg,
    rw [set.mem_set_of_eq, this],
    simp, },
  rw this,
  calc ennreal.of_real c * μ (⋃ (k : ℕ) (H : k ≤ n), {x : α | τ x = k})
      ≤ ennreal.of_real c * ∑ k in finset.range n, μ {x : α | τ x = k} : sorry
  ... = ∑ k in finset.range n, ennreal.of_real c * μ {x : α | τ x = k} : finset.mul_sum
  ... = ∑ k in finset.range n, ennreal.of_real c *
    ∫⁻ x in{x : α | τ x = k}, (λ _, (1 : ℝ≥0∞)) x ∂μ :
      by simp_rw [lintegral_const, measure.restrict_apply_univ, one_mul]
  ... = ∑ k in finset.range n, ennreal.of_real c *
    ∫⁻ x, {x : α | τ x = k}.indicator (λ _, (1 : ℝ≥0∞)) x ∂μ :
      by { congr, ext1 k, rw lintegral_indicator _ (ℱ.le k _ (hτ_stop.measurable_set_eq k)), }
  ... = ∑ k in finset.range n,
    ∫⁻ x, {x : α | τ x = k}.indicator (λ _, ennreal.of_real c) x ∂μ : begin
      congr,
      ext1 k,
      rw ← lintegral_const_mul,
      { congr, ext1 x, by_cases hx : x ∈ {x : α | τ x = k} ; simp [hx], },
      { exact measurable.indicator (by apply measurable_const)
          (ℱ.le k _ (hτ_stop.measurable_set_eq k)), },
    end
  ... ≤ ∑ k in finset.range n,
    ∫⁻ x, {x : α | τ x = k}.indicator (λ x, ennreal.of_real (f k x)) x ∂μ : begin
      refine finset.sum_le_sum (λ k hk, _),
      sorry,
    end
  ... = ∑ k in finset.range n,
    ennreal.of_real ∫ x, {x : α | τ x = k}.indicator (f k) x ∂μ : begin
      congr,
      ext1 k,
      rw of_real_integral_eq_lintegral_of_real,
      sorry,
      sorry,
      sorry,
    end
  ... ≤ ∑ k in finset.range n,
    ennreal.of_real ∫ x, {x : α | τ x = k}.indicator (μ[f n | ℱ k, ℱ.le k]) x ∂μ : begin
      refine finset.sum_le_sum (λ k hk, _),
      refine ennreal.of_real_le_of_real _,
      sorry,  -- use submartingale
    end
  ... = ∑ k in finset.range n,
    ennreal.of_real ∫ x, {x : α | τ x = k}.indicator (f n) x ∂μ : begin
      congr,
      ext1 k,
      congr' 1,
      simp_rw integral_indicator (ℱ.le k _ (hτ_stop.measurable_set_eq k)),
      exact set_integral_condexp _ (h.integrable n) (hτ_stop.measurable_set_eq k),
    end
  ... = ennreal.of_real ∑ k in finset.range n, ∫ x, {x : α | τ x = k}.indicator (f n) x ∂μ : sorry
  ... = ennreal.of_real ∫ x, (∑ k in finset.range n, {x : α | τ x = k}.indicator (f n)) x ∂μ : sorry
  ... = ennreal.of_real (∫ x in {x | c < sup_norm_Iic f n x}, f n x ∂μ) : sorry,
end

end probability_theory
