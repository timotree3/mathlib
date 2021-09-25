/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.radon_nikodym
import measure_theory.measure.lebesgue

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `measure_theory.measure.has_pdf` : A random variable `X : α → E` is said to `has_pdf` with
  respect to the measure `ℙ` on `α` and `μ` on `E` if there exists a measurable function `f`
  such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`.
* `measure_theory.measure.pdf` : If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X`
  is the measurable function `f` such that the push-forward measure of `ℙ` along `X` equals
  `μ.with_density f`.
* `measure_theory.measure.pdf.uniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `measure_theory.measure.pdf.integral_mul_eq_integral'` : Law of the unconscious statistician,
  i.e. if a random variable `X : α → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, g x * f x dx` for
  all measurable `g : E → ℝ`.
* `measure_theory.measure.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `measure_theory.measure.pdf.uniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODOs

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open topological_space

variables {α E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E]

namespace measure

/-- A random variable `X : α → E` is said to `has_pdf` with respect to the measure `ℙ` on `α` and
`μ` on `E` if there exists a measurable function `f` such that the push-forward measure of `ℙ`
along `X` equals `μ.with_density f`. -/
class has_pdf {m : measurable_space α} (X : α → E)
  (ℙ : measure α) (μ : measure E . volume_tac) : Prop :=
(pdf' : ∃ (f : E → ℝ≥0∞), measurable f ∧ map X ℙ = μ.with_density f)

/-- If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X` is the measurable function `f`
such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`. -/
def pdf {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) :=
if hX : has_pdf X ℙ μ then classical.some hX.pdf' else 0

@[measurability]
lemma measurable_pdf {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) :
  measurable (pdf X ℙ μ) :=
begin
  by_cases hX : has_pdf X ℙ μ,
  { rw [pdf, dif_pos hX],
    exact (classical.some_spec hX.pdf').1 },
  { rw [pdf, dif_neg hX],
    exact measurable_zero }
end

lemma map_eq_with_density_pdf {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : has_pdf X ℙ μ] :
  measure.map X ℙ = μ.with_density (pdf X ℙ μ) :=
begin
  rw [pdf, dif_pos hX],
  exact (classical.some_spec hX.pdf').2
end

lemma map_eq_set_lintegral_pdf {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : has_pdf X ℙ μ]
  {s : set E} (hs : measurable_set s) :
  measure.map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ :=
by rw [← with_density_apply _ hs, map_eq_with_density_pdf X ℙ μ]

namespace pdf

variables {m : measurable_space α} {ℙ : measure α} {μ : measure E}

lemma lintegral_eq_measure_univ {X : α → E} [has_pdf X ℙ μ] (hX : measurable X) :
  ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ set.univ :=
begin
  rw [← set_lintegral_univ, ← map_eq_set_lintegral_pdf X ℙ μ measurable_set.univ,
      measure.map_apply hX measurable_set.univ, set.preimage_univ],
end

lemma ae_lt_top {m : measurable_space α} (ℙ : measure α) [is_finite_measure ℙ] {μ : measure E}
  {X : α → E} (hX : measurable X) : ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
begin
  by_cases hpdf : has_pdf X ℙ μ,
  { refine ae_lt_top (measurable_pdf X ℙ μ) _,
    rw lintegral_eq_measure_univ hX,
    { exact (measure_lt_top _ _).ne },
    { exact hpdf } },
  { rw [pdf, dif_neg hpdf],
    exact filter.eventually_of_forall (λ x, with_top.zero_lt_top) }
end

lemma of_real_to_real_ae_eq [is_finite_measure ℙ] {X : α → E} (hX : measurable X) :
  (λ x, ennreal.of_real (pdf X ℙ μ x).to_real) =ᵐ[μ] pdf X ℙ μ :=
begin
  by_cases hpdf : has_pdf X ℙ μ,
  { exactI ennreal.of_real_to_real_ae_eq (ae_lt_top _ hX) },
  { convert ae_eq_refl _,
    ext1 x,
    rw [pdf, dif_neg hpdf, pi.zero_apply, ennreal.zero_to_real, ennreal.of_real_zero] }
end

lemma integrable_iff_integrable_mul_pdf [is_finite_measure ℙ] {X : α → E} [has_pdf X ℙ μ]
  (hX : measurable X) {f : E → ℝ} (hf : measurable f) :
  integrable (λ x, f (X x)) ℙ ↔ integrable (λ x, f x * (pdf X ℙ μ x).to_real) μ :=
begin
  rw [← integrable_map_measure hf.ae_measurable hX, map_eq_with_density_pdf X ℙ μ,
      integrable.with_density_iff (measurable_pdf _ _ _) (ae_lt_top _ hX) hf],
  apply_instance
end

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, f x * pdf X ∂μ`
where `μ` is a measure on the codomain of `X`. -/
lemma integral_mul_eq_integral' [is_finite_measure ℙ]
  {X : α → E} [has_pdf X ℙ μ] (hX : measurable X) {f : E → ℝ} (hf : measurable f) :
  ∫ x, f x * (pdf X ℙ μ x).to_real ∂μ = ∫ x, f (X x) ∂ℙ :=
begin
  by_cases hpdf : integrable (λ x, f x * (pdf X ℙ μ x).to_real) μ,
  { rw [← integral_map hX hf.ae_measurable, map_eq_with_density_pdf X ℙ μ,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hpdf,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
        lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.neg.ennreal_of_real,
        lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.ennreal_of_real],
    { congr' 2,
      { have : ∀ x, ennreal.of_real (f x * (pdf X ℙ μ x).to_real) =
          ennreal.of_real (pdf X ℙ μ x).to_real * ennreal.of_real (f x),
        { intro x,
          rw [mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
        simp_rw [this],
        exact lintegral_congr_ae (filter.eventually_eq.mul
          (of_real_to_real_ae_eq hX) (ae_eq_refl _)) },
      { have : ∀ x, ennreal.of_real (- (f x * (pdf X ℙ μ x).to_real)) =
          ennreal.of_real (pdf X ℙ μ x).to_real * ennreal.of_real (-f x),
        { intro x,
          rw [neg_mul_eq_neg_mul, mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
        simp_rw [this],
        exact lintegral_congr_ae (filter.eventually_eq.mul
          (of_real_to_real_ae_eq hX) (ae_eq_refl _)) } },
    { refine ⟨hf.ae_measurable, _⟩,
      rw [has_finite_integral, lintegral_with_density_eq_lintegral_mul _
            (measurable_pdf _ _ _) hf.nnnorm.coe_nnreal_ennreal],
      have : (λ x, (pdf X ℙ μ * λ x, ↑∥f x∥₊) x) =ᵐ[μ] (λ x, ∥f x * (pdf X ℙ μ x).to_real∥₊),
      { simp_rw [← smul_eq_mul, nnnorm_smul, ennreal.coe_mul],
        rw [smul_eq_mul, mul_comm],
        refine filter.eventually_eq.mul (ae_eq_refl _)
          (ae_eq_trans (of_real_to_real_ae_eq hX).symm _),
        convert ae_eq_refl _,
        ext1 x,
        exact real.ennnorm_eq_of_real ennreal.to_real_nonneg },
      rw lintegral_congr_ae this,
      exact hpdf.2 } },
  { rw [integral_undef hpdf, integral_undef],
    rwa ← integrable_iff_integrable_mul_pdf hX hf at hpdf,
    all_goals { apply_instance } }
end

/-- A random variable that `has_pdf` is quasi-measure preserving. -/
lemma to_quasi_measure_preserving {X : α → E} (hX : measurable X) [has_pdf X ℙ μ] :
  quasi_measure_preserving X ℙ μ :=
{ measurable := hX,
  absolutely_continuous :=
  begin
    rw map_eq_with_density_pdf X ℙ μ,
    exact with_density_absolutely_continuous _ _,
  end }

lemma map_absolutely_continuous {X : α → E} (hX : measurable X) [has_pdf X ℙ μ] :
  map X ℙ ≪ μ :=
(to_quasi_measure_preserving hX).absolutely_continuous

lemma have_lebesgue_decomposition_of_has_pdf {X : α → E} [hX' : has_pdf X ℙ μ] :
  (map X ℙ).have_lebesgue_decomposition μ :=
⟨⟨⟨0, pdf X ℙ μ⟩,
  by simp only [zero_add, measurable_pdf X ℙ μ, true_and, mutually_singular.zero.symm,
    map_eq_with_density_pdf X ℙ μ] ⟩⟩

lemma has_pdf_iff {X : α → E} (hX : measurable X) :
  has_pdf X ℙ μ ↔ (map X ℙ).have_lebesgue_decomposition μ ∧ map X ℙ ≪ μ :=
begin
  split,
  { intro hX',
    exactI ⟨have_lebesgue_decomposition_of_has_pdf, map_absolutely_continuous hX⟩, },
  { rintros ⟨h_decomp, h⟩,
    haveI := h_decomp,
    refine ⟨⟨(measure.map X ℙ).radon_nikodym_deriv μ, measurable_radon_nikodym_deriv _ _, _⟩⟩,
    rwa with_density_radon_nikodym_deriv_eq }
end

section

variables {F : Type*} [normed_group F] [measurable_space F] [second_countable_topology F]
  [normed_space ℝ F] [complete_space F] [borel_space F] {ν : measure F}

/-- A random variable that `has_pdf` transformed under a `quasi_measure_preserving`
map also `has_pdf` if `(map g (map X ℙ)).have_lebesgue_decomposition μ`.

`quasi_measure_preserving_has_pdf'` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
lemma quasi_measure_preserving_has_pdf {X : α → E} (hX : measurable X) [has_pdf X ℙ μ]
  {g : E → F} (hg : quasi_measure_preserving g μ ν)
  (hmap : (map g (map X ℙ)).have_lebesgue_decomposition ν) :
  has_pdf (g ∘ X) ℙ ν :=
begin
  rw [has_pdf_iff (hg.measurable.comp hX), ← map_map hg.measurable hX],
  refine ⟨hmap, _⟩,
  rw [map_eq_with_density_pdf X ℙ μ],
  refine absolutely_continuous.mk (λ s hsm hs, _),
  rw [map_apply hg.measurable hsm, with_density_apply _ (hg.measurable hsm)],
  have := hg.absolutely_continuous hs,
  rw map_apply hg.measurable hsm at this,
  exact set_lintegral_measure_zero _ _ this,
end

lemma quasi_measure_preserving_has_pdf' [is_finite_measure ℙ] [sigma_finite ν]
  {X : α → E} (hX : measurable X) [has_pdf X ℙ μ]
  {g : E → F} (hg : quasi_measure_preserving g μ ν) :
  has_pdf (g ∘ X) ℙ ν :=
begin
  haveI : is_finite_measure (map g (map X ℙ)) :=
    @is_finite_measure_map _ _ _ _ (map X ℙ) (is_finite_measure_map ℙ hX) _ hg.measurable,
  exact quasi_measure_preserving_has_pdf hX hg infer_instance,
end

end

section real

variables [is_finite_measure ℙ] {X : α → ℝ} (hX : measurable X)

include hX

/-- A real-valued random variable `X` `has_pdf X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
lemma real.has_pdf_iff : has_pdf X ℙ ↔ map X ℙ ≪ volume :=
begin
  haveI : is_finite_measure ((map X) ℙ) := is_finite_measure_map ℙ hX,
  rw [has_pdf_iff hX, and_iff_right_iff_imp],
  exact λ h, infer_instance,
end

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
lemma integral_mul_eq_integral [has_pdf X ℙ]:
  ∫ x, x * (pdf X ℙ volume x).to_real ∂(volume) = ∫ x, X x ∂ℙ :=
integral_mul_eq_integral' hX measurable_id

lemma has_finite_integral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞}
  (hg : pdf X ℙ =ᵐ[volume] g) (hgi : ∫⁻ x, ∥f x∥₊ * g x ∂(volume) < ∞) :
  has_finite_integral (λ x, f x * (pdf X ℙ volume x).to_real) volume :=
begin
  rw [has_finite_integral],
  have : (λ x, ↑∥f x∥₊ * g x) =ᵐ[volume] (λ x, ∥f x * (pdf X ℙ volume x).to_real∥₊),
  { refine ae_eq_trans (filter.eventually_eq.mul (ae_eq_refl (λ x, ∥f x∥₊))
      (ae_eq_trans hg.symm (of_real_to_real_ae_eq hX).symm)) _,
    simp_rw [← smul_eq_mul, nnnorm_smul, ennreal.coe_mul, smul_eq_mul],
    refine filter.eventually_eq.mul (ae_eq_refl _) _,
    convert ae_eq_refl _,
    ext1 x,
    exact real.ennnorm_eq_of_real ennreal.to_real_nonneg },
  rwa ← lintegral_congr_ae this,
end

end real

end pdf

end measure

end measure_theory
