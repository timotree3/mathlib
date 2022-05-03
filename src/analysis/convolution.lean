/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.group.integration
import measure_theory.group.prod
import measure_theory.function.locally_integrable
import analysis.calculus.specific_functions
import analysis.calculus.parametric_integral

/-!
# Convolution of functions

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x / t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a measure Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = lsmul ℝ ℝ` or `L = lmul ℝ ℝ`.

We also define `convolution_exists` and `convolution_exists_at` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `convolution_exists_at.distrib_add`), but are generally not stong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

# Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `has_compact_support.has_fderiv_at_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

# Main Definitions
* `convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x / t)) ∂μ` is the convolution of
  `f` and `g` w.r.t. the continuous bilinear map `L` and.
* `convolution_exists_at f g x L μ` states that the convolution `(f ⋆[L, μ] g) x` is well-defined
  (i.e. the integral exists).
* `convolution_exists f g L μ` states that the convolution `f ⋆[L, μ] g` is well-defined at each
  point.

# Main Results
* `has_compact_support.has_fderiv_at_convolution_right` and
  `has_compact_support.has_fderiv_at_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `has_compact_support.cont_diff_convolution_right` and
  `has_compact_support.cont_diff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.
* `convolution_tendsto_right`: Given a sequence of nonnegative normalized functions whose support
  tends to a small neighborhood around `0`, the convolution tends to the right argument.
  This is specialized to bump functions in `cont_diff_bump_of_inner.convolution_tendsto_right`.

# Notation
The following notations are localized in the locale `convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

# To do
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere
-/

open set function filter measure_theory measure_theory.measure topological_space
open continuous_linear_map metric
open_locale pointwise topological_space

variables {𝕜 G E E' E'' F : Type*}
variables [normed_group E] [normed_group E'] [normed_group E''] [normed_group F]
variables {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

section nondiscrete_normed_field

variables [nondiscrete_normed_field 𝕜]
variables [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]
variables (L : E →L[𝕜] E' →L[𝕜] F)

section no_measurability

variables [group G] [topological_space G]

@[to_additive]
lemma has_compact_support.mconvolution_integrand_bound_right (hcg : has_compact_support g)
  (hg : continuous g) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f t) (g (x / t))∥ ≤ ((tsupport g)⁻¹ * s).indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
begin
  refine le_indicator (λ t ht, _) (λ t ht, _) t,
  { refine (L.le_op_norm₂ _ _).trans _,
    exact mul_le_mul_of_nonneg_left
        (le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) $ x / t)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  { have : x / t ∉ support g,
    { refine mt (λ hxt, _) ht, refine ⟨_, _, set.inv_mem_inv.mpr (subset_closure hxt), hx, _⟩,
      rw [inv_div', div_mul_cancel'] },
    rw [nmem_support.mp this, (L _).map_zero, norm_zero] }
end

@[to_additive]
lemma continuous.mconvolution_integrand_fst [has_continuous_inv G] (hg : continuous g) (t : G) :
  continuous (λ x, L (f t) (g (x / t))) :=
L.continuous₂.comp₂ continuous_const $ hg.comp $ continuous_id.div continuous_const

@[to_additive]
lemma has_compact_support.mconvolution_integrand_bound_left (hcf : has_compact_support f)
  (hf : continuous f) {x t : G} {s : set G} (hx : x ∈ s) :
  ∥L (f (x / t)) (g t)∥ ≤ ((tsupport f)⁻¹ * s).indicator (λ t, ∥L∥ * (⨆ i, ∥f i∥) * ∥g t∥) t :=
by { convert hcf.mconvolution_integrand_bound_right L.flip hf hx,
  simp_rw [L.op_norm_flip, mul_right_comm] }

end no_measurability

section measurability

variables [measurable_space G] {μ : measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x / t))` is
  integrable. There are various conditions on `f` and `g` to prove this. -/
@[to_additive /-" The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x / t))` is
  integrable. There are various conditions on `f` and `g` to prove this. "-/]
def mconvolution_exists_at [has_div G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
integrable (λ t, L (f t) (g (x / t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x / t))` is integrable
  for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
@[to_additive /-" The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x / t))` is integrable
  for all `x : G`. There are various conditions on `f` and `g` to prove this. "-/]
def mconvolution_exists [has_div G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
∀ x : G, mconvolution_exists_at f g x L μ

section mconvolution_exists

variables {L}
@[to_additive]
lemma mconvolution_exists_at.integrable [has_div G] {x : G} (h : mconvolution_exists_at f g x L μ) :
  integrable (λ t, L (f t) (g (x / t))) μ :=
h

variables (L)

section group

variables [group G]
variables [has_measurable_mul₂ G] [has_measurable_inv G]

@[to_additive]
lemma measure_theory.ae_strongly_measurable.mconvolution_integrand' [sigma_finite μ]
  (hf : ae_strongly_measurable f μ)
  (hg : ae_strongly_measurable g $ map (λ (p : G × G), p.1 / p.2) (μ.prod μ)) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 / p.2))) (μ.prod μ) :=
L.ae_strongly_measurable_comp₂ hf.snd $ hg.comp_measurable $ measurable_fst.div measurable_snd

@[to_additive]
lemma measure_theory.ae_strongly_measurable.mconvolution_integrand_snd'
  (hf : ae_strongly_measurable f μ) {x : G}
  (hg : ae_strongly_measurable g $ map (λ t, x / t) μ) :
  ae_strongly_measurable (λ t, L (f t) (g (x / t))) μ :=
L.ae_strongly_measurable_comp₂ hf $ hg.comp_measurable $ measurable_id.const_sub x

@[to_additive]
lemma measure_theory.ae_strongly_measurable.mconvolution_integrand_swap_snd'
  {x : G} (hf : ae_strongly_measurable f $ map (λ t, x / t) μ)
  (hg : ae_strongly_measurable g μ) : ae_strongly_measurable (λ t, L (f (x / t)) (g t)) μ :=
L.ae_strongly_measurable_comp₂ (hf.comp_measurable $ measurable_id.const_sub x) hg

@[to_additive]
lemma bdd_above.mconvolution_exists_at' {x₀ : G}
  {s : set G} (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ / t))) ⊆ s)
  (hf : integrable_on f s μ)
  (hmf : ae_strongly_measurable f μ)
  (hbg : bdd_above ((λ i, ∥g i∥) '' ((λ t, t⁻¹ * x₀) ⁻¹' s)))
  (hmg : ae_strongly_measurable g $ map (λ t, x₀ / t) μ) :
    mconvolution_exists_at f g x₀ L μ :=
begin
  set s' := (λ t, t⁻¹ * x₀) ⁻¹' s,
  have : ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x₀ / t))∥ ≤ s.indicator (λ t, ∥L∥ * ∥f t∥ * ⨆ i : s', ∥g i∥) t,
  { refine eventually_of_forall _,
    refine le_indicator (λ t ht, _) (λ t ht, _),
    { refine (L.le_op_norm₂ _ _).trans _,
      refine mul_le_mul_of_nonneg_left
        (le_csupr_set hbg $ mem_preimage.mpr _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      rwa [inv_div', div_mul_cancel'] },
    { have : t ∉ support (λ t, L (f t) (g (x₀ / t))) := mt (λ h, h2s h) ht,
      rw [nmem_support.mp this, norm_zero] } },
  refine integrable.mono' _ _ this,
  { rw [integrable_indicator_iff hs], exact (hf.norm.const_mul _).mul_const _ },
  { exact hmf.mconvolution_integrand_snd' L hmg }
end

section left
variables [sigma_finite μ] [is_mul_left_invariant μ]

@[to_additive]
lemma measure_theory.ae_strongly_measurable.mconvolution_integrand_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f t) (g (x / t))) μ :=
hf.mconvolution_integrand_snd' L $ hg.mono' $ map_div_left_absolutely_continuous μ x

@[to_additive]
lemma measure_theory.ae_strongly_measurable.mconvolution_integrand_swap_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f (x / t)) (g t)) μ :=
(hf.mono' (map_div_left_absolutely_continuous μ x)).mconvolution_integrand_swap_snd' L hg

end left

section right

variables [sigma_finite μ] [is_mul_right_invariant μ]

@[to_additive]
lemma measure_theory.ae_strongly_measurable.mconvolution_integrand
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 / p.2))) (μ.prod μ) :=
hf.mconvolution_integrand' L $ hg.mono' (quasi_measure_preserving_div μ).absolutely_continuous

@[to_additive]
lemma measure_theory.integrable.mconvolution_integrand (hf : integrable f μ) (hg : integrable g μ) :
  integrable (λ p : G × G, L (f p.2) (g (p.1 / p.2))) (μ.prod μ) :=
begin
  have h_meas : ae_strongly_measurable (λ (p : G × G), (L (f p.2)) (g (p.1 / p.2))) (μ.prod μ) :=
    hf.ae_strongly_measurable.mconvolution_integrand L hg.ae_strongly_measurable,
  have h2_meas : ae_strongly_measurable (λ (y : G), ∫ (x : G), ∥(L (f y)) (g (x / y))∥ ∂μ) μ :=
    h_meas.prod_swap.norm.integral_prod_right',
  simp_rw [integrable_prod_iff' h_meas],
  refine ⟨eventually_of_forall (λ t, (L (f t)).integrable_comp (hg.comp_div_right t)), _⟩,
  refine integrable.mono' _ h2_meas (eventually_of_forall $
    λ t, (_ : _ ≤ ∥L∥ * ∥f t∥ * ∫ x, ∥g (x / t)∥ ∂μ)),
  { simp_rw [integral_div_right_eq_self (λ t, ∥ g t ∥)],
    exact (hf.norm.const_mul _).mul_const _ },
  { simp_rw [← integral_mul_left],
    rw [real.norm_of_nonneg],
    { exact integral_mono_of_nonneg (eventually_of_forall $ λ t, norm_nonneg _)
        ((hg.comp_div_right t).norm.const_mul _) (eventually_of_forall $ λ t, L.le_op_norm₂ _ _) },
    exact integral_nonneg (λ x, norm_nonneg _) }
end

@[to_additive]
lemma integrable.ae_mconvolution_exists (hf : integrable f μ) (hg : integrable g μ) :
  ∀ᵐ x ∂μ, mconvolution_exists_at f g x L μ :=
((integrable_prod_iff $ hf.ae_strongly_measurable.mconvolution_integrand L
  hg.ae_strongly_measurable).mp $ hf.mconvolution_integrand L hg).1

end right

variables [topological_space G] [topological_group G] [borel_space G]
  [second_countable_topology G] [sigma_compact_space G]

@[to_additive]
lemma has_compact_support.mconvolution_exists_at {x₀ : G}
  (h : has_compact_support (λ t, L (f t) (g (x₀ / t)))) (hf : locally_integrable f μ)
  (hg : continuous g) : mconvolution_exists_at f g x₀ L μ :=
((((homeomorph.inv G).trans $ homeomorph.mul_right x₀).compact_preimage.mpr h).bdd_above_image
  hg.norm.continuous_on).mconvolution_exists_at' L is_closed_closure.measurable_set subset_closure
  (hf h) hf.ae_strongly_measurable hg.ae_strongly_measurable

@[to_additive]
lemma has_compact_support.mconvolution_exists_right
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g) :
  mconvolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.mconvolution_exists_at L _ hf hg,
  refine (hcg.comp_homeomorph (homeomorph.div_left x₀)).mono _,
  refine λ t, mt (λ ht : g (x₀ / t) = 0, _),
  simp_rw [ht, (L _).map_zero]
end

@[to_additive]
lemma has_compact_support.mconvolution_exists_left_of_continuous_right
  (hcf : has_compact_support f) (hf : locally_integrable f μ) (hg : continuous g) :
  mconvolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.mconvolution_exists_at L _ hf hg,
  refine hcf.mono _,
  refine λ t, mt (λ ht : f t = 0, _),
  simp_rw [ht, L.map_zero₂]
end

end group

section comm_group

variables [comm_group G]

section measurable_group

variables [has_measurable_mul₂ G] [has_measurable_inv G] [is_mul_left_invariant μ]

@[to_additive]
lemma bdd_above.mconvolution_exists_at [sigma_finite μ] {x₀ : G}
  {s : set G} (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ / t))) ⊆ s)
  (hf : integrable_on f s μ)
  (hmf : ae_strongly_measurable f μ)
  (hbg : bdd_above ((λ i, ∥g i∥) '' ((λ t, x₀ / t) ⁻¹' s)))
  (hmg : ae_strongly_measurable g μ) :
    mconvolution_exists_at f g x₀ L μ :=
begin
  refine bdd_above.mconvolution_exists_at' L hs h2s hf hmf _ _,
  { simp_rw [← div_eq_inv_mul, hbg] },
  { exact hmg.mono' (map_div_left_absolutely_continuous μ x₀) }
end

variables {L} [is_inv_invariant μ]

@[to_additive]
lemma mconvolution_exists_at_flip :
  mconvolution_exists_at g f x L.flip μ ↔ mconvolution_exists_at f g x L μ :=
by simp_rw [mconvolution_exists_at, ← integrable_comp_div_left (λ t, L (f t) (g (x / t))) x,
  div_div_cancel, flip_apply]

@[to_additive]
lemma mconvolution_exists_at.integrable_swap (h : mconvolution_exists_at f g x L μ) :
  integrable (λ t, L (f (x / t)) (g t)) μ :=
by { convert h.comp_div_left x, simp_rw [div_div_self'] }

@[to_additive]
lemma mconvolution_exists_at_iff_integrable_swap :
  mconvolution_exists_at f g x L μ ↔ integrable (λ t, L (f (x / t)) (g t)) μ :=
mconvolution_exists_at_flip.symm

end measurable_group

variables [topological_space G] [topological_group G] [borel_space G]
  [second_countable_topology G] [is_mul_left_invariant μ] [is_inv_invariant μ]
  [sigma_compact_space G]

@[to_additive]
lemma has_compact_support.mconvolution_exists_left
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
  mconvolution_exists f g L μ :=
λ x₀, mconvolution_exists_at_flip.mp $ hcf.mconvolution_exists_right L.flip hg hf x₀

@[to_additive]
lemma has_compact_support.mconvolution_exists_right_of_continuous_left
  (hcg : has_compact_support g) (hf : continuous f) (hg : locally_integrable g μ) :
  mconvolution_exists f g L μ :=
λ x₀, mconvolution_exists_at_flip.mp $
  hcg.mconvolution_exists_left_of_continuous_right L.flip hg hf x₀

end comm_group

end mconvolution_exists

variables [normed_space ℝ F] [complete_space F]

/-- The convolution of two functions `f` and `g`. -/
@[to_additive /-" The convolution of two functions `f` and `g`. "-/]
noncomputable def mconvolution [has_div G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : G → F :=
λ x, ∫ t, L (f t) (g (x / t)) ∂μ

localized "notation f ` ⋆[`:67 L:67 `, ` μ:67 `] `:0 g:66 := mconvolution f g L μ" in convolution
localized "notation f ` ⋆[`:67 L:67 `]`:0 g:66 := mconvolution f g L
  measure_theory.measure_space.volume" in convolution
localized "notation f ` ⋆ `:67 g:66 := mconvolution f g (continuous_linear_map.lsmul ℝ ℝ)
  measure_theory.measure_space.volume" in convolution

@[to_additive]
lemma mconvolution_def [has_div G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x / t)) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
@[to_additive /-" The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. "-/]
lemma mconvolution_lsmul [has_div G] {f : G → 𝕜} {g : G → F}:
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x / t) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
@[to_additive /-" The definition of convolution where the bilinear operator is multiplication. "-/]
lemma mconvolution_lmul [has_div G] [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[lmul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x / t) ∂μ := rfl

section group

variables {L} [group G]

@[to_additive]
lemma smul_mconvolution [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : (y • f) ⋆[L, μ] g = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, mconvolution_def, ← integral_smul, L.map_smul₂] }

@[to_additive]
lemma mconvolution_smul [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : f ⋆[L, μ] (y • g) = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, mconvolution_def, ← integral_smul, (L _).map_smul] }

@[to_additive]
lemma zero_mconvolution : 0 ⋆[L, μ] g = 0 :=
by { ext, simp_rw [mconvolution_def, pi.zero_apply, L.map_zero₂, integral_zero] }

@[to_additive]
lemma mconvolution_zero : f ⋆[L, μ] 0 = 0 :=
by { ext, simp_rw [mconvolution_def, pi.zero_apply, (L _).map_zero, integral_zero] }

@[to_additive]
lemma mconvolution_exists_at.distrib_add {x : G} (hfg : mconvolution_exists_at f g x L μ)
  (hfg' : mconvolution_exists_at f g' x L μ) :
  (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x :=
by simp only [mconvolution_def, (L _).map_add, pi.add_apply, integral_add hfg hfg']

@[to_additive]
lemma mconvolution_exists.distrib_add (hfg : mconvolution_exists f g L μ)
  (hfg' : mconvolution_exists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' :=
by { ext, exact (hfg x).distrib_add (hfg' x) }

@[to_additive]
lemma mconvolution_exists_at.add_distrib {x : G} (hfg : mconvolution_exists_at f g x L μ)
  (hfg' : mconvolution_exists_at f' g x L μ) :
  ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x :=
by simp only [mconvolution_def, L.map_add₂, pi.add_apply, integral_add hfg hfg']

@[to_additive]
lemma mconvolution_exists.add_distrib (hfg : mconvolution_exists f g L μ)
  (hfg' : mconvolution_exists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g :=
by { ext, exact (hfg x).add_distrib (hfg' x) }

variables (L)

@[to_additive]
lemma mconvolution_congr [has_measurable_mul G] [has_measurable_inv G] [is_mul_left_invariant μ]
  [is_inv_invariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') :
  f ⋆[L, μ] g = f' ⋆[L, μ] g' :=
begin
  ext x,
  apply integral_congr_ae,
  exact (h1.prod_mk $ h2.comp_tendsto (map_div_left_ae μ x).le).fun_comp ↿(λ x y, L x y)
end

@[to_additive]
lemma support_mconvolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g * support f :=
begin
  intros x h2x,
  by_contra hx,
  apply h2x,
  simp_rw [set.mem_mul, not_exists, not_and_distrib, nmem_support] at hx,
  rw [mconvolution_def],
  convert integral_zero G F,
  ext t,
  rcases hx (x / t) t with h|h|h,
  { rw [h, (L _).map_zero] },
  { rw [h, L.map_zero₂] },
  { exact (h $ inv_mul_cancel' x t).elim }
end

variables [topological_space G]
variables [topological_group G]

@[to_additive]
lemma has_compact_support.mconvolution [t2_space G] (hcf : has_compact_support f)
  (hcg : has_compact_support g) : has_compact_support (f ⋆[L, μ] g) :=
compact_of_is_closed_subset (hcg.is_compact.mul hcf) is_closed_closure $ closure_minimal
  ((support_mconvolution_subset_swap L).trans $ mul_subset_mul subset_closure subset_closure)
  (hcg.is_compact.mul hcf).is_closed

variables [borel_space G] [second_countable_topology G] [sigma_finite μ]
variables [is_mul_right_invariant μ]

@[to_additive]
lemma integrable.integrable_mconvolution (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⋆[L, μ] g) μ :=
(hf.mconvolution_integrand L hg).integral_prod_left

/-- The convolution is continuous if one function is locally integrable and the other has compact
  support and is continuous. -/
@[to_additive /-" The convolution is continuous if one function is locally integrable and the other has compact
  support and is continuous. "-/]
lemma has_compact_support.continuous_mconvolution_right [locally_compact_space G] [t2_space G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g)
  (hg : continuous g) : continuous (f ⋆[L, μ] g) :=
begin
  refine continuous_iff_continuous_at.mpr (λ x₀, _),
  obtain ⟨K, hK, h2K⟩ := exists_compact_mem_nhds x₀,
  let K' := (tsupport g)⁻¹ * K,
  have hK' : is_compact K' := hcg.neg.add hK,
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x / t))∥ ≤ K'.indicator (λ t, ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥)) t :=
  eventually_of_mem h2K (λ x hx, eventually_of_forall $
    λ t, hcg.mconvolution_integrand_bound_right L hg hx),
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall
      (λ x, hf.ae_strongly_measurable.mconvolution_integrand_snd' L hg.ae_strongly_measurable) },
  { rw [integrable_indicator_iff hK'.measurable_set],
    exact ((hf hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous₂.comp₂ continuous_const $
      hg.comp $ continuous_id.div $ by apply continuous_const).continuous_at) }
end

/-- The convolution is continuous if one function is integrable and the other is bounded and
  continuous. -/
@[to_additive /-" The convolution is continuous if one function is integrable and the other is bounded and
  continuous. "-/]
lemma bdd_above.continuous_mconvolution_right_of_integrable
  (hf : integrable f μ) (hbg : bdd_above (range (λ x, ∥g x∥))) (hg : continuous g) :
    continuous (f ⋆[L, μ] g) :=
begin
  refine continuous_iff_continuous_at.mpr (λ x₀, _),
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ∥L (f t) (g (x / t))∥ ≤ ∥L∥ * ∥f t∥ * (⨆ i, ∥g i∥),
  { refine eventually_of_forall (λ x, eventually_of_forall $ λ t, _),
    refine (L.le_op_norm₂ _ _).trans _,
    exact mul_le_mul_of_nonneg_left (le_csupr hbg $ x / t)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall
      (λ x, hf.ae_strongly_measurable.mconvolution_integrand_snd' L hg.ae_strongly_measurable) },
  { exact (hf.norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous₂.comp₂ continuous_const $
      hg.comp $ continuous_id.div $ by apply continuous_const).continuous_at) }
end

end group

section comm_group

variables [comm_group G]

@[to_additive]
lemma support_mconvolution_subset : support (f ⋆[L, μ] g) ⊆ support f * support g :=
(support_mconvolution_subset_swap L).trans (mul_comm _ _).subset

variables [topological_space G]
variables [topological_group G]
variables [borel_space G]
variables [is_mul_left_invariant μ]  [is_inv_invariant μ]

variable (L)
/-- Commutativity of convolution -/
@[to_additive /-" Commutativity of convolution "-/]
lemma mconvolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g :=
begin
  ext1 x,
  simp_rw [mconvolution_def],
  rw [← integral_sub_left_eq_self _ μ x],
  simp_rw [sub_sub_self, flip_apply]
end

/-- The symmetric definition of convolution. -/
@[to_additive /-" The symmetric definition of convolution. "-/]
lemma mconvolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x / t)) (g t) ∂μ :=
by { rw [← mconvolution_flip], refl }

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
@[to_additive /-" The symmetric definition of convolution where the bilinear operator is scalar multiplication. "-/]
lemma mconvolution_lsmul_swap {f : G → 𝕜} {g : G → F}:
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x / t) • g t ∂μ :=
mconvolution_eq_swap _

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
@[to_additive /-" The symmetric definition of convolution where the bilinear operator is multiplication. "-/]
lemma mconvolution_lmul_swap [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[lmul 𝕜 𝕜, μ] g) x = ∫ t, f (x / t) * g t ∂μ :=
mconvolution_eq_swap _

variables [second_countable_topology G] [sigma_finite μ]

@[to_additive]
lemma has_compact_support.continuous_mconvolution_left [locally_compact_space G] [t2_space G]
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
by { rw [← mconvolution_flip], exact hcf.continuous_mconvolution_right L.flip hg hf }

@[to_additive]
lemma bdd_above.continuous_mconvolution_left_of_integrable
  (hbf : bdd_above (range (λ x, ∥f x∥))) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
by { rw [← mconvolution_flip], exact hbf.continuous_mconvolution_right_of_integrable L.flip hg hf }

/-- A version of `has_compact_support.continuous_mconvolution_left` that works if `G` is
  not locally compact but requires that `g` is integrable. -/
@[to_additive /-" A version of `has_compact_support.continuous_convolution_left` that works if `G` is
  not locally compact but requires that `g` is integrable. "-/]
lemma has_compact_support.continuous_mconvolution_left_of_integrable
  (hcf : has_compact_support f) (hf : continuous f) (hg : integrable g μ) :
    continuous (f ⋆[L, μ] g) :=
(hf.norm.bdd_above_range_of_has_compact_support hcf.norm).continuous_mconvolution_left_of_integrable
  L hf hg

end comm_group

section normed_group

variables [semi_normed_group G]

/-- We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)`.
  TODO: add a version that assumes `antilipschitz_with` on `L`. -/
@[to_additive /-" We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)`. "-/]
lemma mconvolution_eq_right' {x₀ : G} {R : ℝ}
  (hf : support f ⊆ ball (0 : G) R)
  (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ (t : G), (L (f t)) (g x₀) ∂μ :=
begin
  have h2 : ∀ t, L (f t) (g (x₀ / t)) = L (f t) (g x₀),
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ / t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      rw [hg h2t] },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂] } },
  simp_rw [mconvolution_def, h2],
end

variables [borel_space G] [second_countable_topology G]
variables [is_mul_left_invariant μ] [sigma_finite μ]

--measurable_set_ball can be pseudo_metric_space

@[to_additive]
lemma dist_mconvolution_le' {x₀ : G} {R ε : ℝ}
  (hif : integrable f μ)
  (hR : 0 < R) -- todo: remove this assumption(?)
  (hf : support f ⊆ ball (0 : G) R)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) (g x₀) ≤ ε) :
  dist ((f ⋆[L, μ] g : G → F) x₀) (∫ (t : G), (L (f t)) (g x₀) ∂μ) ≤ ∥L∥ * ∫ x, ∥f x∥ ∂μ * ε :=
begin
  have hε : 0 ≤ ε, { convert hg x₀ (mem_ball_self hR), rw dist_self },
  have hfg : mconvolution_exists_at f g x₀ L μ,
  { refine bdd_above.mconvolution_exists_at L metric.is_open_ball.measurable_set (subset_trans _ hf)
      hif.integrable_on hif.ae_strongly_measurable _ hmg,
    { refine λ t, mt (λ ht : f t = 0, _), simp_rw [ht, L.map_zero₂] },
    rw [bdd_above_def],
    refine ⟨∥g x₀∥ + ε, _⟩,
    rintro _ ⟨x, hx, rfl⟩,
    refine norm_le_norm_add_const_of_dist_le (hg x _),
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff] },
  have h2 : ∀ t, dist (L (f t) (g (x₀ / t))) (L (f t) (g x₀)) ≤ ∥L (f t)∥ * ε,
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ / t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      refine ((L (f t)).dist_le_op_norm _ _).trans _,
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _) },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self] } },
  simp_rw [mconvolution_def],
  simp_rw [dist_eq_norm] at h2 ⊢,
  rw [← integral_sub hfg.integrable], swap, { exact (L.flip (g x₀)).integrable_comp hif },
  refine (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
    (eventually_of_forall h2)).trans _,
  rw [integral_mul_right],
  refine mul_le_mul_of_nonneg_right _ hε,
  have h3 : ∀ t, ∥L (f t)∥ ≤ ∥L∥ * ∥f t∥ := λ t, L.le_op_norm (f t),
  refine (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq _,
  rw [integral_mul_left]
end

variables [normed_space ℝ E] [normed_space ℝ E'] [complete_space E']

@[to_additive]
lemma dist_mconvolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ}
  (hR : 0 < R) -- todo: remove this assumption(?)
  (hf : support f ⊆ ball (0 : G) R)
  (hnf : ∀ x, 0 ≤ f x)
  (hintf : ∫ x, f x ∂μ = 1)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) (g x₀) ≤ ε) :
  dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
begin
  have hε : 0 ≤ ε, { convert hg x₀ (mem_ball_self hR), rw dist_self },
  have hif : integrable f μ,
  { by_contra hif, exact zero_ne_one ((integral_undef hif).symm.trans hintf) },
  convert (dist_mconvolution_le' _ hif hR hf hmg hg).trans _,
  { simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul] },
  { simp_rw [real.norm_of_nonneg (hnf _), hintf, mul_one],
    convert (mul_le_mul_of_nonneg_right op_norm_lsmul_le hε).trans_eq (one_mul ε) }
end

@[to_additive]
lemma mconvolution_tendsto_right {ι} {l : filter ι} {φ : ι → G → ℝ}
  (hnφ : ∀ i x, 0 ≤ φ i x)
  (hiφ : ∀ i, ∫ s, φ i s ∂μ = 1)
  (hφ : tendsto (λ n, support (φ n)) l (𝓝 0).small_sets)
  (hmg : ae_strongly_measurable g μ) {x₀ : G} (hcg : continuous_at g x₀) :
  tendsto (λ i, (φ i ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
begin
  simp_rw [tendsto_small_sets_iff] at hφ,
  rw [metric.continuous_at_iff] at hcg,
  rw [metric.tendsto_nhds],
  intros ε hε,
  rcases hcg (ε / 2) (half_pos hε) with ⟨δ, hδ, hgδ⟩,
  refine (hφ (ball (0 : G) δ) $ ball_mem_nhds _ hδ).mono (λ i hi, _),
  exact (dist_mconvolution_le hδ hi (hnφ i) (hiφ i) hmg (λ x hx, (hgδ hx.out).le)).trans_lt
    (half_lt_self hε)
end

end normed_group

namespace cont_diff_bump_of_inner

variables {n : with_top ℕ}
variables [normed_space ℝ E']
variables [inner_product_space ℝ G]
variables [complete_space E']
variables {a : G} {φ : cont_diff_bump_of_inner (0 : G)}

@[to_additive]
lemma mconvolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ :=
by simp_rw [mconvolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

variables [borel_space G]
variables [is_locally_finite_measure μ] [is_open_pos_measure μ]
variables [finite_dimensional ℝ G]

@[to_additive]
lemma normed_mconvolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ :=
by { simp_rw [mconvolution_eq_right' _ φ.support_normed_eq.subset hg, lsmul_apply],
  exact integral_normed_smul φ μ (g x₀) }

variables [is_mul_left_invariant μ]

@[to_additive]
lemma dist_normed_mconvolution_le {x₀ : G} {ε : ℝ}
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ φ.R, dist (g x) (g x₀) ≤ ε) :
  dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
dist_mconvolution_le φ.R_pos φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg

@[to_additive]
lemma mconvolution_tendsto_right' {ι} {φ : ι → cont_diff_bump_of_inner (0 : G)}
  {l : filter ι} (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hmg : ae_strongly_measurable g μ) {x₀ : G} (hcg : continuous_at g x₀) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
begin
  refine mconvolution_tendsto_right (λ i, (φ i).nonneg_normed) (λ i, (φ i).integral_normed)
    _ hmg hcg,
  rw [normed_group.tendsto_nhds_zero] at hφ,
  rw [tendsto_small_sets_iff],
  intros t ht,
  rcases metric.mem_nhds_iff.mp ht with ⟨ε, hε, ht⟩,
  refine (hφ ε hε).mono (λ i hi, subset_trans _ ht),
  simp_rw [(φ i).support_normed_eq],
  rw [real.norm_eq_abs, abs_eq_self.mpr (φ i).R_pos.le] at hi,
  exact ball_subset_ball hi.le
end

@[to_additive]
lemma mconvolution_tendsto_right {ι} {φ : ι → cont_diff_bump_of_inner (0 : G)}
  {l : filter ι} (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hg : continuous g) (x₀ : G) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
mconvolution_tendsto_right' hφ hg.ae_strongly_measurable hg.continuous_at

end cont_diff_bump_of_inner

end measurability

end nondiscrete_normed_field

open_locale convolution


section normed_space
-- (`𝕜` cannot be nondiscrete_normed_field, because of `continuous_linear_map.integral_apply`)
variables [is_R_or_C 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space 𝕜 E'']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables [normed_group G]
variables {n : with_top ℕ}
variables [complete_space F]
variables [measurable_space G] [borel_space G] {μ : measure G} [second_countable_topology G]
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [sigma_finite μ] [sigma_compact_space G]
variables [is_mul_left_invariant μ]

@[to_additive]
lemma mconvolution_precompR_apply {g : G → E'' →L[𝕜] E'}
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g)
  (x₀ : G) (x : E'') : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] (λ a, g a x)) x₀  :=
begin
  have := hcg.mconvolution_exists_right (L.precompR E'') hf hg x₀,
  simp_rw [mconvolution_def, continuous_linear_map.integral_apply this],
  refl,
end

variables [normed_space 𝕜 G] [proper_space G]

@[to_additive]
lemma has_compact_support.has_fderiv_at_mconvolution_right
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : cont_diff 𝕜 1 g) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ :=
begin
  set L' := L.precompR G,
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (λ t, L (f t) (g (x / t))) μ :=
  eventually_of_forall
    (hf.ae_strongly_measurable.mconvolution_integrand_snd L hg.continuous.ae_strongly_measurable),
  have h2 : ∀ x, ae_strongly_measurable (λ t, L' (f t) (fderiv 𝕜 g (x / t))) μ,
  { exact hf.ae_strongly_measurable.mconvolution_integrand_snd L'
      (hg.continuous_fderiv le_rfl).ae_strongly_measurable },
  have h3 : ∀ x t, has_fderiv_at (λ x, g (x / t)) (fderiv 𝕜 g (x / t)) x,
  { intros x t,
    simpa using (hg.differentiable le_rfl).differentiable_at.has_fderiv_at.comp x
      ((has_fderiv_at_id x).div (has_fderiv_at_const t x)) },
  let K' := - tsupport (fderiv 𝕜 g) + closed_ball x₀ 1,
  have hK' : is_compact K' := (hcg.fderiv 𝕜).neg.add (is_compact_closed_ball x₀ 1),
  refine has_fderiv_at_integral_of_dominated_of_fderiv_le
    zero_lt_one h1 _ (h2 x₀) _ _ _,
  { exact K'.indicator (λ t, ∥L'∥ * ∥f t∥ * (⨆ x, ∥fderiv 𝕜 g x∥)) },
  { exact hcg.mconvolution_exists_right L hf hg.continuous x₀ },
  { refine eventually_of_forall (λ t x hx, _),
    exact (hcg.fderiv 𝕜).mconvolution_integrand_bound_right L'
      (hg.continuous_fderiv le_rfl) (ball_subset_closed_ball hx) },
  { rw [integrable_indicator_iff hK'.measurable_set],
    exact ((hf hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t x hx, (L _).has_fderiv_at.comp x (h3 x t)) },
end

@[to_additive]
lemma has_compact_support.has_fderiv_at_mconvolution_left [is_inv_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 1 f) (hg : locally_integrable g μ) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ :=
begin
  simp only [← mconvolution_flip] {single_pass := tt},
  exact hcf.has_fderiv_at_mconvolution_right L.flip hg hf x₀,
end

@[to_additive]
lemma has_compact_support.cont_diff_mconvolution_right [finite_dimensional 𝕜 G]
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
begin
  induction n using with_top.nat_induction with n ih ih generalizing g,
  { rw [cont_diff_zero] at hg ⊢,
    exact hcg.continuous_mconvolution_right L hf hg },
  { have h : ∀ x, has_fderiv_at (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x) x :=
      hcg.has_fderiv_at_mconvolution_right L hf hg.one_of_succ,
    rw cont_diff_succ_iff_fderiv_apply,
    split,
    { exact λ x₀, ⟨_, h x₀⟩ },
    { simp_rw [fderiv_eq h, mconvolution_precompR_apply L hf (hcg.fderiv 𝕜)
        (hg.one_of_succ.continuous_fderiv le_rfl)],
      intro x,
      refine ih _ _,
      { refine @has_compact_support.comp_left _ _ _ _ _ _ (λ (G : _ →L[𝕜] _), G x) _
          (hcg.fderiv 𝕜) (continuous_linear_map.zero_apply x) },
      { revert x, rw [← cont_diff_clm_apply],
        exact (cont_diff_succ_iff_fderiv.mp hg).2 } } },
  { rw [cont_diff_top] at hg ⊢, exact λ n, ih n hcg (hg n) }
end

@[to_additive]
lemma has_compact_support.cont_diff_mconvolution_left [finite_dimensional 𝕜 G] [is_inv_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 n f) (hg : locally_integrable g μ) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
begin
  rw [← mconvolution_flip],
  exact hcf.cont_diff_mconvolution_right L.flip hg hf,
end

variables {F' F'' : Type*}
variables [normed_group E''] [normed_space 𝕜 E'']
variables [normed_group F'] [normed_space ℝ F'] [normed_space 𝕜 F'] [complete_space F']
variables [normed_group F''] [normed_space ℝ F''] [normed_space 𝕜 F''] [complete_space F'']
variables {k : G → E''}
variables (L₂ : F →L[𝕜] E'' →L[𝕜] F')
variables (L₃ : E →L[𝕜] F'' →L[𝕜] F')
variables (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')

/-- convolution is associative.
To do: prove that `hi` follows from simpler conditions. -/
@[to_additive /-" convolution is associative. "-/]
lemma mconvolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
  {x₀ : G}
  (h₄ : mconvolution_exists g k L₄ μ)
  (h₁ : mconvolution_exists f g L μ)
  (hi : integrable (uncurry (λ x y, (L₃ (f y)) ((L₄ (g (x / y))) (k (x₀ - x))))) (μ.prod μ)) :
  ((f ⋆[L, μ] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, μ] (g ⋆[L₄, μ] k)) x₀ :=
begin
  have h1 := λ t, (L₂.flip (k (x₀ / t))).integral_comp_comm (h₁ t),
  dsimp only [flip_apply] at h1,
  simp_rw [mconvolution_def, ← (L₃ (f _)).integral_comp_comm (h₄ (x₀ - _)), ← h1, hL],
  rw [integral_integral_swap hi],
  congr', ext t,
  rw [eq_comm, ← integral_sub_right_eq_self _ t],
  simp_rw [sub_sub_sub_cancel_right],
end

end normed_space

section real
/-! The one-variable case -/

variables [is_R_or_C 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}
variables {n : with_top ℕ}
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [complete_space F]
variables {μ : measure 𝕜}
variables [is_mul_left_invariant μ] [sigma_finite μ]

@[to_additive]
lemma has_compact_support.has_deriv_at_mconvolution_right
  (hf : locally_integrable f₀ μ) (hcg : has_compact_support g₀) (hg : cont_diff 𝕜 1 g₀)
  (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ :=
begin
  convert (hcg.has_fderiv_at_mconvolution_right L hf hg x₀).has_deriv_at,
  rw [mconvolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)],
  refl,
end

@[to_additive]
lemma has_compact_support.has_deriv_at_mconvolution_left [is_inv_invariant μ]
  (hcf : has_compact_support f₀) (hf : cont_diff 𝕜 1 f₀)
  (hg : locally_integrable g₀ μ) (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ :=
begin
  simp only [← mconvolution_flip] {single_pass := tt},
  exact hcf.has_deriv_at_mconvolution_right L.flip hg hf x₀,
end

end real
