/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import analysis.calculus.fderiv
import analysis.calculus.mean_value
import analysis.convex.topology
import analysis.normed_space.is_R_or_C
import data.complex.is_R_or_C
import order.filter.basic

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `has_fderiv_at_of_tendsto_uniformly_on`.

## Main statements

* `has_fderiv_at_of_tendsto_uniformly_on` : If `f : ℕ → E → G` is a sequence of functions with
  derivatives `f' : ℕ → (E → (E →L[𝕜] G))` and the `f` converge pointwise to `g` and the `f'`
  converge _uniformly_ on some closed ball, then the derivative of `g'` is the pointwise limit
  of the `f'` on the closed ball

## Implementation notes

Our proof utilizes three major components:
  * `convex.norm_image_sub_le_of_norm_has_fderiv_within_le`: The mean value inequality for
    vector-valued functions over `ℝ` and `ℂ`
  * `norm_add_le`: The triangle inequality
  * `uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto` which allows us to upgrade pointwise
    convergence to uniform convergence by showing that the Cauchy sequences converge uniformly to 0

## Tags

uniform convergence, limits of derivatives
-/

open finset filter metric
open_locale uniformity filter

section convenience_lemmas

/-- Convenience lemma -/
private lemma mul_cancel_inv_left₀ {a b : ℝ} (ha : a ≠ 0) : a⁻¹ * (a * b) = b :=
 begin
  conv { congr, congr, skip, rw ←inv_inv a, },
  have : a⁻¹ ≠ 0, simp [ha],
  rw mul_inv_cancel_left₀ this,
end

/-- We'll need to apply the triangle ineqaulity twice, which is easier to do in lemma
format -/
private lemma norm_add_three_le {E : Type*} [semi_normed_group E] {a b c : E} :
  ∥a + b + c∥ ≤ ∥a∥ + ∥b∥ + ∥c∥ :=
begin
  refine le_trans (norm_add_le _ _) _,
  exact add_le_add (norm_add_le _ _) rfl.le,
end

/-- Convenience lemma for three way comparisons -/
private lemma lt_of_lt_of_lt_of_le {a b c a' b' c': ℝ} :
  a < a' → b < b' → c ≤ c' → a + b + c < a' + b' + c' :=
begin
  intros ha hb hc,
  linarith [ha, hb, hc],
end

end convenience_lemmas

section limits_of_derivatives

variables {E : Type*} [normed_group E] {𝕜 : Type*} {G : Type*}
  [is_R_or_C 𝕜] [normed_group G] [normed_space 𝕜 G]
  {f : ℕ → E → G} {g : E → G} {x y z : E} {r R C : ℝ}

/-- For fixed y and z, if `f_n → g` pointwise, then the difference quotients
`∥z - y∥⁻¹ • (f_n z - f_n y)` converge to the difference quotients
`∥z - y∥⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge
  (hfg : ∀ (y : E), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y))) :
  ∀ y : E, y ∈ closed_ball x r → ∀ z : E, z ∈ closed_ball x r →
    tendsto (λ n : ℕ, (∥z - y∥⁻¹ : 𝕜) • (f n z - f n y))
      at_top (nhds ((∥z - y∥⁻¹ : 𝕜) • (g z - g y))) :=
(λ y hy z hz, ((hfg z hz).sub (hfg y hy)).const_smul _)

variables [normed_space ℝ E] [normed_space 𝕜 E] {f' : ℕ → (E → (E →L[𝕜] G))} {g' : E → (E →L[𝕜] G)}

/-- A convenience theorem for utilizing the mean value theorem for differences of
differentiable functions -/
lemma mean_value_theorem_for_differences {f : E → G} {f' : E → (E →L[𝕜] G)}
  (hrR : r < R) (hf : ∀ (y : E), y ∈ ball x R → has_fderiv_at f (f' y) y)
  (hg : ∀ (y : E), y ∈ ball x R → has_fderiv_at g (g' y) y)
  (hbound : ∀ (y : E), y ∈ closed_ball x r → ∥f' y - g' y∥ ≤ C)
  (hy : y ∈ closed_ball x r) (hz : z ∈ closed_ball x r) :
  ∥y - z∥⁻¹ * ∥(f y - g y) - (f z - g z)∥ ≤ C :=
begin
  -- Differences of differentiable functions are differentiable and closed balls are
  -- convex, so a bit of annoying symbol pushing will get us the actual theorem

  -- Closed balls are convex
  have hconvex := convex_closed_ball x r,

  -- Differences of differentiable functions are differentiable
  have hderiv : ∀ (y : E), y ∈ closed_ball x r →
    has_fderiv_within_at (f - g) ((f' - g') y) (closed_ball x r) y,
  { intros y hy,
    have : y ∈ ball x R, {calc dist y x ≤ r : hy ... < R : hrR,},
    have := ((hf y this).sub (hg y this)).has_fderiv_within_at,
    simp only [pi.sub_apply],
    have : (λ x : E, f x - g x) = f - g, { funext, simp only [pi.sub_apply], },
    rwa ←this, },

  -- Apply the mean value theorem
  have := convex.norm_image_sub_le_of_norm_has_fderiv_within_le
    hderiv hbound hconvex hz hy,

  -- Auxiliary lemmas necessary for algebraic manipulation
  have h_le : ∥y - z∥⁻¹ ≤ ∥y - z∥⁻¹, { exact le_refl _, },
  have C_nonneg : 0 ≤ C,
  { calc 0 ≤ ∥f' y - g' y∥ : norm_nonneg _ ... ≤ C : hbound y hy, },
  have h_le' : 0 ≤ C * ∥y - z∥, exact mul_nonneg C_nonneg (by simp),

  -- The case y = z is degenerate. Eliminate it
  by_cases h : y = z,
  { simp only [h, C_nonneg, sub_self, norm_zero, mul_zero], },
  have h_ne_zero : ∥y - z∥ ≠ 0,
  { simp only [ne.def, norm_eq_zero],
    exact λ hh, h (sub_eq_zero.mp hh), },

  -- Final manipulation
  have := mul_le_mul this h_le (by simp) h_le',
  simp only [pi.sub_apply] at this,
  rw mul_inv_cancel_right₀ h_ne_zero at this,
  rwa mul_comm,
end

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `∥z - y∥⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `∥z - y∥⁻¹ • (g z - g y)` -/
lemma difference_quotients_converge_uniformly
  (hrR : r < R)
  (hf : ∀ (n : ℕ), ∀ (y : E), y ∈ ball x R → has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
  ∀ y : E, y ∈ closed_ball x r →
    tendsto_uniformly_on
      (λ n : ℕ, λ z : E, (∥z - y∥⁻¹ : 𝕜) • ((f n z) - (f n y)))
      (λ z : E, (∥z - y∥⁻¹ : 𝕜) • ((g z) - (g y))) at_top ((closed_ball x r)) :=
begin
  -- Proof strategy: Rewrite the Cauchy sequence of difference quotients as
  -- a difference quotient. Then apply the mean value theorem and the uniform
  -- convergence of the difference of derivatives
  intros y hy,
  refine uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto _
    (difference_quotients_converge hfg y hy),
  rw uniform_cauchy_seq_on_iff,
  intros ε hε,
  have := hfg'.uniform_cauchy_seq_on,
  rw metric.uniform_cauchy_seq_on_iff at this,
  have half_eps_ge_zero : 2⁻¹ * ε > 0, { simp [hε.lt], },
  have half_eps_lt_eps : 2⁻¹ * ε < ε,
  { -- This seems like it should be golfable?
    have := half_lt_self hε.lt,
    ring_nf at this,
    ring_nf,
    exact this, },
  rcases (this (2⁻¹ * ε) half_eps_ge_zero) with ⟨N, hN⟩,
  use N,
  intros m hm n hn z hz,
  specialize hN m hm n hn,
  have : ∀ (x_1 : E), x_1 ∈ closed_ball x r → ∥f' m x_1 - f' n x_1∥ ≤ 2⁻¹ * ε,
  { intros y hy,
    rw ←dist_eq_norm,
    exact (hN y hy).le, },
  have mvt := mean_value_theorem_for_differences hrR (hf m) (hf n) this hz hy,

  rw [dist_eq_norm, ←smul_sub, norm_smul, norm_inv, is_R_or_C.norm_coe_norm],
  -- This would work with `ring` but this is no longer a `ring`. Is there a
  -- `comm_group` equivalent of `ring`?
  have : f m z - f m y - (f n z - f n y) = f m z - f n z - (f m y - f n y),
  { rw [←sub_add, ←sub_add, sub_sub, sub_sub],
    conv { congr, congr, congr, skip, rw add_comm, }, },
  rw this,
  exact lt_of_le_of_lt mvt half_eps_lt_eps,
end

lemma uniform_convergence_of_uniform_convergence_derivatives
  (hrpos : 0 < r)
  (hrR : r < R)
  (hf : ∀ (n : ℕ), ∀ (y : E), y ∈ ball x R → has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
  tendsto_uniformly_on f g at_top (closed_ball x r) :=
begin
  -- Proof strategy: We have assumed that f → g pointwise, so it suffices to show that
  -- `f` is a *uniform* cauchy sequence on `closed_ball x r`. But for any `y`, we have
  -- `|f m y - f n y| ≤ |(f m - f n) y - (f m - f n) x| + |f m x - f n x|` by
  -- the triangle inequality and "adding zero". Importantly, note that `x` is fixed.
  --
  -- The first of these summands can be bounded using the fact that the difference
  -- quotients converge uniformly. The latter follows from the fact that `λ n, f n x` is
  -- a (not-necessarily uniform) cauchy sequence.
  refine uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto _ hfg,
  rw metric.uniform_cauchy_seq_on_iff,
  intros ε hε,

  -- Get the bound for |f m x - f n x|
  have := metric.cauchy_seq_iff.mp (hfg x (by simp [hrpos.le])).cauchy_seq,
  have two_inv_pos : 0 < (2 : ℝ)⁻¹, simp,
  have ε_over_two_pos : 0 < (2⁻¹ * ε),
  { exact mul_pos two_inv_pos hε.lt, },
  cases this (2⁻¹ * ε) ε_over_two_pos.gt with N1 hN1,

  -- The mean value theorem will let us |(f m - f n) y - (f m - f n) x| up to a factor
  -- of diam closed_ball x r = 2 * r. Choose N2 with this in mind
  have foo := metric.uniform_cauchy_seq_on_iff.mp hfg'.uniform_cauchy_seq_on,
  have : 0 < (2⁻¹ * r⁻¹ * ε),
  { exact mul_pos (mul_pos (by norm_num) (by simp [hrpos])) hε.lt, },
  specialize foo (2⁻¹ * r⁻¹ * ε) this.gt,
  cases foo with N2 hN2,

  -- Some annoying manipulation
  let N := max N1 N2,
  refine ⟨N, λ m hm n hn y hy, _⟩,
  rw dist_eq_norm,

  -- Apply the triangle inequality
  have : f m y - f n y = (f m y - f n y) - (f m x - f n x) + (f m x - f n x),
  { rw sub_add_cancel, },
  rw this,
  have : ∥f m y - f n y - (f m x - f n x) + (f m x - f n x)∥ ≤
    ∥f m y - f n y - (f m x - f n x)∥ + ∥f m x - f n x∥,
  { exact norm_add_le _ _, },
  refine lt_of_le_of_lt this _,

  -- The case y = x is trivial and causes some divide by zero errors throughout the
  -- proof, so we just take care of it now
  by_cases hyxx : y = x,
  { simp [hyxx],
    rw ←dist_eq_norm,
    have := hN1 m
      (le_trans (le_max_left N1 N2) hm.le) n (le_trans (le_max_left N1 N2) hn.le),
    transitivity,
    exact this,
    rw mul_lt_iff_lt_one_left hε.lt,
    norm_num, },

  -- Conveniences that the ring solver can't figure out on its own
  have hxyy : y - x ≠ 0, exact λ H, hyxx (sub_eq_zero.mp H),
  have hxyy' : ∥y - x∥ ≠ 0, simp [hxyy],

  -- Multiply and divide by the difference quotient denominator
  have : ∥f m y - f n y - (f m x - f n x)∥ = ∥y - x∥ * (∥y - x∥⁻¹ * ∥f m y - f n y - (f m x - f n x)∥),
  { exact (mul_inv_cancel_left₀ hxyy' _).symm, },
  rw this,

  specialize hN2 m (ge_trans hm (by simp)) n (ge_trans hn (by simp)),
  have : ∀ (x_1 : E), x_1 ∈ closed_ball x r → ∥ f' m x_1 - f' n x_1∥ ≤ 2⁻¹ * r⁻¹ * ε, {
    intros y hy,
    rw ←dist_eq_norm,
    exact (hN2 y hy).le,
  },
  have hxb : x ∈ closed_ball x r, simp [hrpos.le],
  have mvt := mean_value_theorem_for_differences hrR (hf m) (hf n) this hy hxb,
  specialize hN1 m (ge_trans hm (by simp)) n (ge_trans hn (by simp)),
  rw dist_eq_norm at hN1,

  have : ε = (2⁻¹ * ε) + (2⁻¹ * ε), ring,
  rw this,
  have : r⁻¹ * r = 1, { exact inv_mul_cancel hrpos.ne.symm, },

  have : ∥y - x∥ * (∥y - x∥⁻¹ * ∥f m y - f n y - (f m x - f n x)∥) ≤ 2⁻¹ * ε,
  { have : ∥y - x∥ ≤ r, { rw [mem_closed_ball, dist_eq_norm] at hy, exact hy, },
    calc ∥y - x∥ * (∥y - x∥⁻¹ * ∥f m y - f n y - (f m x - f n x)∥) ≤ r * (2⁻¹ * r⁻¹ * ε) :
      mul_le_mul this mvt (mul_nonneg (by simp) (by simp)) (hrpos.le)
    ... = 2⁻¹ * ε : begin
      ring_nf,
      rw [mul_assoc, inv_mul_cancel hrpos.ne.symm],
      ring,
    end },
  exact add_lt_add_of_le_of_lt this hN1,
end

/-- (d/dx) lim_{n → ∞} f_n x = lim_{n → ∞} f'_n x on a closed ball when the f'_n
converge _uniformly_ to their limit. -/
lemma has_fderiv_at_of_tendsto_uniformly_on
  (hrR : r < R)
  (hf : ∀ (n : ℕ), ∀ (y : E), y ∈ ball x R → has_fderiv_at (f n) (f' n y) y)
  (hfg : ∀ (y : E), y ∈ closed_ball x r → tendsto (λ n, f n y) at_top (nhds (g y)))
  (hfg' : tendsto_uniformly_on f' g' at_top (closed_ball x r)) :
  ∀ y : E, y ∈ ball x r → has_fderiv_at g (g' y) y :=
begin
  -- We do the famous "ε / 3 proof" which will involve several bouts of utilizing
  -- uniform continuity. First we setup our goal in terms of ε and δ
  intros y hy,
  rw [has_fderiv_at_iff_tendsto, tendsto_nhds_nhds],

  -- Now some important auxiliary facts such as:
  have hrpos : 0 < r,
  { calc 0 ≤ dist y x : dist_nonneg ... < r : mem_ball.mp hy, },

  have hyc : y ∈ closed_ball x r,
  { exact (mem_ball.mp hy).le, },

  -- uniform convergence of the derivatives implies uniform convergence of the primal
  have hfguc := uniform_convergence_of_uniform_convergence_derivatives hrpos hrR hf hfg hfg',

  -- convergence of the primal and uniform convergence of the derivatives implies
  -- uniform convergence of the difference quotients
  have hdiff := difference_quotients_converge_uniformly hrR hf hfg hfg' y hyc,

  -- The first (ε / 3) comes from the convergence of the derivatives
  intros ε hε,
  have : 0 < (3 : ℝ)⁻¹, simp, linarith,
  have ε_over_three_pos : 0 < (3⁻¹ * ε),
  { exact mul_pos this hε.lt, },

  rw tendsto_uniformly_on_iff at hfg',
  specialize hfg' (3⁻¹ * ε) ε_over_three_pos.gt,
  rw eventually_at_top at hfg',
  rcases hfg' with ⟨N1, hN1⟩,

  -- The second (ε / 3) comes from the uniform convergence of the difference quotients
  rw tendsto_uniformly_on_iff at hdiff,
  specialize hdiff (3⁻¹ * ε) ε_over_three_pos.gt,
  rw eventually_at_top at hdiff,
  rcases hdiff with ⟨N2, hN2⟩,

  -- These two N determine our final N
  let N := max N1 N2,

  -- The final (ε / 3) comes from the definition of a derivative
  specialize hf N y (calc dist y x < r : hy ... < R : hrR),
  rw has_fderiv_at_iff_tendsto at hf,
  rw tendsto_nhds_nhds at hf,
  specialize hf (3⁻¹ * ε) ε_over_three_pos.gt,
  rcases hf with ⟨δ', hδ', hf⟩,

  -- Choose our final δ
  let δ := min (r - dist y x) δ',
  have hδ : δ > 0,
  { refine lt_min _ hδ'.lt,
    rw sub_pos,
    exact hy, },

  -- Start the final manipulation
  use [δ, hδ],
  intros x' hx',
  have hxc : x' ∈ closed_ball x r,
  { have foo := calc dist x' y < δ : hx' ... ≤ r - dist y x : by simp [δ],
    calc dist x' x ≤ dist x' y + dist y x : dist_triangle _ _ _ ... ≤ r : by linarith, },
  have hxy : dist x' y < δ', calc dist x' y < δ : hx' ... ≤ δ' : by simp [δ],
  specialize hf hxy,

  -- There's a technical issue where we need to rule out the case y = x'
  by_cases hy' : y = x',
  { simp [hy', hε.lt], },
  have hx'y : x' - y ≠ 0, exact λ H, hy' (sub_eq_zero.mp H).symm,
  have hx'yy : 0 < ∥x' - y∥, simp only [hx'y, norm_pos_iff, ne.def, not_false_iff],

  -- Now that this case is ruled out, we begin setting up our final outcome:
  -- rewrite ε as 3 * (3⁻¹ * ε)
  have : ε = (3⁻¹ * ε) + (3⁻¹ * ε) + (3⁻¹ * ε),
  { ring, },
  rw this,

  -- Our three inequalities come from `hf`, `hN1`, and `hN2`. Get them and the goal in
  -- shape for the final triangle inequality application
  specialize hN1 N (by simp) y hyc,
  rw dist_comm at hN1,
  have hN1 := (f' N y - g' y).le_of_op_norm_le hN1.le (x' - y),
  rw ←mul_inv_le_iff' hx'yy at hN1,
  rw mul_comm at hN1,

  specialize hN2 N (by simp) x' hxc,
  rw [dist_eq_norm, ←smul_sub, norm_smul] at hN2,
  simp only [norm_inv, is_R_or_C.norm_coe_norm] at hN2,

  rw dist_eq_norm at hf,
  simp only [map_sub, sub_zero, norm_mul, norm_inv, norm_norm] at hf,

  rw dist_eq_norm,
  simp only [algebra.id.smul_eq_mul, sub_zero, norm_mul, norm_inv, norm_norm],

  -- Get into shape for triangle inequality
  have : g x' - g y - (g' y) (x' - y) =
    (g x' - g y - (f N x' - f N y)) +
    ((f N x' - f N y) - ((f' N y) x' - (f' N y) y)) +
    ((f' N y - g' y) (x' - y)), simp,
  rw this,

  have : ∥x' - y∥⁻¹ * ∥(g x' - g y - (f N x' - f N y)) +
    ((f N x' - f N y) - ((f' N y) x' - (f' N y) y)) +
    ((f' N y - g' y) (x' - y))∥ ≤
    ∥x' - y∥⁻¹ * ∥(g x' - g y - (f N x' - f N y))∥ +
    ∥x' - y∥⁻¹ * ∥((f N x' - f N y) - ((f' N y) x' - (f' N y) y))∥ +
    ∥x' - y∥⁻¹ * ∥((f' N y - g' y) (x' - y))∥,
  { rw [←mul_add (∥x' - y∥⁻¹) _ _, ←mul_add (∥x' - y∥⁻¹) _ _],
    have : ∥x' - y∥⁻¹ ≤ ∥x' - y∥⁻¹, exact le_refl _,
    refine mul_le_mul this norm_add_three_le (by simp) (by simp), },

  exact lt_of_le_of_lt this (lt_of_lt_of_lt_of_le hN2 hf hN1),
end

end limits_of_derivatives
