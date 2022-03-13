import analysis.convex.combination
import data.finset.basic

open_locale big_operators

universes u
variables {𝕜 : Type*} {E : Type u} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]

lemma exists_nontrivial_relation_sum_zero_of_not_affine_ind'
  {ι} {p : ι → E} (h : ¬ affine_independent 𝕜 p) : ∃ t : finset ι,
  (∃ f : ι → 𝕜, ∑ e in t, f e • p e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0) :=
sorry

lemma radon_lemma {ι} {p : ι → E} (hp : function.injective p) (h : ¬ affine_independent 𝕜 p) :
  ∃ (M₁ M₂ ⊆ set.range p), disjoint M₁ M₂ ∧ ¬ disjoint (convex_hull 𝕜 M₁) (convex_hull 𝕜 M₂) :=
begin
  -- We take an affine combination of the points in `ι` adding up to 0.
  classical,
  rcases exists_nontrivial_relation_sum_zero_of_not_affine_ind' h with ⟨M, f, hf, hf', a, ha, ha'⟩,

  -- We choose `M₁` and `M₂` as the sets of points in this combination with positive and negative
  -- coefficients respectively.
  let I₁ := M.filter (λ i : ι, 0 < f i),
  let I₂ := M.filter (λ i : ι, f i ≤ 0),
  refine ⟨_, set.image_subset_range p I₁, _, set.image_subset_range p I₂, _, _⟩,
  { rw set.disjoint_iff_forall_ne,
    rintros _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ h,
    rw hp h at hi,
    exact (finset.mem_filter.1 hj).2.not_lt (finset.mem_filter.1 hi).2 },

  -- `∑ x in I₁, (f x / k) • p x = ∑ x in I₂, (- f x / k) • p x` is in both convex hulls.
  { rw set.not_disjoint_iff,
    let k := ∑ x in I₁, f x,
    have HI₁ : ∀ j, j ∈ I₁ → 0 < f j := λ j hj, (finset.mem_filter.1 hj).2,
    have HI₁' : ∀ j, j ∈ I₁ → 0 ≤ f j := λ j hj, (HI₁ j hj).le,
    have HI₂ : ∀ j, j ∈ I₂ → f j ≤ 0 := λ j hj, (finset.mem_filter.1 hj).2,
    have hk : 0 ≤ k := finset.sum_nonneg HI₁',

    -- Surely this can be golfed somewhat??
    have HI₁₂ : I₁ = M \ I₂,
    { ext i,
      refine ⟨λ hi, _, λ hi, _⟩,
      { rw finset.mem_sdiff,
        exact ⟨(finset.mem_filter.1 hi).1, λ hi', (HI₁ i hi).not_le (HI₂ i hi')⟩ },
      { rw finset.mem_sdiff at hi,
        refine finset.mem_filter.2 ⟨hi.1, _⟩,
        by_contra' hi',
        exact hi.2 (finset.mem_filter.2 ⟨hi.1, hi'⟩) } },

    have HS : ∑ i in I₁, f i / k = 1,
    { rw ←finset.sum_div,
      refine div_self (ne_of_gt (finset.sum_pos HI₁ _)),
      { by_contra H,
        rw finset.not_nonempty_iff_eq_empty at H,

        -- Since every term in `∑ i in M, f i` sum is nonnegative, and `f a ≠ 0`, then the sum is
        -- negative, contradicting `hf`.

        -- This is pretty much `finset.single_lt_sum` but with the signs reversed.
        sorry } },
    refine ⟨∑ x in I₁, (f x / k) • p x, _, _⟩,
    { rw finset.coe_filter,
      exact convex.sum_mem (convex_convex_hull _ _) (λ i hi, div_nonneg (HI₁' i hi) hk) HS
        (λ i hi, subset_convex_hull _ _ ⟨i, finset.mem_filter.1 hi, rfl⟩) },
    { have HS₁₂ : ∑ x in I₁, (f x / k) • p x = ∑ x in I₂, (- f x / k) • p x,
      { simp_rw [neg_div, neg_smul],
        rw [finset.sum_neg_distrib, eq_neg_iff_add_eq_zero, HI₁₂,
          finset.sum_sdiff (finset.filter_subset _ _)],
        simp_rw [div_eq_mul_inv, mul_comm _ k⁻¹, mul_smul],
        rw [←finset.smul_sum, hf],
        apply smul_zero },
      rw HS₁₂,
      refine convex.sum_mem (convex_convex_hull _ _) (λ i hi, div_nonneg (le_neg_of_le_neg _) hk) _
        (λ i hi, subset_convex_hull _ _ ⟨i, hi, rfl⟩),
      { rw neg_zero,
        exact HI₂ i hi },
      { rw ←HS,
        simp_rw [neg_div],
        symmetry,
        rw [finset.sum_neg_distrib, eq_neg_iff_add_eq_zero, HI₁₂,
          finset.sum_sdiff (finset.filter_subset _ _), ←finset.sum_div],
        exact div_eq_zero_iff.2 (or.inl hf') } } }
end
