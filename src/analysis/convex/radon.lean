import analysis.convex.combination
import data.finset.basic

open_locale big_operators

universes u
variables {𝕜 : Type*} {E : Type u} [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]

theorem filter_union_filter_not (M : finset E) (p : E → Prop) [decidable_pred p] :
  (M.filter p : set E) ∪ M.filter (λ x, ¬ p x) = M :=
begin
  ext, split,
  { rintro (hx | hx);
    rw [finset.mem_coe, finset.mem_filter] at hx;
    exact hx.1 },
  { intro hx,
    by_cases p x,
    left, swap, right,
    all_goals { rw [finset.mem_coe, finset.mem_filter], exact ⟨hx, h⟩ } }
end

theorem filter_inter_filter_not (M : finset E) (p : E → Prop) [decidable_pred p] :
  (M.filter p : set E) ∩ M.filter (λ x, ¬ p x) = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  rintros x ⟨hx₁, hx₂⟩,
  rw [finset.mem_coe, finset.mem_filter] at *,
  exact hx₂.2 hx₁.2
end

lemma radon_lemma {ι} {p : ι → E} (hp : function.injective p) (h : ¬ affine_independent 𝕜 p) :
  ∃ (M₁ M₂ ⊆ set.range p), disjoint M₁ M₂ ∧ ¬ disjoint (convex_hull 𝕜 M₁) (convex_hull 𝕜 M₂) :=
begin
  rw affine_independent_def at h,
  push_neg at h,
  rcases h with ⟨M, f, hf, hf', a, ha, ha'⟩,
  haveI : decidable_pred (λ i : ι, f i > 0) := by { classical, apply_instance },
  let I₁ := M.filter (λ i : ι, f i > 0),
  let I₂ := M.filter (λ i : ι, ¬ f i > 0),
  refine ⟨p '' I₁, set.image_subset_range p I₁, p '' I₂, set.image_subset_range p I₂, _, _⟩,
  { rw set.disjoint_iff_forall_ne,
    rintros _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ h,
    rw hp h at hi,
    exact (finset.mem_filter.1 hj).2 (finset.mem_filter.1 hi).2 },
  { rw set.not_disjoint_iff,
    let k := ∑ x in I₁, f x,
    use ∑ x in I₁, (f x / k) • p x,
    split, {

    }
  }
end
