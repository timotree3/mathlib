/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.bounded_linear_maps
import geometry.manifold.charted_space

/-! # The groupoid of transition functions for `F`-vector bundles over `B` -/

open set filter

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (B : Type*) [topological_space B]
  (F : Type*) [normed_group F] [normed_space 𝕜 F] [complete_space F]

/-- The groupoid of valid transition functions for a topological vector bundle over `B` modelled on
a normed space `F`: a transition function must be a local homeomorphism of `B × F` with source and
target both `s ×ˢ univ`, which on this set is of the form `λ (b, v), (b, ε b v)` for some continuous
map `ε` from `s` to `F ≃L[𝕜] F`.  Here continuity is with respect to the operator norm on
`F ≃L[𝕜] F`. -/
def continuous_transitions : structure_groupoid (B × F) :=
{ members := {e | ∃ s : set B, e.source = s ×ˢ (univ : set F) ∧ e.target = s ×ˢ (univ : set F)
    ∧ ∃ ε : B → (F ≃L[𝕜] F), continuous_on (λ b, (ε b : F →L[𝕜] F)) s
      ∧ ∀ b ∈ s, ∀ v : F, e (b, v) = (b, ε b v)},
  trans' := λ e e' ⟨s, hes₁, hes₂, ε, hε, heε⟩ ⟨s', hes₁', hes₂', ε', hε', heε'⟩, begin
    refine ⟨s ∩ s', _, _, (λ b, (ε b).trans (ε' b)), _,  _⟩,
    { sorry },
    { sorry },
    { exact is_bounded_bilinear_map_comp.continuous.comp_continuous_on
        ((hε.mono (inter_subset_left s s')).prod (hε'.mono (inter_subset_right s s'))) },
    { rintros b ⟨hb, hb'⟩ v,
      simp [heε b hb, heε' b hb'] },
  end,
  symm' := λ e ⟨s, hes₁, hes₂, ε, hε, heε⟩, begin
    refine ⟨s, _, _, (λ b, (ε b).symm), _, _⟩,
    { simp [hes₂] },
    { simp [hes₁] },
    { intros b hb,
      have hb' : s ∈ nhds b := sorry,
      have H₁ : continuous_at ring.inverse ((λ x, (ε x : F →L[𝕜] F)) b) :=
        normed_ring.inverse_continuous_at ((continuous_linear_equiv.units_equiv 𝕜 F).symm (ε b)),
      have H₂ : continuous_at (λ x, (ε x : F →L[𝕜] F)) b := hε.continuous_at hb',
      refine ((H₁.comp H₂).congr _).continuous_within_at,
      apply eventually_eq_of_mem hb',
      intros a ha,
      simp },
    { rintros b hb v,
      have heb : (b, v) ∈ e.target,
      { simp [hes₂, hb] },
      apply e.inj_on (e.map_target heb),
      { simp [hes₁, hb] },
      simp [heε b hb, e.right_inv heb] }
  end,
  id_mem' := begin
    refine ⟨univ, _, _, λ b, continuous_linear_equiv.refl 𝕜 F, _, _⟩,
    { simp },
    { simp },
    { exact continuous_on_const },
    { rintros b hb v,
      simp }
  end,
  locality' := λ e h, begin
    classical,
    dsimp at *,
    choose a b c d f g ε₀ hε₀ heε₀ using h,
    let s : set B := prod.fst '' e.source,
    have hes₁ : e.source = s ×ˢ univ := sorry,
    have H : ∀ {b : B}, b ∈ s → (b, (0:F)) ∈ e.source := sorry,
    let ε : B → (F ≃L[𝕜] F) :=
      λ b, if hb : b ∈ s then ε₀ _ (H hb) b else continuous_linear_equiv.refl 𝕜 F,
    refine ⟨s, hes₁, _, ε, _, _⟩,
    { sorry },
    { sorry },
    { sorry }
  end,
  eq_on_source' := λ e e' ⟨s, hes₁, hes₂, ε, hε, heε⟩ hee', begin
    refine ⟨s, _, _, ε, _, _⟩,
    { simp [hee'.source_eq, hes₁] },
    { simp [hee'.target_eq, hes₂] },
    { sorry },
    { sorry }
  end }
