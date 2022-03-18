import topology.vector_bundle.basic
import analysis.normed_space.operator_norm
import analysis.normed_space.bounded_linear_maps

open bundle

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]

variables {B : Type*} [topological_space B]

variables {F₁ : Type*} [normed_group F₁] [normed_space 𝕜 F₁]
  {E₁ : B → Type*} [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜 (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [topological_space (total_space E₁)]
  [Π x, has_continuous_add (E₁ x)] [Π x, has_continuous_smul 𝕜 (E₁ x)]
  [topological_vector_bundle 𝕜 F₁ E₁]

variables {F₂ : Type*} [normed_group F₂][normed_space 𝕜 F₂]
  {E₂ : B → Type*} [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜 (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [topological_space (total_space E₂)]
  [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜 (E₂ x)]
  [topological_vector_bundle 𝕜 F₂ E₂]

-- might actually be false for the norm topology?
lemma continuous_transition (e : homeomorph (B × F₁) (B × F₁))
  (ε : B → F₁ ≃L[𝕜] F₁) (h : ∀ x f, (x, ε x f) = e (x, f)) :
  continuous (λ x, (ε x : F₁ →L[𝕜] F₁)) :=
sorry

example (E F G : Type*) [normed_group E] [normed_group F] [normed_group G] [normed_space 𝕜 E]
  [normed_space 𝕜 F] [normed_space 𝕜 G] :
  continuous (λ p : (E →L[𝕜] F) × (F →L[𝕜] G), p.2.comp p.1) :=
is_bounded_bilinear_map_comp.continuous

example (E F G : Type*) [normed_group E] [normed_group F] [normed_group G] [normed_space 𝕜 E]
  [normed_space 𝕜 F] [normed_space 𝕜 G] :
  continuous (λ p : (F →L[𝕜] F) × (F →L[𝕜] G), p.2.comp p.1) :=
by library_search

example (e₁ : homeomorph (B × F₁) (B × F₁)) (e₂ : homeomorph (B × F₂) (B × F₂))
  (ε₁ : B → F₁ ≃L[𝕜] F₁) (ε₂ : B → F₂ ≃L[𝕜] F₂) (h₁ : ∀ x f, (x, ε₁ x f) = e₁ (x, f))
  (h₂ : ∀ x f, (x, ε₂ x f) = e₂ (x, f)) :
  continuous (λ p : B × (F₁ →L[𝕜] F₂),
    continuous_linear_map.compL 𝕜 F₁ F₁ F₂
      (continuous_linear_map.compL 𝕜 F₁ F₂ F₂
        (ε₂ p.1 : F₂ →L[𝕜] F₂)
        p.2)
      (ε₁ p.1 : F₁ →L[𝕜] F₁)) :=
begin
  let Φ : (F₁ →L[𝕜] F₁) × (F₁ →L[𝕜] F₂) × (F₂ →L[𝕜] F₂) → F₁ →L[𝕜] F₂ := λ p, p.2.2 ∘L p.2.1 ∘L p.1,
  have H : continuous Φ := sorry,
  have H' : continuous
    (λ p : B × (F₁ →L[𝕜] F₂), ((ε₁ p.1 : F₁ →L[𝕜] F₁), p.2, (ε₂ p.1 : F₂ →L[𝕜] F₂))),
  { refine ((continuous_transition e₁ ε₁ h₁).comp continuous_fst).prod_mk _,
    refine continuous_snd.prod_mk _,
    exact (continuous_transition e₂ ε₂ h₂).comp continuous_fst },
  exact H.comp H',
end
