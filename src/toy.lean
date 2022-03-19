import analysis.normed_space.bounded_linear_maps

variables {B : Type*} [topological_space B]
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {F₁ : Type*} [normed_group F₁] [normed_space 𝕜 F₁]
  {F₂ : Type*} [normed_group F₂] [normed_space 𝕜 F₂]
  {F₃ : Type*} [normed_group F₃] [normed_space 𝕜 F₃]

/-! ## Operator norm -/

section

lemma pre (ε : B → (F₁ →L[𝕜] F₂)) (h : continuous (λ p : B × F₁, ε p.1 p.2)) :
  continuous (λ p : B × (F₂ →L[𝕜] F₃), p.2 ∘L ε p.1) :=
begin
  have hε : continuous ε := sorry, -- would work in topology of pointwise convergence, see `***` below
  exact is_bounded_bilinear_map_comp.continuous.comp (hε.prod_map continuous_id),
end

lemma post (ε : B → (F₂ →L[𝕜] F₃)) (h : continuous (λ p : B × F₂, ε p.1 p.2)) :
  continuous (λ p : B × (F₁ →L[𝕜] F₂), ε p.1 ∘L p.2) :=
begin
  have hε : continuous ε := sorry, -- would work in topology of pointwise convergence, see `***` below
  exact is_bounded_bilinear_map_comp.continuous.comp (continuous_snd.prod_mk (hε.comp continuous_fst)),
end

example (ε₁ : B → (F₁ ≃L[𝕜] F₁)) (h₁ : continuous (λ p : B × F₁, ε₁ p.1 p.2))
  (ε₂ : B → (F₂ ≃L[𝕜] F₂)) (h₂ : continuous (λ p : B × F₂, ε₂ p.1 p.2)) :
  continuous (λ p : B × (F₁ →L[𝕜] F₂), (ε₂ p.1 : F₂ →L[𝕜] F₂) ∘L p.2 ∘L (ε₁ p.1 : F₁ →L[𝕜] F₁)) :=
(post (λ x, (ε₂ x : F₂ →L[𝕜] F₂)) h₂).comp
  (continuous_fst.prod_mk (pre (λ x, (ε₁ x : F₁ →L[𝕜] F₁)) h₁))

end

/-! ## Topology of pointwise convergence -/

section

 -- get rid of operator norm topology
local attribute [-instance] continuous_linear_map.to_normed_group

/-- The topology of pointwise convergence on `F₁ →L[𝕜] F₂`. -/
instance : topological_space (F₁ →L[𝕜] F₂) :=
@topological_space.induced (F₁ →L[𝕜] F₂) (F₁ → F₂) (λ f, (f : F₁ → F₂)) (by apply_instance)

/-- see `***` above -/
example (ε : B → (F₂ →L[𝕜] F₃)) (h : continuous (λ p : B × F₂, ε p.1 p.2)) : continuous ε :=
begin
  apply continuous_induced_rng,
  rw continuous_iff_continuous_at,
  intros x,
  rw continuous_at_pi,
  intros v,
  exact (h.comp (continuous_id.prod_mk continuous_const)).continuous_at
end

lemma pre' (ε : B → (F₁ →L[𝕜] F₂)) (h : continuous (λ p : B × F₁, ε p.1 p.2)) :
  continuous (λ p : B × (F₂ →L[𝕜] F₃), p.2 ∘L ε p.1) :=
begin
  apply continuous_induced_rng,
  rw continuous_iff_continuous_at,
  intros x,
  rw continuous_at_pi,
  intros v,
  let Φ : (F₂ →L[𝕜] F₃) × F₂ → F₃ := λ p, p.1 p.2,
  have hΦ : continuous Φ := sorry, -- would work in operator-norm topology (`is_bounded_bilinear_map_apply`)
  exact (hΦ.comp (continuous_snd.prod_mk ((h.comp (continuous_id.prod_mk continuous_const)).comp
    continuous_fst))).continuous_at,
end

lemma post' (ε : B → (F₂ →L[𝕜] F₃)) (h : continuous (λ p : B × F₂, ε p.1 p.2)) :
  continuous (λ p : B × (F₁ →L[𝕜] F₂), ε p.1 ∘L p.2) :=
begin
  apply continuous_induced_rng,
  rw continuous_iff_continuous_at,
  intros x,
  rw continuous_at_pi,
  intros v,
  exact (h.comp (continuous_id.prod_map
    ((continuous_apply v).comp continuous_induced_dom))).continuous_at,
end

example (ε₁ : B → (F₁ ≃L[𝕜] F₁)) (h₁ : continuous (λ p : B × F₁, ε₁ p.1 p.2))
  (ε₂ : B → (F₂ ≃L[𝕜] F₂)) (h₂ : continuous (λ p : B × F₂, ε₂ p.1 p.2)) :
  continuous (λ p : B × (F₁ →L[𝕜] F₂), (ε₂ p.1 : F₂ →L[𝕜] F₂) ∘L p.2 ∘L (ε₁ p.1 : F₁ →L[𝕜] F₁)) :=
(post' (λ x, (ε₂ x : F₂ →L[𝕜] F₂)) h₂).comp
  (continuous_fst.prod_mk (pre' (λ x, (ε₁ x : F₁ →L[𝕜] F₁)) h₁))

end
