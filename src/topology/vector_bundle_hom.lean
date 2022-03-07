import topology.vector_bundle
import analysis.normed_space.operator_norm

/-! # Direct sum of two vector bundles over the same base -/

noncomputable theory

open bundle

namespace topological_vector_bundle

section defs
variables {R₁ : Type*} [semiring R₁] [topological_space R₁]
variables {R₂ : Type*} [comm_semiring R₂] [topological_space R₂]
variables (σ : R₁ →+* R₂)
variables {B : Type*}
  (F₁ : Type*) (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module R₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [Π x, has_continuous_add (E₁ x)]
  [Π x, has_continuous_smul R₁ (E₁ x)]
  (F₂ : Type*) (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module R₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [Π x, has_continuous_add (E₂ x)]
  [Π x, has_continuous_smul R₂ (E₂ x)]

include F₁ F₂

/-- The bundle of continuous `σ`-semilinear maps between the topological vector bundles `E₁` and
`E₂`.  Type synonym for `λ x, E₁ x →SL[σ] E₂ x`. -/
@[derive [add_comm_monoid, module R₂, inhabited], nolint unused_arguments]
def vector_bundle_continuous_linear_map (x : B) :=
E₁ x →SL[σ] E₂ x

end defs

namespace pretrivialization

variables {𝕜₁ : Type*} [nondiscrete_normed_field 𝕜₁] {𝕜₂ : Type*} [nondiscrete_normed_field 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂) [ring_hom_isometric σ]

variables {B : Type*} [topological_space B]

variables (F₁ : Type*) [normed_group F₁] [normed_space 𝕜₁ F₁]
  (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)] [topological_space (total_space E₁)]
  [Π x, has_continuous_add (E₁ x)] [Π x, has_continuous_smul 𝕜₁ (E₁ x)]
  [topological_vector_bundle 𝕜₁ F₁ E₁]

variables (F₂ : Type*) [normed_group F₂][normed_space 𝕜₂ F₂]
  (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [topological_space (total_space E₂)]
  [Π x, has_continuous_add (E₂ x)] [Π x, has_continuous_smul 𝕜₂ (E₂ x)]
  [topological_vector_bundle 𝕜₂ F₂ E₂]

variables (e₁ : trivialization 𝕜₁ F₁ E₁) (e₂ : trivialization 𝕜₂ F₂ E₂)

include e₁ e₂
variables {σ F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.pretrivialization.continuous_linear_map`,
the induced pretrivialization for the continuous semilinear maps from `E₁` to `E₂`. -/
def continuous_linear_map.to_fun'
  (p : total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :
  B × (F₁ →SL[σ] F₂) :=
begin
  obtain ⟨x, f⟩ := p,
  refine ⟨x, _⟩,
  by_cases h : x ∈ e₁.base_set ∧ x ∈ e₂.base_set,
  { let φ₁ := e₁.continuous_linear_equiv_at x h.1,
    let φ₂ := e₂.continuous_linear_equiv_at x h.2,
    exact ((φ₂ : E₂ x →L[𝕜₂] F₂).comp f).comp (φ₁.symm : F₁ →L[𝕜₁] E₁ x) },
  { exact 0 }
end

lemma continuous_linear_map.to_fun'_apply {x : B} (h₁ : x ∈ e₁.base_set) (h₂ : x ∈ e₂.base_set)
  (f : E₁ x →SL[σ] E₂ x) :
  continuous_linear_map.to_fun' e₁ e₂ ⟨x, f⟩ =
  ⟨x, ((e₂.continuous_linear_equiv_at x h₂ : E₂ x →L[𝕜₂] F₂).comp f).comp
    ((e₁.continuous_linear_equiv_at x h₁).symm : F₁ →L[𝕜₁] E₁ x)⟩ :=
begin
  rw continuous_linear_map.to_fun',
  dsimp,
end

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.pretrivialization.continuous_linear_map`,
the induced pretrivialization for the continuous semilinear maps from `E₁` and `E₂`. -/
def continuous_linear_map.inv_fun' (p : B × (F₁ →SL[σ] F₂)) :
  total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
begin
  obtain ⟨x, f⟩ := p,
  refine ⟨x, _⟩,
  by_cases h : x ∈ e₁.base_set ∧ x ∈ e₂.base_set,
  { let φ₁ := e₁.continuous_linear_equiv_at x h.1,
    let φ₂ := e₂.continuous_linear_equiv_at x h.2,
    exact ((φ₂.symm : F₂ →L[𝕜₂] E₂ x).comp f).comp (φ₁ : E₁ x →L[𝕜₁] F₁) },
  { exact 0 }
end

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
pretrivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`.  That is, the map which
will later become a trivialization, after this direct sum is equipped with the right topological
vector bundle structure. -/
def continuous_linear_map :
  @pretrivialization 𝕜₂ B (F₁ →SL[σ] F₂) (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) _
  (vector_bundle_continuous_linear_map.add_comm_monoid σ F₁ E₁ F₂ E₂)
  (vector_bundle_continuous_linear_map.module σ F₁ E₁ F₂ E₂) _ _ _ _ :=
{ to_fun := continuous_linear_map.to_fun' e₁ e₂,
  inv_fun := continuous_linear_map.inv_fun' e₁ e₂,
  source := (proj (λ x, E₁ x →SL[σ] E₂ x)) ⁻¹' (e₁.base_set.inter e₂.base_set),
  target := (e₁.base_set.inter e₂.base_set) ×ˢ (set.univ : set (F₁ →SL[σ] F₂)),
  map_source' := λ ⟨x, f⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, f⟩ h, h.1,
  left_inv' := λ ⟨x, f⟩ h,
  begin
    simp only [continuous_linear_map.to_fun', continuous_linear_map.inv_fun', sigma.mk.inj_iff, true_and, eq_self_iff_true,
      prod.mk.inj_iff, heq_iff_eq],
    -- split,
    rw [dif_pos, dif_pos],-- ← e₁.continuous_linear_equiv_at_apply x h.1,
        -- continuous_linear_equiv.symm_apply_apply] },
    { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
        continuous_linear_equiv.symm_apply_apply] },
  end,
  right_inv' := λ ⟨x, f⟩ ⟨h, _⟩,
  begin
    dsimp [prod.to_fun', prod.inv_fun'],
    simp only [prod.mk.inj_iff, eq_self_iff_true, true_and],
    split,
    { rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1,
        continuous_linear_equiv.apply_symm_apply] },
    { rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2,
        continuous_linear_equiv.apply_symm_apply] },
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  base_set := e₁.base_set.inter e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, f⟩ h, rfl,
  linear := λ x h,
  { map_add := λ f f', sorry,
    map_smul := λ c f, sorry, } }

-- @[simp] lemma base_set_prod (e₁ : trivialization 𝕜 F₁ E₁) (e₂ : trivialization 𝕜 F₂ E₂) :
--   (prod e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
-- rfl

-- lemma open_base_set_prod (e₁ : trivialization 𝕜 F₁ E₁) (e₂ : trivialization 𝕜 F₂ E₂) :
--   is_open (prod e₁ e₂).base_set :=
-- begin
--   rw base_set_prod,
--   exact e₁.to_pretrivialization.open_base_set.inter e₂.open_base_set,
-- end

-- @[simp] lemma prod_apply {e₁ : trivialization 𝕜 F₁ E₁}
--   {e₂ : trivialization 𝕜 F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
--   (v₁ : E₁ x) (v₂ : E₂ x) :
--   prod e₁ e₂ ⟨x, (v₁, v₂)⟩
--   = ⟨x, e₁.continuous_linear_equiv_at x hx₁ v₁, e₂.continuous_linear_equiv_at x hx₂ v₂⟩ :=
-- rfl

-- lemma prod_symm_apply {e₁ : trivialization 𝕜 F₁ E₁}
--   {e₂ : trivialization 𝕜 F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
--   (w₁ : F₁) (w₂ : F₂) :
--   (prod e₁ e₂).to_local_equiv.symm (x, (w₁, w₂))
--   = ⟨x, ((e₁.continuous_linear_equiv_at x hx₁).symm w₁,
--       (e₂.continuous_linear_equiv_at x hx₂).symm w₂)⟩ :=
-- begin
--   dsimp [prod, prod.inv_fun'],
--   rw [dif_pos, dif_pos]
-- end

-- lemma continuous_triv_change_prod
--   (e₁ f₁ : trivialization 𝕜 F₁ E₁) (e₂ f₂ : trivialization 𝕜 F₂ E₂) :
--   continuous_on ((prod e₁ e₂) ∘ (prod f₁ f₂).to_local_equiv.symm)
--     ((prod f₁ f₂).target ∩ ((prod f₁ f₂).to_local_equiv.symm) ⁻¹' (prod e₁ e₂).source) :=
-- begin
--   refine continuous_on.prod' _ _,
--   { apply continuous_fst.continuous_on.congr,
--     rintros p ⟨hp₁, hp₂⟩,
--     convert (prod e₁ e₂).to_fiber_bundle_pretrivialization.coe_fst hp₂,
--     rw (prod f₁ f₂).to_fiber_bundle_pretrivialization.proj_symm_apply hp₁ },
--   rw [topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--     pretrivialization.base_set_prod, pretrivialization.base_set_prod],
--   let ψ₁ := f₁.to_local_homeomorph.symm.trans e₁.to_local_homeomorph,
--   let ψ₂ := f₂.to_local_homeomorph.symm.trans e₂.to_local_homeomorph,
--   have hψ₁ : ψ₁.source = (e₁.base_set ∩ f₁.base_set) ×ˢ (univ : set F₁) :=
--     e₁.to_pretrivialization.to_fiber_bundle_pretrivialization.trans_source f₁,
--   have hψ₂ : ψ₂.source = (e₂.base_set ∩ f₂.base_set) ×ˢ (univ : set F₂) :=
--     e₂.to_pretrivialization.to_fiber_bundle_pretrivialization.trans_source f₂,
--   refine continuous_on.prod' _ _,
--   { refine ((continuous_snd.comp_continuous_on ψ₁.continuous_on).comp
--       (continuous_id.prod_map continuous_fst).continuous_on _).congr _,
--     { rw hψ₁,
--       mfld_set_tac },
--     { rintros ⟨x, ⟨w₁, w₂⟩⟩ ⟨hx, -⟩,
--       have hxe₁ : x ∈ e₁.base_set := hx.1.1,
--       have hxe₂ : x ∈ e₂.base_set := hx.1.2,
--       dsimp,
--       rw [prod_symm_apply hx.2.1 hx.2.2, prod_apply hxe₁ hxe₂],
--       dsimp,
--       rw [f₁.symm_apply_eq_prod_continuous_linear_equiv_at_symm] } },
--   { refine ((continuous_snd.comp_continuous_on ψ₂.continuous_on).comp
--       (continuous_id.prod_map continuous_snd).continuous_on _).congr _,
--     { rw hψ₂,
--       mfld_set_tac },
--     { rintros ⟨x, ⟨w₁, w₂⟩⟩ ⟨hx, -⟩,
--       have hxe₁ : x ∈ e₁.base_set := hx.1.1,
--       have hxe₂ : x ∈ e₂.base_set := hx.1.2,
--       dsimp,
--       rw [prod_symm_apply hx.2.1 hx.2.2, prod_apply hxe₁ hxe₂],
--       dsimp,
--       rw [f₂.symm_apply_eq_prod_continuous_linear_equiv_at_symm] } },
-- end

end pretrivialization

-- open pretrivialization

-- variables [topological_vector_bundle 𝕜 F₁ E₁] [topological_vector_bundle 𝕜 F₂ E₂]

-- /-- The direct sum of topological vector bundles is a `topological_vector_prebundle` (this is an
-- auxiliary construction for the `topological_vector_prebundle` instance, in which the
-- pretrivializations are collated but no topology on the total space is yet provided). -/
-- def _root_.vector_bundle_prod.topological_vector_prebundle :
--   topological_vector_prebundle 𝕜 (F₁ × F₂) (vector_bundle_prod 𝕜 F₁ E₁ F₂ E₂) :=
-- { pretrivialization_at := λ x,
--     pretrivialization.prod (trivialization_at 𝕜 F₁ E₁ x) (trivialization_at 𝕜 F₂ E₂ x),
--   mem_base_pretrivialization_at := λ x,
--     ⟨mem_base_set_trivialization_at 𝕜 F₁ E₁ x, mem_base_set_trivialization_at 𝕜 F₂ E₂ x⟩,
--   continuous_triv_change := λ p q, pretrivialization.continuous_triv_change_prod
--     (trivialization_at 𝕜 F₁ E₁ p)
--     (trivialization_at 𝕜 F₁ E₁ q)
--     (trivialization_at 𝕜 F₂ E₂ p)
--     (trivialization_at 𝕜 F₂ E₂ q),
--   total_space_mk_inducing := λ b,
--   begin
--     let e₁ := trivialization_at 𝕜 F₁ E₁ b,
--     let e₂ := trivialization_at 𝕜 F₂ E₂ b,
--     have hb₁ : b ∈ e₁.base_set := mem_base_set_trivialization_at 𝕜 F₁ E₁ b,
--     have hb₂ : b ∈ e₂.base_set := mem_base_set_trivialization_at 𝕜 F₂ E₂ b,
--     have key : inducing (λ w : E₁ b × E₂ b,
--       (b, e₁.continuous_linear_equiv_at b hb₁ w.1, e₂.continuous_linear_equiv_at b hb₂ w.2)),
--     { refine (inducing_prod_mk b).comp _,
--       exact ((e₁.continuous_linear_equiv_at b hb₁).to_homeomorph.inducing.prod_mk
--         (e₂.continuous_linear_equiv_at b hb₂).to_homeomorph.inducing) },
--     { convert key,
--       ext1 w,
--       simpa using prod_apply hb₁ hb₂ w.1 w.2 },
--   end }

-- /-- The natural topology on the total space of the product of two vector bundles. -/
-- instance : topological_space (total_space (vector_bundle_prod 𝕜 F₁ E₁ F₂ E₂)) :=
-- (vector_bundle_prod.topological_vector_prebundle 𝕜 F₁ E₁ F₂ E₂).total_space_topology

-- /-- The product of two vector bundles is a vector bundle. -/
-- instance : topological_vector_bundle 𝕜 (F₁ × F₂) (vector_bundle_prod 𝕜 F₁ E₁ F₂ E₂) :=
-- (vector_bundle_prod.topological_vector_prebundle 𝕜 F₁ E₁ F₂ E₂).to_topological_vector_bundle

-- variables {𝕜 F₁ E₁ F₂ E₂}

-- /-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
-- trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-- -/
-- def trivialization.prod (e₁ : trivialization 𝕜 F₁ E₁) (e₂ : trivialization 𝕜 F₂ E₂) :
--   trivialization 𝕜 (F₁ × F₂) (vector_bundle_prod 𝕜 F₁ E₁ F₂ E₂) :=
-- { open_source := (open_base_set_prod e₁ e₂).preimage
--     (topological_vector_bundle.continuous_proj 𝕜 B (F₁ × F₂)),
--   continuous_to_fun :=
--   begin
--     apply topological_fiber_prebundle.continuous_on_of_comp_right,
--     { exact e₁.open_base_set.inter e₂.open_base_set },
--     intros b,
--     convert continuous_triv_change_prod e₁ (trivialization_at 𝕜 F₁ E₁ b) e₂
--       (trivialization_at 𝕜 F₂ E₂ b),
--     rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--     refl,
--   end,
--   continuous_inv_fun := λ x hx, continuous_at.continuous_within_at
--   begin
--     let f₁ := trivialization_at 𝕜 F₁ E₁ x.1,
--     let f₂ := trivialization_at 𝕜 F₂ E₂ x.1,
--     have H :
--       (prod e₁ e₂).target ∩ (prod e₁ e₂).to_local_equiv.symm ⁻¹' (prod f₁ f₂).source ∈ nhds x,
--     { rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--       refine is_open.mem_nhds _ ⟨⟨_, hx.1⟩, mem_univ _⟩,
--       { exact ((open_base_set_prod f₁ f₂).inter (open_base_set_prod e₁ e₂)).prod is_open_univ },
--       { exact ⟨mem_base_set_trivialization_at 𝕜 F₁ E₁ x.1,
--           mem_base_set_trivialization_at 𝕜 F₂ E₂ x.1⟩ } },
--     let a := (vector_bundle_prod.topological_vector_prebundle
--       𝕜 F₁ E₁ F₂ E₂).to_topological_fiber_prebundle,
--     rw (a.trivialization_at x.1).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left,
--     { exact (continuous_triv_change_prod f₁ e₁ f₂ e₂).continuous_at H },
--     { exact filter.mem_of_superset H (inter_subset_right _ _) },
--   end,
--   .. pretrivialization.prod e₁ e₂ }

-- @[simp] lemma trivialization.base_set_prod (e₁ : trivialization 𝕜 F₁ E₁)
--   (e₂ : trivialization 𝕜 F₂ E₂) :
--   (e₁.prod e₂).base_set = e₁.base_set ∩ e₂.base_set :=
-- rfl

-- @[simp] lemma trivialization.continuous_linear_equiv_at_prod {e₁ : trivialization 𝕜 F₁ E₁}
--   {e₂ : trivialization 𝕜 F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) :
--   (e₁.prod e₂).continuous_linear_equiv_at x ⟨hx₁, hx₂⟩
--   = (e₁.continuous_linear_equiv_at x hx₁).prod (e₂.continuous_linear_equiv_at x hx₂) :=
-- begin
--   ext1,
--   funext v,
--   obtain ⟨v₁, v₂⟩ := v,
--   rw [(e₁.prod e₂).continuous_linear_equiv_at_apply, trivialization.prod],
--   exact congr_arg prod.snd (prod_apply hx₁ hx₂ v₁ v₂),
-- end

end topological_vector_bundle
