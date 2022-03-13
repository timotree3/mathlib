/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/

import topology.vector_bundle.basic
import analysis.normed_space.operator_norm

/-! # The bundle of continuous linear maps between two vector bundles over the same base -/

noncomputable theory

open bundle

namespace topological_vector_bundle

variables {𝕜₁ : Type*} [semiring 𝕜₁]
variables {𝕜₂ : Type*} [comm_semiring 𝕜₂] [topological_space 𝕜₂]
variables (σ : 𝕜₁ →+* 𝕜₂)
variables {B : Type*}
  (F₁ : Type*) (E₁ : B → Type*) [Π x, add_comm_monoid (E₁ x)] [Π x, module 𝕜₁ (E₁ x)]
  [Π x : B, topological_space (E₁ x)]
  (F₂ : Type*) (E₂ : B → Type*) [Π x, add_comm_monoid (E₂ x)] [Π x, module 𝕜₂ (E₂ x)]
  [Π x : B, topological_space (E₂ x)] [Π x, has_continuous_add (E₂ x)]
  [Π x, has_continuous_smul 𝕜₂ (E₂ x)]

section defs
include F₁ F₂

/-- The bundle of continuous `σ`-semilinear maps between the topological vector bundles `E₁` and
`E₂`.  Type synonym for `λ x, E₁ x →SL[σ] E₂ x`. -/
@[derive [add_comm_monoid, module 𝕜₂, inhabited], nolint unused_arguments]
def vector_bundle_continuous_linear_map (x : B) :=
E₁ x →SL[σ] E₂ x

instance vector_bundle_continuous_linear_map.add_monoid_hom_class (x : B) :
  add_monoid_hom_class (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ x) (E₁ x) (E₂ x) :=
continuous_linear_map.add_monoid_hom_class

end defs

variables [topological_space B]

variables [add_comm_group F₁] [module 𝕜₁ F₁] [topological_space F₁]
  [topological_space (total_space E₁)]
  [topological_vector_bundle 𝕜₁ F₁ E₁]

variables [add_comm_group F₂] [module 𝕜₂ F₂] [topological_space F₂]
  [topological_space (total_space E₂)]
  [topological_vector_bundle 𝕜₂ F₂ E₂]

namespace pretrivialization

variables (e₁ : trivialization 𝕜₁ F₁ E₁) (e₂ : trivialization 𝕜₂ F₂ E₂)

include e₁ e₂
variables {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.pretrivialization.continuous_linear_map`,
the induced pretrivialization for the continuous semilinear maps from `E₁` to `E₂`. -/
def continuous_linear_map.to_fun'
  (p : total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :
  B × (F₁ →SL[σ] F₂) :=
begin
  obtain ⟨x, L⟩ := p,
  refine ⟨x, _⟩,
  by_cases h : x ∈ e₁.base_set ∧ x ∈ e₂.base_set,
  { let φ₁ := e₁.continuous_linear_equiv_at x h.1,
    let φ₂ := e₂.continuous_linear_equiv_at x h.2,
    exact ((φ₂ : E₂ x →L[𝕜₂] F₂).comp L).comp (φ₁.symm : F₁ →L[𝕜₁] E₁ x) },
  { exact 0 }
end

variables {σ e₁ e₂}

lemma continuous_linear_map.to_fun'_apply {x : B} (h₁ : x ∈ e₁.base_set) (h₂ : x ∈ e₂.base_set)
  (L : E₁ x →SL[σ] E₂ x) :
  continuous_linear_map.to_fun' σ e₁ e₂ ⟨x, L⟩ =
  ⟨x, ((e₂.continuous_linear_equiv_at x h₂ : E₂ x →L[𝕜₂] F₂).comp L).comp
    ((e₁.continuous_linear_equiv_at x h₁).symm : F₁ →L[𝕜₁] E₁ x)⟩ :=
begin
  dsimp [continuous_linear_map.to_fun'],
  rw dif_pos,
  exact ⟨h₁, h₂⟩
end

variables (σ e₁ e₂)

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

variables {σ e₁ e₂}

lemma continuous_linear_map.inv_fun'_apply {x : B} (h₁ : x ∈ e₁.base_set) (h₂ : x ∈ e₂.base_set)
  (f : F₁ →SL[σ] F₂) :
  continuous_linear_map.inv_fun' σ e₁ e₂ ⟨x, f⟩
  = total_space_mk (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) x
    ((((e₂.continuous_linear_equiv_at x h₂).symm : F₂ →L[𝕜₂] E₂ x).comp f).comp
      ((e₁.continuous_linear_equiv_at x h₁) : E₁ x →L[𝕜₁] F₁)) :=
begin
  dsimp [continuous_linear_map.inv_fun'],
  rw dif_pos,
  exact ⟨h₁, h₂⟩
end

variables (σ e₁ e₂)

variables [topological_space (F₁ →SL[σ] F₂)]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
pretrivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`.  That is, the map which
will later become a trivialization, after this direct sum is equipped with the right topological
vector bundle structure. -/
def _root_.topological_vector_bundle.fiber_bundle_pretrivialization.continuous_linear_map :
  topological_fiber_bundle.pretrivialization (F₁ →SL[σ] F₂)
  (proj (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :=
{ to_fun := continuous_linear_map.to_fun' σ e₁ e₂,
  inv_fun := continuous_linear_map.inv_fun' σ e₁ e₂,
  source := (proj (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) ⁻¹'
    (e₁.base_set ∩ e₂.base_set),
  target := (e₁.base_set ∩ e₂.base_set) ×ˢ (set.univ : set (F₁ →SL[σ] F₂)),
  map_source' := λ ⟨x, L⟩ h, ⟨h, set.mem_univ _⟩,
  map_target' := λ ⟨x, f⟩ h, h.1,
  left_inv' := λ ⟨x, L⟩ ⟨h₁, h₂⟩,
  begin
    rw [continuous_linear_map.to_fun'_apply h₁ h₂, continuous_linear_map.inv_fun'_apply h₁ h₂],
    simp only [sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_and],
    ext v,
    simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe, function.comp_app,
      continuous_linear_equiv.symm_apply_apply],
  end,
  right_inv' := λ ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩,
  begin
    rw [continuous_linear_map.inv_fun'_apply h₁ h₂, continuous_linear_map.to_fun'_apply h₁ h₂],
    simp only [prod.mk.inj_iff, eq_self_iff_true, true_and],
    ext v,
    simp only [continuous_linear_map.coe_comp', continuous_linear_equiv.coe_coe, function.comp_app,
      continuous_linear_equiv.apply_symm_apply],
  end,
  open_target := (e₁.open_base_set.inter e₂.open_base_set).prod is_open_univ,
  base_set := e₁.base_set ∩ e₂.base_set,
  open_base_set := e₁.open_base_set.inter e₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ ⟨x, f⟩ h, rfl }

variables [has_continuous_add F₂] [has_continuous_smul 𝕜₂ F₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
pretrivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`.  That is, the map which
will later become a trivialization, after this direct sum is equipped with the right topological
vector bundle structure. -/
def continuous_linear_map :
  pretrivialization 𝕜₂ (F₁ →SL[σ] F₂) (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ linear := λ x h,
  { map_add := λ L L', sorry,
    map_smul := λ c L, sorry, },
  .. topological_vector_bundle.fiber_bundle_pretrivialization.continuous_linear_map σ e₁ e₂ }

@[simp] lemma base_set_continuous_linear_map :
  (continuous_linear_map σ e₁ e₂).base_set = e₁.base_set ∩ e₂.base_set :=
rfl

lemma open_base_set_continuous_linear_map
  (e₁ : trivialization 𝕜₁ F₁ E₁) (e₂ : trivialization 𝕜₂ F₂ E₂) :
  is_open (continuous_linear_map σ e₁ e₂).base_set :=
begin
  rw base_set_continuous_linear_map,
  exact e₁.to_pretrivialization.open_base_set.inter e₂.open_base_set,
end

lemma continuous_linear_map_apply {e₁ : trivialization 𝕜₁ F₁ E₁}
  {e₂ : trivialization 𝕜₂ F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (L : E₁ x →SL[σ] E₂ x) :
  continuous_linear_map σ e₁ e₂ ⟨x, L⟩
  = ⟨x, ((e₂.continuous_linear_equiv_at x hx₂ : E₂ x →L[𝕜₂] F₂).comp L).comp
      ((e₁.continuous_linear_equiv_at x hx₁).symm : F₁ →L[𝕜₁] E₁ x)⟩ :=
continuous_linear_map.to_fun'_apply hx₁ hx₂ L

lemma continuous_linear_map_symm_apply {e₁ : trivialization 𝕜₁ F₁ E₁}
  {e₂ : trivialization 𝕜₂ F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set)
  (f : F₁ →SL[σ] F₂) :
  (continuous_linear_map σ e₁ e₂).to_local_equiv.symm (x, f)
  = ⟨x, (((e₂.continuous_linear_equiv_at x hx₂).symm : F₂ →L[𝕜₂] E₂ x).comp f).comp
      ((e₁.continuous_linear_equiv_at x hx₁) : E₁ x →L[𝕜₁] F₁)⟩ :=
continuous_linear_map.inv_fun'_apply hx₁ hx₂ f

lemma continuous_triv_change_continuous_linear_map
  (e₁ f₁ : trivialization 𝕜₁ F₁ E₁) (e₂ f₂ : trivialization 𝕜₂ F₂ E₂) :
  continuous_on
    ((continuous_linear_map σ e₁ e₂
      : total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) → B × (F₁ →SL[σ] F₂))
    ∘ (continuous_linear_map σ f₁ f₂).to_local_equiv.symm)
    ((continuous_linear_map σ f₁ f₂).target
    ∩ ((continuous_linear_map σ f₁ f₂).to_local_equiv.symm) ⁻¹'
      (continuous_linear_map σ e₁ e₂).source) :=
sorry
-- begin
--   refine continuous_on.prod' _ _,
--   { apply continuous_fst.continuous_on.congr,
--     rintros p ⟨hp₁, hp₂⟩,
--     convert (continuous_linear_map e₁ e₂).to_fiber_bundle_pretrivialization.coe_fst hp₂,
--     rw (continuous_linear_map f₁ f₂).to_fiber_bundle_pretrivialization.proj_symm_apply hp₁ },
--   rw [topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--     pretrivialization.base_set_continuous_linear_map, pretrivialization.base_set_continuous_linear_map],
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
--       rw [continuous_linear_map_symm_apply hx.2.1 hx.2.2, continuous_linear_map_apply hxe₁ hxe₂],
--       dsimp,
--       rw [f₁.symm_apply_eq_continuous_linear_map_continuous_linear_equiv_at_symm] } },
--   { refine ((continuous_snd.comp_continuous_on ψ₂.continuous_on).comp
--       (continuous_id.continuous_linear_map_map continuous_snd).continuous_on _).congr _,
--     { rw hψ₂,
--       mfld_set_tac },
--     { rintros ⟨x, ⟨w₁, w₂⟩⟩ ⟨hx, -⟩,
--       have hxe₁ : x ∈ e₁.base_set := hx.1.1,
--       have hxe₂ : x ∈ e₂.base_set := hx.1.2,
--       dsimp,
--       rw [continuous_linear_map_symm_apply hx.2.1 hx.2.2, continuous_linear_map_apply hxe₁ hxe₂],
--       dsimp,
--       rw [f₂.symm_apply_eq_continuous_linear_map_continuous_linear_equiv_at_symm] } },
-- end

end pretrivialization

open pretrivialization

variables [topological_space (F₁ →SL[σ] F₂)]

variables [has_continuous_add F₂] [has_continuous_smul 𝕜₂ F₂]

/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`topological_vector_prebundle` (this is an auxiliary construction for the
`topological_vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def _root_.vector_bundle_continuous_linear_map.topological_vector_prebundle :
  topological_vector_prebundle 𝕜₂ (F₁ →SL[σ] F₂)
  (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
{ pretrivialization_at := λ x,
    pretrivialization.continuous_linear_map σ (trivialization_at 𝕜₁ F₁ E₁ x) (trivialization_at 𝕜₂ F₂ E₂ x),
  mem_base_pretrivialization_at := λ x,
    ⟨mem_base_set_trivialization_at 𝕜₁ F₁ E₁ x, mem_base_set_trivialization_at 𝕜₂ F₂ E₂ x⟩,
  continuous_triv_change := λ p q, sorry }
  -- pretrivialization.continuous_triv_change_continuous_linear_map
  --   (trivialization_at 𝕜₁ F₁ E₁ p)
  --   (trivialization_at 𝕜₁ F₁ E₁ q)
  --   (trivialization_at 𝕜₂ F₂ E₂ p)
  --   (trivialization_at 𝕜₂ F₂ E₂ q) }

--   total_space_mk_inducing := λ b,
--   begin
--     let e₁ := trivialization_at 𝕜 F₁ E₁ b,
--     let e₂ := trivialization_at 𝕜 F₂ E₂ b,
--     have hb₁ : b ∈ e₁.base_set := mem_base_set_trivialization_at 𝕜 F₁ E₁ b,
--     have hb₂ : b ∈ e₂.base_set := mem_base_set_trivialization_at 𝕜 F₂ E₂ b,
--     have key : inducing (λ w : E₁ b × E₂ b,
--       (b, e₁.continuous_linear_equiv_at b hb₁ w.1, e₂.continuous_linear_equiv_at b hb₂ w.2)),
--     { refine (inducing_continuous_linear_map_mk b).comp _,
--       exact ((e₁.continuous_linear_equiv_at b hb₁).to_homeomorph.inducing.continuous_linear_map_mk
--         (e₂.continuous_linear_equiv_at b hb₂).to_homeomorph.inducing) },
--     { convert key,
--       ext1 w,
--       simpa using continuous_linear_map_apply hb₁ hb₂ w.1 w.2 },
--   end }

/-- Topology on the continuous `σ`-semilinear_maps between the respective fibres at a point of two
"normable" vector bundles over the same base. Here "normable" means that the bundles have fibres
modelled on normed spaces `F₁`, `F₂` respectively.  The topology we put on the continuous
`σ`-semilinear_maps is the topology coming from the operator norm on maps from `F₁` to `F₂`. -/
instance (x : B) : topological_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂ x) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle σ F₁ E₁ F₂ E₂).fiber_topology x

/-- Topology on the total space of the continuous `σ`-semilinear_maps between two "normable" vector
bundles over the same base. -/
instance : topological_space (total_space (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂)) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle σ F₁ E₁ F₂ E₂).total_space_topology

/-- The continuous `σ`-semilinear_maps between two vector bundles form a vector bundle. -/
instance vector_bundle_continuous_linear_map.topological_vector_bundle :
  topological_vector_bundle 𝕜₂ (F₁ →SL[σ] F₂)
    (vector_bundle_continuous_linear_map σ F₁ E₁ F₂ E₂) :=
(vector_bundle_continuous_linear_map.topological_vector_prebundle σ F₁ E₁ F₂ E₂).to_topological_vector_bundle

-- variables {𝕜 F₁ E₁ F₂ E₂}

-- /-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
-- trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-- -/
-- def trivialization.continuous_linear_map (e₁ : trivialization 𝕜 F₁ E₁) (e₂ : trivialization 𝕜 F₂ E₂) :
--   trivialization 𝕜 (F₁ × F₂) (vector_bundle_continuous_linear_map 𝕜 F₁ E₁ F₂ E₂) :=
-- { open_source := (open_base_set_continuous_linear_map e₁ e₂).preimage
--     (topological_vector_bundle.continuous_proj 𝕜 B (F₁ × F₂)),
--   continuous_to_fun :=
--   begin
--     apply topological_fiber_prebundle.continuous_on_of_comp_right,
--     { exact e₁.open_base_set.inter e₂.open_base_set },
--     intros b,
--     convert continuous_triv_change_continuous_linear_map e₁ (trivialization_at 𝕜 F₁ E₁ b) e₂
--       (trivialization_at 𝕜 F₂ E₂ b),
--     rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--     refl,
--   end,
--   continuous_inv_fun := λ x hx, continuous_at.continuous_within_at
--   begin
--     let f₁ := trivialization_at 𝕜 F₁ E₁ x.1,
--     let f₂ := trivialization_at 𝕜 F₂ E₂ x.1,
--     have H :
--       (continuous_linear_map e₁ e₂).target ∩ (continuous_linear_map e₁ e₂).to_local_equiv.symm ⁻¹' (continuous_linear_map f₁ f₂).source ∈ nhds x,
--     { rw topological_fiber_bundle.pretrivialization.target_inter_preimage_symm_source_eq,
--       refine is_open.mem_nhds _ ⟨⟨_, hx.1⟩, mem_univ _⟩,
--       { exact ((open_base_set_continuous_linear_map f₁ f₂).inter (open_base_set_continuous_linear_map e₁ e₂)).continuous_linear_map is_open_univ },
--       { exact ⟨mem_base_set_trivialization_at 𝕜 F₁ E₁ x.1,
--           mem_base_set_trivialization_at 𝕜 F₂ E₂ x.1⟩ } },
--     let a := (vector_bundle_continuous_linear_map.topological_vector_prebundle
--       𝕜 F₁ E₁ F₂ E₂).to_topological_fiber_prebundle,
--     rw (a.trivialization_at x.1).to_local_homeomorph.continuous_at_iff_continuous_at_comp_left,
--     { exact (continuous_triv_change_continuous_linear_map f₁ e₁ f₂ e₂).continuous_at H },
--     { exact filter.mem_of_superset H (inter_subset_right _ _) },
--   end,
--   .. pretrivialization.continuous_linear_map e₁ e₂ }

-- @[simp] lemma trivialization.base_set_continuous_linear_map (e₁ : trivialization 𝕜 F₁ E₁)
--   (e₂ : trivialization 𝕜 F₂ E₂) :
--   (e₁.continuous_linear_map e₂).base_set = e₁.base_set ∩ e₂.base_set :=
-- rfl

-- @[simp] lemma trivialization.continuous_linear_equiv_at_continuous_linear_map {e₁ : trivialization 𝕜 F₁ E₁}
--   {e₂ : trivialization 𝕜 F₂ E₂} {x : B} (hx₁ : x ∈ e₁.base_set) (hx₂ : x ∈ e₂.base_set) :
--   (e₁.continuous_linear_map e₂).continuous_linear_equiv_at x ⟨hx₁, hx₂⟩
--   = (e₁.continuous_linear_equiv_at x hx₁).continuous_linear_map (e₂.continuous_linear_equiv_at x hx₂) :=
-- begin
--   ext1,
--   funext v,
--   obtain ⟨v₁, v₂⟩ := v,
--   rw [(e₁.continuous_linear_map e₂).continuous_linear_equiv_at_apply, trivialization.continuous_linear_map],
--   exact congr_arg continuous_linear_map.snd (continuous_linear_map_apply hx₁ hx₂ v₁ v₂),
-- end

end topological_vector_bundle
