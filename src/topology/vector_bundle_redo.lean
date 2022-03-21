/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.normed_space.bounded_linear_maps
import topology.vector_bundle

/-! # Topological vector bundles -/

noncomputable theory

open set filter bundle topological_vector_bundle

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (B : Type*) [topological_space B]
  (F : Type*) [normed_group F] [normed_space 𝕜 F] [complete_space F]

/-- The valid transition functions for a topological vector bundle over `B` modelled on
a normed space `F`: a transition function must be a local homeomorphism of `B × F` with source and
target both `s ×ˢ univ`, which on this set is of the form `λ (b, v), (b, ε b v)` for some continuous
map `ε` from `s` to `F ≃L[𝕜] F`.  Here continuity is with respect to the operator norm on
`F ≃L[𝕜] F`. -/
def continuous_transitions (e : local_equiv (B × F) (B × F)) : Prop :=
∃ s : set B, e.source = s ×ˢ (univ : set F) ∧ e.target = s ×ˢ (univ : set F)
    ∧ ∃ ε : B → (F ≃L[𝕜] F), continuous_on (λ b, (ε b : F →L[𝕜] F)) s
      ∧ ∀ b ∈ s, ∀ v : F, e (b, v) = (b, ε b v)

variables {B}
variables (E : B → Type*) [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]

section
variables [∀ x : B, topological_space (E x)] [topological_space (total_space E)]

/-- A topological vector bundle is the former definition of a topological vector bundle, with the
further property that the transition functions are continuous as maps from a subset of `B` into
`F →L[𝕜] F` (with respect to the operator norm). -/
class really_topological_vector_bundle extends topological_vector_bundle 𝕜 F E :=
(continuous_coord_change : ∀ e e' ∈ trivialization_atlas,
  continuous_transitions 𝕜 B F (by exact e.to_local_equiv.symm.trans e'.to_local_equiv))
-- what is the `by exact` doing here???

end

section

/-! ### Topological vector prebundle -/

open topological_space

/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphisms and hence vector bundle trivializations. -/
@[nolint has_inhabited_instance]
structure really_topological_vector_prebundle :=
(pretrivialization_atlas : set (topological_vector_bundle.pretrivialization 𝕜 F E))
(pretrivialization_at : B → topological_vector_bundle.pretrivialization 𝕜 F E)
(mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).base_set)
(pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas)
(continuous_coord_change : ∀ e e' ∈ pretrivialization_atlas,
  continuous_transitions 𝕜 B F (by exact e.to_local_equiv.symm.trans e'.to_local_equiv))

namespace really_topological_vector_prebundle

variables {𝕜 E F}

/-- Natural identification of `really_topological_vector_prebundle` as a
`topological_fiber_prebundle`. -/
def to_topological_fiber_prebundle (a : really_topological_vector_prebundle 𝕜 F E) :
  topological_fiber_prebundle F (proj E) :=
{ pretrivialization_atlas :=
    pretrivialization.to_fiber_bundle_pretrivialization '' a.pretrivialization_atlas,
  pretrivialization_at := λ x, (a.pretrivialization_at x).to_fiber_bundle_pretrivialization,
  pretrivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_triv_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    obtain ⟨s, hs, hs', ε, hε, heε⟩ := a.continuous_coord_change e he e' he',
    have h_source : (e'.to_local_equiv.target ∩ (e'.to_local_equiv.symm) ⁻¹'
      e.to_local_equiv.source) = (e.to_local_equiv.symm.trans e'.to_local_equiv).source,
    { sorry },
    have : continuous_on (λ p : B × F, (p.1, ε p.1 p.2))
      (e'.to_local_equiv.target ∩ (e'.to_local_equiv.symm) ⁻¹' e.to_local_equiv.source),
    { rw h_source,
      sorry },
    refine this.congr _,
    rintros ⟨b, v⟩ h,
    sorry,
  end,
  .. a }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def total_space_topology (a : really_topological_vector_prebundle 𝕜 F E) :
  topological_space (total_space E) :=
a.to_topological_fiber_prebundle.total_space_topology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivialization_of_mem_pretrivialization_atlas (a : really_topological_vector_prebundle 𝕜 F E)
  {e : topological_vector_bundle.pretrivialization 𝕜 F E} (he : e ∈ a.pretrivialization_atlas) :
  @topological_vector_bundle.trivialization 𝕜 _ F E _ _ _ _ _ _ _ a.total_space_topology :=
begin
  letI := a.total_space_topology,
  exact
  { linear := e.linear,
    .. a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas ⟨e, he, rfl⟩ }
end

variable (a : really_topological_vector_prebundle 𝕜 F E)

lemma mem_trivialization_at_source (b : B) (x : E b) :
  total_space_mk E b x ∈ (a.pretrivialization_at b).source :=
begin
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, proj],
  exact a.mem_base_pretrivialization_at b,
end

@[simp] lemma total_space_mk_preimage_source (b : B) :
  (total_space_mk E b) ⁻¹' (a.pretrivialization_at b).source = univ :=
begin
  apply eq_univ_of_univ_subset,
  rw [(a.pretrivialization_at b).source_eq, ←preimage_comp, function.comp],
  simp only [proj],
  rw preimage_const_of_mem _,
  exact a.mem_base_pretrivialization_at b,
end

def fiber_topology (b : B) : topological_space (E b) :=
topological_space.induced (total_space_mk E b) a.total_space_topology

noncomputable lemma to_really_topological_vector_bundle :
  @really_topological_vector_bundle 𝕜 _ _ _ F _ _ _ E _ _ a.fiber_topology a.total_space_topology :=
{ total_space_mk_inducing := λ b,
  begin
    letI := a.total_space_topology,
    letI := a.fiber_topology,
    exact ⟨rfl⟩,
  end,
  trivialization_atlas := {e | ∃ e₀ (he₀ : e₀ ∈ a.pretrivialization_atlas),
    e = a.trivialization_of_mem_pretrivialization_atlas he₀},
  trivialization_at := λ x, a.trivialization_of_mem_pretrivialization_atlas
    (a.pretrivialization_mem_atlas x),
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at,
  trivialization_mem_atlas := λ x, ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
  continuous_coord_change := begin
    rintros _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩,
    exact a.continuous_coord_change e he e' he',
  end }

end really_topological_vector_prebundle

end
