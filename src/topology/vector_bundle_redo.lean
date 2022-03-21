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
def continuous_transitions (e : local_homeomorph (B × F) (B × F)) : Prop :=
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
(nice : ∀ e e' ∈ trivialization_atlas,
  continuous_transitions 𝕜 B F (by exact e.to_local_homeomorph.symm.trans e'.to_local_homeomorph))
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
(continuous_coord_change : ∀ e e' ∈ pretrivialization_atlas, ∃ ε : B → (F ≃L[𝕜] F),
  continuous_on (λ b, (ε b : F →L[𝕜] F)) (e.base_set ∩ e'.base_set) ∧
  ∀ b ∈ e.base_set ∩ e'.base_set,
    ∀ v : F, (e.to_local_equiv.symm.trans e'.to_local_equiv) (b, v) = (b, ε b v))

namespace really_topological_vector_prebundle

variables {𝕜 E F}

/-- Natural identification of `really_topological_vector_prebundle` as a
`topological_vector_prebundle`. -/
def to_topological_vector_prebundle (a : really_topological_vector_prebundle 𝕜 F E) :
  topological_vector_prebundle 𝕜 F E :=
{ continuous_triv_change := λ e he e' he', begin
    obtain ⟨ε, hε, heε⟩ := a.continuous_coord_change e he e' he',
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

/-- Make a `really_topological_vector_bundle` from a `really_topological_vector_prebundle`. -/
def to_really_topological_vector_bundle (a : really_topological_vector_prebundle 𝕜 F E) :
  @really_topological_vector_bundle 𝕜 _ _ _ F _ _ _ E _ _
    a.to_topological_vector_prebundle.fiber_topology
    a.to_topological_vector_prebundle.total_space_topology :=
begin
  letI := a.to_topological_vector_prebundle.fiber_topology,
  letI := a.to_topological_vector_prebundle.total_space_topology,
  exact
  { nice := λ e he e' he', begin
        obtain ⟨ε, hε, hee'ε⟩ :=
        a.continuous_coord_change e.to_pretrivialization _ e'.to_pretrivialization _,
        { refine ⟨e.base_set ∩ e'.base_set, _, _, ε, hε, hee'ε⟩,
          { sorry },
          { sorry } },
        { sorry },
        { sorry }
      end,
    .. a.to_topological_vector_prebundle.to_topological_vector_bundle }
end

end really_topological_vector_prebundle

end
