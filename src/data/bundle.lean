/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import tactic.basic
import algebra.module.basic

/-!
# Bundle
Basic data structure to implement fiber bundles, vector bundles (maybe fibrations?), etc. This file
should contain all possible results that do not involve any topology.
We provide a type synonym of `Σ x, E x` as `bundle.total_space E`, to be able to endow it with
a topology which is not the disjoint union topology `sigma.topological_space`. In general, the
constructions of fiber bundles we will make will be of this form.

## References
- https://en.wikipedia.org/wiki/Bundle_(mathematics)
-/

namespace bundle

variables {B : Type*} (E : B → Type*)

/--
`total_space E` is the total space of the bundle `Σ x, E x`. This type synonym is used to avoid
conflicts with general sigma types.
-/
def total_space := Σ x, E x

instance [inhabited B] [inhabited (E default)] :
  inhabited (total_space E) := ⟨⟨default, default⟩⟩

/-- `bundle.proj E` is the canonical projection `total_space E → B` on the base space. -/
@[simp, reducible] def proj : total_space E → B := sigma.fst

/-- Constructor for the total space of a `topological_fiber_bundle_core`. -/
@[simp, reducible] def total_space_mk (E : B → Type*) (b : B) (a : E b) :
  bundle.total_space E := ⟨b, a⟩

instance {x : B} : has_coe_t (E x) (total_space E) := ⟨sigma.mk x⟩

@[simp] lemma coe_fst (x : B) (v : E x) : (v : total_space E).fst = x := rfl
@[simp] lemma coe_snd {x : B} {y : E x} : (y : total_space E).snd = y := rfl

lemma to_total_space_coe {x : B} (v : E x) : (v : total_space E) = ⟨x, v⟩ := rfl

-- notation for the direct sum of two bundles over the same base
notation E₁ `×ᵇ`:100 E₂ := λ x, E₁ x × E₂ x

/-- `bundle.trivial B F` is the trivial bundle over `B` of fiber `F`. -/
def trivial (B : Type*) (F : Type*) : B → Type* := function.const B F

instance {F : Type*} [inhabited F] {b : B} : inhabited (bundle.trivial B F b) := ⟨(default : F)⟩

/-- The trivial bundle, unlike other bundles, has a canonical projection on the fiber. -/
def trivial.proj_snd (B : Type*) (F : Type*) : (total_space (bundle.trivial B F)) → F := sigma.snd

@[simp] lemma total_space_mk_cast {E} {x : B} (y : total_space E) (h : y.1 = x) :
  total_space_mk E x (cast (congr_arg E h) y.2) = y :=
by { ext, exact h.symm, simp only [cast_heq], }

section pullback

variable {B' : Type*}

/-- The pullback of a bundle `E` over a base `B` under a map `f : B' → B`, denoted by `pullback f E`
or `f *ᵖ E`,  is the bundle over `B'` whose fiber over `b'` is `E (f b')`. -/
def pullback (f : B' → B) (E : B → Type*) := λ x, E (f x)

notation f `*ᵖ` E := pullback f E

/-- The base map `f : B' → B` lifts to a canonical map on the total spaces from a pullback bundle
``f *ᵖ E`` to the total space of `E`, by acting trivially on the fibers. -/
def pullback.lift (f : B' → B) (p : total_space (f *ᵖ E)) :=
total_space_mk E (f p.1) p.2

end pullback

section fiber_structures

variable [∀ x, add_comm_monoid (E x)]

@[simp] lemma coe_snd_map_apply (x : B) (v w : E x) :
  (↑(v + w) : total_space E).snd = (v : total_space E).snd + (w : total_space E).snd := rfl

variables (R : Type*) [semiring R] [∀ x, module R (E x)]

@[simp] lemma coe_snd_map_smul (x : B) (r : R) (v : E x) :
  (↑(r • v) : total_space E).snd = r • (v : total_space E).snd := rfl

end fiber_structures

section trivial_instances
local attribute [reducible] bundle.trivial

variables {F : Type*} {R : Type*} [semiring R] (b : B)

instance [add_comm_monoid F] : add_comm_monoid (bundle.trivial B F b) := ‹add_comm_monoid F›
instance [add_comm_group F] : add_comm_group (bundle.trivial B F b) := ‹add_comm_group F›
instance [add_comm_monoid F] [module R F] : module R (bundle.trivial B F b) := ‹module R F›

end trivial_instances

end bundle
