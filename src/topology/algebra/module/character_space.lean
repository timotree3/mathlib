/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import topology.algebra.module.weak_dual
import topology.algebra.algebra
import algebra.algebra.spectrum
import topology.continuous_function.zero_at_infty
import topology.continuous_function.algebra

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `character_space 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `to_alg_hom` which provides the algebra homomorphism
corresponding to any element. We also provide `to_clm` which provides the element as a
continuous linear map. (Even though `weak_dual 𝕜 A` is a type copy of `A →L[𝕜] 𝕜`, this is
often more convenient.)

## TODO

* Prove that the character space is a compact subset of the weak dual. This requires the
  Banach-Alaoglu theorem.

## Tags

character space, Gelfand transform, functional calculus

-/

open_locale zero_at_infty

variables {𝕜 : Type*} {A : Type*}

namespace weak_dual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def character_space (𝕜 : Type*) (A : Type*) [comm_semiring 𝕜] [topological_space 𝕜]
  [has_continuous_add 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [non_unital_non_assoc_semiring A] [topological_space A] [module 𝕜 A] :=
  {φ : weak_dual 𝕜 A | (φ ≠ 0) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

namespace character_space

section non_unital_non_assoc_semiring

variables [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [non_unital_non_assoc_semiring A] [topological_space A]
  [module 𝕜 A]

lemma coe_apply (φ : character_space 𝕜 A) (x : A) : (φ : weak_dual 𝕜 A) x = φ x := rfl

/-- An element of the character space, as a continuous linear map. -/
def to_clm (φ : character_space 𝕜 A) : A →L[𝕜] 𝕜 := (φ : weak_dual 𝕜 A)

lemma to_clm_apply (φ : character_space 𝕜 A) (x : A) : φ x = to_clm φ x := rfl

/-- An element of the character space, as an non-unital algebra homomorphism. -/
@[simps] def to_non_unital_alg_hom (φ : character_space 𝕜 A) : non_unital_alg_hom 𝕜 A 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_mul' := φ.prop.2,
  map_smul' := (to_clm φ).map_smul,
  map_zero' := continuous_linear_map.map_zero _,
  map_add' := continuous_linear_map.map_add _ }

lemma map_zero (φ : character_space 𝕜 A) : φ 0 = 0 := (to_non_unital_alg_hom φ).map_zero
lemma map_add (φ : character_space 𝕜 A) (x y : A) : φ (x + y) = φ x + φ y :=
  (to_non_unital_alg_hom φ).map_add _ _
lemma map_smul (φ : character_space 𝕜 A) (r : 𝕜) (x : A) : φ (r • x) = r • (φ x) :=
  (to_clm φ).map_smul _ _
lemma map_mul (φ : character_space 𝕜 A) (x y : A) : φ (x * y) = φ x * φ y :=
  (to_non_unital_alg_hom φ).map_mul _ _
lemma continuous (φ : character_space 𝕜 A) : continuous φ := (to_clm φ).continuous

end non_unital_non_assoc_semiring

section unital

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [semiring A] [algebra 𝕜 A]

lemma map_one (φ : character_space 𝕜 A) : φ 1 = 1 :=
begin
  have h₁ : (φ 1) * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ←map_mul φ, one_mul],
  rcases mul_eq_zero.mp h₁ with h₂|h₂,
  { exfalso,
    apply φ.prop.1,
    ext,
    rw [continuous_linear_map.zero_apply, ←one_mul x, coe_apply, map_mul φ, h₂, zero_mul] },
  { rw [sub_eq_zero] at h₂,
    exact h₂.symm },
end

@[simp] lemma map_algebra_map (φ : character_space 𝕜 A) (r : 𝕜) : φ (algebra_map 𝕜 A r) = r :=
by rw [algebra.algebra_map_eq_smul_one, map_smul, map_one, smul_eq_mul, mul_one]

/-- An element of the character space, as an algebra homomorphism. -/
@[simps] def to_alg_hom (φ : character_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ map_one' := map_one φ,
  commutes' := λ r, by
  { rw [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id, ring_hom.id_apply],
    change ((φ : weak_dual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r,
    rw [continuous_linear_map.map_smul, algebra.id.smul_eq_mul, coe_apply, map_one φ, mul_one] },
  ..to_non_unital_alg_hom φ }

end unital

section ring

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [ring A] [algebra 𝕜 A]

lemma apply_mem_spectrum [nontrivial 𝕜] (φ : character_space 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
(to_alg_hom φ).apply_mem_spectrum a

end ring

end character_space

end weak_dual

section non_unital_gelfand_transform

open weak_dual

variables [comm_semiring 𝕜] [topological_space 𝕜] [topological_semiring 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [non_unital_semiring A] [topological_space A] [module 𝕜 A]

variables (𝕜) (A)

def non_unital_gelfand_transform : non_unital_alg_hom 𝕜 A C₀(character_space 𝕜 A, 𝕜) :=
{ to_fun := λ a,
  { to_fun := λ φ, φ a,
    continuous_to_fun := (weak_dual.eval_continuous a).comp (continuous_subtype_coe),
    zero_at_infty' := sorry },
  map_smul' := λ _ _, by { ext, exact character_space.map_smul _ _ _ },
  map_mul' := λ _ _, by { ext, exact character_space.map_mul _ _ _ },
  map_zero' := by { ext, exact character_space.map_zero _ },
  map_add' := λ _ _, by { ext, exact character_space.map_add _ _ _} }

end non_unital_gelfand_transform

section gelfand_transform

open weak_dual

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [topological_ring 𝕜]
  [semiring A] [topological_space A] [algebra 𝕜 A]

variables (𝕜) (A)

def gelfand_transform : A →ₐ[𝕜] C(character_space 𝕜 A, 𝕜) :=
{ to_fun := λ a,
  { to_fun := λ φ, φ a,
    continuous_to_fun := (weak_dual.eval_continuous a).comp (continuous_subtype_coe) },
  map_one' := by { ext, exact character_space.map_one _ },
  map_mul' := λ _ _, by { ext, exact character_space.map_mul _ _ _ },
  map_zero' := by { ext, exact character_space.map_zero _ },
  map_add' := λ _ _, by { ext, exact character_space.map_add _ _ _},
  commutes' := λ r, by { ext φ, exact character_space.map_algebra_map _ _ } }

class bijective_gelfand_transform : Prop :=
(bijective : function.bijective (gelfand_transform 𝕜 A))

noncomputable def gelfand_transform_equiv [bijective_gelfand_transform 𝕜 A] :
  A ≃ₐ[𝕜] C(character_space 𝕜 A, 𝕜) :=
alg_equiv.of_bijective (gelfand_transform 𝕜 A) bijective_gelfand_transform.bijective

end gelfand_transform

section continuous_functional_calculus

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [topological_ring 𝕜]
  [ring A] [topological_space A] [topological_ring A] [algebra 𝕜 A]

noncomputable def continuous_functional_calculus (f : C(𝕜, 𝕜)) (a : A)
  [bijective_gelfand_transform 𝕜 (algebra.elemental_algebra 𝕜 a)] : A :=
(gelfand_transform_equiv 𝕜 _).symm $ f.comp $
  (gelfand_transform_equiv 𝕜 _)
    (⟨a, algebra.self_mem_elemental_algebra 𝕜 a⟩ : algebra.elemental_algebra 𝕜 a)

end continuous_functional_calculus
