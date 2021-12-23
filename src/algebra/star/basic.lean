/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.apply_fun
import algebra.field.opposite
import algebra.field_power
import data.equiv.ring_aut
import group_theory.group_action.units
import group_theory.group_action.opposite
import algebra.ring.comp_typeclasses
import algebra.smul_with_zero

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/


universes u v

open mul_opposite

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class has_star (R : Type u) :=
(star : R → R)

variables {R : Type u}

export has_star (star)

/--
A star operation (e.g. complex conjugate).
-/
add_decl_doc star


/--
Typeclass for a star operation with is involutive.
-/
class has_involutive_star (R : Type u) extends has_star R :=
(star_involutive : function.involutive star)

export has_involutive_star (star_involutive)

@[simp] lemma star_star [has_involutive_star R] (r : R) : star (star r) = r :=
star_involutive _

lemma star_injective [has_involutive_star R] : function.injective (star : R → R) :=
star_involutive.injective

/--
A `*`-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_monoid (R : Type u) [monoid R] extends has_involutive_star R :=
(star_mul : ∀ r s : R, star (r * s) = star s * star r)

export star_monoid (star_mul)
attribute [simp] star_mul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp] lemma star_mul' [comm_monoid R] [star_monoid R] (x y : R) :
  star (x * y) = star x * star y :=
(star_mul x y).trans (mul_comm _ _)

/-- `star` as an `mul_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def star_mul_equiv [monoid R] [star_monoid R] : R ≃* Rᵐᵒᵖ :=
{ to_fun := λ x, mul_opposite.op (star x),
  map_mul' := λ x y, (star_mul x y).symm ▸ (mul_opposite.op_mul _ _),
  ..(has_involutive_star.star_involutive.to_equiv star).trans op_equiv}

/-- `star` as a `mul_aut` for commutative `R`. -/
@[simps apply]
def star_mul_aut [comm_monoid R] [star_monoid R] : mul_aut R :=
{ to_fun := star,
  map_mul' := star_mul',
  ..(has_involutive_star.star_involutive.to_equiv star) }

variables (R)

@[simp] lemma star_one [monoid R] [star_monoid R] : star (1 : R) = 1 :=
op_injective $ (star_mul_equiv : R ≃* Rᵐᵒᵖ).map_one.trans (op_one _).symm

variables {R}

@[simp] lemma star_pow [monoid R] [star_monoid R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_pow x n).trans (op_pow (star x) n).symm

@[simp] lemma star_inv [group R] [star_monoid R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_inv x).trans (op_inv (star x)).symm

@[simp] lemma star_zpow [group R] [star_monoid R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
op_injective $
  ((star_mul_equiv : R ≃* Rᵐᵒᵖ).to_monoid_hom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp] lemma star_div [comm_group R] [star_monoid R] (x y : R) : star (x / y) = star x / star y :=
(star_mul_aut : R ≃* R).to_monoid_hom.map_div _ _

section
open_locale big_operators

@[simp] lemma star_prod [comm_monoid R] [star_monoid R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∏ x in s, f x) = ∏ x in s, star (f x) :=
(star_mul_aut : R ≃* R).map_prod _ _

end

/--
Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def star_monoid_of_comm {R : Type*} [comm_monoid R] : star_monoid R :=
{ star := id,
  star_involutive := λ x, rfl,
  star_mul := mul_comm }

section
local attribute [instance] star_monoid_of_comm

/-- Note that since `star_monoid_of_comm` is reducible, `simp` can already prove this. --/
lemma star_id_of_comm {R : Type*} [comm_semiring R] {x : R} : star x = x := rfl

end

/--
A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.
-/
class star_add_monoid (R : Type u) [add_monoid R] extends has_involutive_star R :=
(star_add : ∀ r s : R, star (r + s) = star r + star s)

export star_add_monoid (star_add)
attribute [simp] star_add

/-- `star` as an `add_equiv` -/
@[simps apply]
def star_add_equiv [add_monoid R] [star_add_monoid R] : R ≃+ R :=
{ to_fun := star,
  map_add' := star_add,
  ..(has_involutive_star.star_involutive.to_equiv star)}

variables (R)

@[simp] lemma star_zero [add_monoid R] [star_add_monoid R] : star (0 : R) = 0 :=
(star_add_equiv : R ≃+ R).map_zero

variables {R}

@[simp] lemma star_neg [add_group R] [star_add_monoid R] (r : R) : star (-r) = - star r :=
(star_add_equiv : R ≃+ R).map_neg _

@[simp] lemma star_sub [add_group R] [star_add_monoid R] (r s : R) :
  star (r - s) = star r - star s :=
(star_add_equiv : R ≃+ R).map_sub _ _

@[simp] lemma star_nsmul [add_comm_monoid R] [star_add_monoid R] (x : R) (n : ℕ) :
  star (n • x) = n • star x :=
(star_add_equiv : R ≃+ R).to_add_monoid_hom.map_nsmul _ _

@[simp] lemma star_zsmul [add_comm_group R] [star_add_monoid R] (x : R) (n : ℤ) :
  star (n • x) = n • star x :=
(star_add_equiv : R ≃+ R).to_add_monoid_hom.map_zsmul _ _

section
open_locale big_operators

@[simp] lemma star_sum [add_comm_monoid R] [star_add_monoid R] {α : Type*}
  (s : finset α) (f : α → R):
  star (∑ x in s, f x) = ∑ x in s, star (f x) :=
(star_add_equiv : R ≃+ R).map_sum _ _

end

/--
A `*`-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a `*`-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [semiring R] extends star_monoid R :=
(star_add : ∀ r s : R, star (r + s) = star r + star s)

@[priority 100]
instance star_ring.to_star_add_monoid [semiring R] [star_ring R] : star_add_monoid R :=
{ star_add := star_ring.star_add }

/-- `star` as an `ring_equiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def star_ring_equiv [semiring R] [star_ring R] : R ≃+* Rᵐᵒᵖ :=
{ to_fun := λ x, mul_opposite.op (star x),
  ..star_add_equiv.trans (mul_opposite.op_add_equiv : R ≃+ Rᵐᵒᵖ),
  ..star_mul_equiv}

/-- `star` as a `ring_aut` for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `complex_conjugate` -/
def star_ring_aut [comm_semiring R] [star_ring R] : ring_aut R :=
{ to_fun := star,
  ..star_add_equiv,
  ..star_mul_aut }

localized "notation `conj` := star_ring_aut" in complex_conjugate

/-- This is not a simp lemma, since we usually want simp to keep `star_ring_aut` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
lemma star_ring_aut_apply [comm_semiring R] [star_ring R] {x : R} :
  star_ring_aut x = star x := rfl

@[simp] lemma star_ring_aut_self_apply [comm_semiring R] [star_ring R] (x : R) :
  star_ring_aut (star_ring_aut x) = x := star_star x

-- A more convenient name for complex conjugation
alias star_ring_aut_self_apply ← complex.conj_conj
alias star_ring_aut_self_apply ← is_R_or_C.conj_conj

@[simp] lemma star_inv' [division_ring R] [star_ring R] (x : R) : star (x⁻¹) = (star x)⁻¹ :=
op_injective $
  ((star_ring_equiv : R ≃+* Rᵐᵒᵖ).to_ring_hom.map_inv x).trans (op_inv (star x)).symm

@[simp] lemma star_zpow₀ [division_ring R] [star_ring R] (x : R) (z : ℤ) :
  star (x ^ z) = star x ^ z :=
op_injective $
  ((star_ring_equiv : R ≃+* Rᵐᵒᵖ).to_ring_hom.map_zpow x z).trans (op_zpow (star x) z).symm

/-- When multiplication is commutative, `star` preserves division. -/
@[simp] lemma star_div' [field R] [star_ring R] (x y : R) : star (x / y) = star x / star y :=
(star_ring_aut : R ≃+* R).to_ring_hom.map_div _ _

@[simp] lemma star_bit0 [ring R] [star_ring R] (r : R) : star (bit0 r) = bit0 (star r) :=
by simp [bit0]

@[simp] lemma star_bit1 [ring R] [star_ring R] (r : R) : star (bit1 r) = bit1 (star r) :=
by simp [bit1]

/--
Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
@[reducible]
def star_ring_of_comm {R : Type*} [comm_semiring R] : star_ring R :=
{ star := id,
  star_add := λ x y, rfl,
  ..star_monoid_of_comm }

/--
An ordered `*`-ring is a ring which is both an ordered ring and a `*`-ring,
and `0 ≤ star r * r` for every `r`.

(In a Banach algebra, the natural ordering is given by the positive cone
which is the closure of the sums of elements `star r * r`.
This ordering makes the Banach algebra an ordered `*`-ring.)
-/
class star_ordered_ring (R : Type u) [ordered_semiring R] extends star_ring R :=
(star_mul_self_nonneg : ∀ r : R, 0 ≤ star r * r)

lemma star_mul_self_nonneg [ordered_semiring R] [star_ordered_ring R] {r : R} : 0 ≤ star r * r :=
star_ordered_ring.star_mul_self_nonneg r

/--
A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[semiring R] [star_ring R] [add_comm_monoid A] [star_add_monoid A] [module R A]`, and that
the statement only requires `[has_star R] [has_star A] [has_scalar R A]`.

If used as `[comm_ring R] [star_ring R] [semiring A] [star_ring A] [algebra R A]`, this represents a
star algebra.
-/
class star_module (R : Type u) (A : Type v) [has_star R] [has_star A] [has_scalar R A] :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a)

export star_module (star_smul)
attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `monoid.to_mul_action`. -/
instance star_monoid.to_star_module [comm_monoid R] [star_monoid R] : star_module R R :=
⟨star_mul'⟩

namespace ring_hom_inv_pair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [comm_semiring R] [star_ring R] :
  ring_hom_inv_pair ((star_ring_aut : ring_aut R) : R →+* R)
    ((star_ring_aut : ring_aut R) : R →+* R) :=
⟨ring_hom.ext star_star, ring_hom.ext star_star⟩

end ring_hom_inv_pair

/-! ### Instances -/

namespace units

variables [monoid R] [star_monoid R]

instance : star_monoid (units R) :=
{ star := λ u,
  { val := star u,
    inv := star ↑u⁻¹,
    val_inv := (star_mul _ _).symm.trans $ (congr_arg star u.inv_val).trans $ star_one _,
    inv_val := (star_mul _ _).symm.trans $ (congr_arg star u.val_inv).trans $ star_one _ },
  star_involutive := λ u, units.ext (star_involutive _),
  star_mul := λ u v, units.ext (star_mul _ _) }

@[simp] lemma coe_star (u : units R) : ↑(star u) = (star ↑u : R) := rfl
@[simp] lemma coe_star_inv (u : units R) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) := rfl

instance {A : Type*} [has_star A] [has_scalar R A] [star_module R A] : star_module (units R) A :=
⟨λ u a, (star_smul ↑u a : _)⟩

end units

lemma is_unit.star [monoid R] [star_monoid R] {a : R} : is_unit a → is_unit (star a)
| ⟨u, hu⟩ := ⟨star u, hu ▸ rfl⟩

@[simp] lemma is_unit_star [monoid R] [star_monoid R] {a : R} : is_unit (star a) ↔ is_unit a :=
⟨λ h, star_star a ▸ h.star, is_unit.star⟩

lemma ring.inverse_star [semiring R] [star_ring R] (a : R) :
  ring.inverse (star a) = star (ring.inverse a) :=
begin
  by_cases ha : is_unit a,
  { obtain ⟨u, rfl⟩ := ha,
    rw [ring.inverse_unit, ←units.coe_star, ring.inverse_unit, ←units.coe_star_inv], },
  rw [ring.inverse_non_unit _ ha, ring.inverse_non_unit _ (mt is_unit_star.mp ha), star_zero],
end

namespace mul_opposite

/-- The opposite type carries the same star operation. -/
instance [has_star R] : has_star (Rᵐᵒᵖ) :=
{ star := λ r, op (star (r.unop)) }

@[simp] lemma unop_star [has_star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) := rfl
@[simp] lemma op_star [has_star R] (r : R) : op (star r) = star (op r) := rfl

instance [has_involutive_star R] : has_involutive_star (Rᵐᵒᵖ) :=
{ star_involutive := λ r, unop_injective (star_star r.unop) }

instance [monoid R] [star_monoid R] : star_monoid (Rᵐᵒᵖ) :=
{ star_mul := λ x y, unop_injective (star_mul y.unop x.unop) }

instance [add_monoid R] [star_add_monoid R] : star_add_monoid (Rᵐᵒᵖ) :=
{ star_add := λ x y, unop_injective (star_add x.unop y.unop) }

instance [semiring R] [star_ring R] : star_ring (Rᵐᵒᵖ) :=
{ .. mul_opposite.star_add_monoid }

end mul_opposite

/-- A commutative star monoid is a star module over its opposite via
`monoid.to_opposite_mul_action`. -/
instance star_monoid.to_opposite_star_module [comm_monoid R] [star_monoid R] : star_module Rᵐᵒᵖ R :=
⟨λ r s, star_mul' s r.unop⟩

variables (R)
/-- The self-adjoint elements of a type with star, as a subtype. -/
def self_adjoints [has_star R] := {x : R // star x = x}
variables {R}

/-- An element `x` of a type with star is self-adjoint if `star x = x`. -/
abbreviation is_self_adjoint [has_star R] (x : R) : Prop := star x = x

namespace self_adjoints

instance [has_star R] : has_coe (self_adjoints R) R := ⟨subtype.val⟩

lemma is_self_adjoint [has_star R] (x : self_adjoints R) : is_self_adjoint (x : R) := x.prop

instance [has_star R] : has_star (self_adjoints R) := ⟨id⟩
instance [has_involutive_star R] : has_involutive_star (self_adjoints R) := ⟨λ _, rfl⟩

@[simp] lemma star_eq [has_star R] {x : self_adjoints R} : star x = x := rfl
@[simp] lemma star_coe_eq [has_star R] {x : self_adjoints R} : star (x : R) = x := x.prop

instance [add_monoid R] [star_add_monoid R] : add_monoid (self_adjoints R) :=
{ add := λ x y, ⟨x.1 + y.1, by rw [star_add, x.2, y.2]⟩,
  zero := ⟨0, star_zero _⟩,
  add_assoc := λ x y z, by { ext, exact add_assoc _ _ _ },
  zero_add := λ x, by simp only [zero_add, subtype.coe_eta, subtype.val_eq_coe],
  add_zero :=  λ x, by simp only [add_zero, subtype.coe_eta, subtype.val_eq_coe] }

@[simp] lemma coe_add [add_monoid R] [star_add_monoid R] (x y : self_adjoints R) :
  (coe : self_adjoints R → R) (x + y) = (x : R) + y := rfl

@[simp] lemma coe_zero [add_monoid R] [star_add_monoid R] :
  (coe : self_adjoints R → R) (0 : self_adjoints R) = (0 : R) := rfl

instance [add_monoid R] [star_add_monoid R] : star_add_monoid (self_adjoints R) := ⟨λ x y, star_eq⟩

instance [add_group R] [star_add_monoid R] : add_group (self_adjoints R) :=
{ neg := λ x, ⟨-x, by simp only [star_coe_eq, star_neg]⟩,
  add_left_neg := λ x, by { ext, exact add_left_neg _ },
  ..self_adjoints.add_monoid }

@[simp] lemma coe_neg [add_group R] [star_add_monoid R] (x : self_adjoints R) :
  (coe : self_adjoints R → R) (-x) = -(x : R) := rfl

@[simp] lemma coe_sub [add_group R] [star_add_monoid R] (x y : self_adjoints R) :
  (coe : self_adjoints R → R) (x - y) = (x : R) - y :=
by { simp only [sub_eq_add_neg], refl }

instance [add_comm_monoid R] [star_add_monoid R] : add_comm_monoid (self_adjoints R) :=
{ add_comm := λ x y, by { ext, exact add_comm _ _ },
  ..self_adjoints.add_monoid }

instance [add_comm_group R] [star_add_monoid R] : add_comm_group (self_adjoints R) :=
{ ..self_adjoints.add_comm_monoid,
  ..self_adjoints.add_group }

instance [monoid R] [star_monoid R] : has_one (self_adjoints R) := ⟨⟨1, star_one _⟩⟩

@[simp] lemma coe_one [monoid R] [star_monoid R] :
  (coe : self_adjoints R → R) (1 : self_adjoints R) = (1 : R) := rfl

instance [comm_monoid R] [star_monoid R] : has_mul (self_adjoints R) :=
⟨λ x y, ⟨(x : R) * y, by simp only [star_mul', star_coe_eq]⟩⟩

@[simp] lemma coe_mul [comm_monoid R] [star_monoid R] (x y : self_adjoints R) :
  (coe : self_adjoints R → R) (x * y) = (x : R) * y := rfl

instance [comm_monoid R] [star_monoid R] : monoid (self_adjoints R) :=
{ mul_assoc := λ x y z, by { ext, exact mul_assoc _ _ _ },
  one_mul := λ x, by { ext, simp only [coe_mul, one_mul, coe_one] },
  mul_one := λ x, by { ext, simp only [mul_one, coe_mul, coe_one] },
  ..self_adjoints.has_one,
  ..self_adjoints.has_mul }

instance [comm_monoid R] [star_monoid R] : comm_monoid (self_adjoints R) :=
{ mul_comm := λ x y, by { ext, exact mul_comm _ _ },
  ..self_adjoints.monoid }

instance [division_ring R] [star_ring R] : has_inv (self_adjoints R) :=
⟨λ x, ⟨(x : R)⁻¹, by simp only [star_inv', star_coe_eq]⟩⟩

@[simp] lemma coe_inv [division_ring R] [star_ring R] (x : self_adjoints R) :
  (coe : self_adjoints R → R) (x⁻¹) = (x : R)⁻¹ := rfl

instance [comm_ring R] [star_ring R] : distrib (self_adjoints R) :=
{ left_distrib := λ x y z, by { ext, exact left_distrib _ _ _ },
  right_distrib := λ x y z, by { ext, exact right_distrib _ _ _ },
  ..show has_add (self_adjoints R), by apply_instance,
  ..show has_mul (self_adjoints R), by apply_instance }

instance [comm_ring R] [star_ring R] : comm_ring (self_adjoints R) :=
{ ..self_adjoints.add_comm_group,
  ..self_adjoints.comm_monoid,
  ..self_adjoints.distrib }

instance [field R] [star_ring R] : field (self_adjoints R) :=
{ inv :=  λ x, ⟨(x.val)⁻¹, by simp only [star_inv', star_coe_eq, subtype.val_eq_coe]⟩,
  exists_pair_ne := ⟨0, 1, subtype.ne_of_val_ne zero_ne_one⟩,
  mul_inv_cancel := λ x hx, by { ext, exact mul_inv_cancel (λ H, hx $ subtype.eq H) },
  inv_zero := by { ext, exact inv_zero },
  ..self_adjoints.comm_ring }

/-- Conjugation of a self-adjoint by an element of the original type: given `r : R` and
`x : self_adjoints R`, we define `r • x` as `r * x * star r`. -/
instance [monoid R] [star_monoid R] : has_scalar R (self_adjoints R) :=
⟨λ r x, ⟨r * x * star r, by simp only [mul_assoc, star_coe_eq, star_star, star_mul]⟩⟩

@[simp] lemma conj_eq_smul [monoid R] [star_monoid R] (r : R) (x : self_adjoints R) :
  (coe : self_adjoints R → R) (r • x) = r * x * star r := rfl

@[simp] lemma conj_eq_smul' [monoid R] [star_monoid R] (r : R) (x : self_adjoints R) :
  (coe : self_adjoints R → R) (star r • x) = star r * x * r :=
by simp only [conj_eq_smul, star_star]

@[simp] lemma mul_self_star_eq_smul_one [monoid R] [star_monoid R] (r : R) :
  (coe : self_adjoints R → R) (r • 1) = r * star r :=
by simp only [conj_eq_smul, mul_one, coe_one]

@[simp] lemma star_mul_self_eq_smul_one [monoid R] [star_monoid R] (r : R) :
  (coe : self_adjoints R → R) (star r • 1) = star r * r :=
by simp only [conj_eq_smul, mul_one, coe_one, star_star]

instance [monoid R] [star_monoid R] : mul_action R (self_adjoints R) :=
{ one_smul := λ x, by { ext, simp only [mul_one, one_mul, conj_eq_smul, star_one] },
  mul_smul := λ r s x, by { ext, simp only [mul_assoc, conj_eq_smul, star_mul] } }

instance [ring R] [star_ring R] : distrib_mul_action R (self_adjoints R) :=
{ smul_add := λ r x y, by { ext, simp only [mul_add, add_mul, conj_eq_smul, coe_add] },
  smul_zero := λ r, by { ext, simp only [coe_zero, zero_mul, conj_eq_smul, mul_zero] } }

instance [ring R] [star_ring R] : smul_with_zero R (self_adjoints R) :=
{ smul_zero := λ r, by { ext, simp only [smul_zero] },
  zero_smul := λ r,  by { ext, simp only [coe_zero, conj_eq_smul, star_zero, mul_zero] } }

end self_adjoints


namespace is_self_adjoint

/-- Construct a self-adjoint element from the assumption `is_self_adjoint x`.  -/
def to_self_adjoints [has_star R] {x : R} (h : is_self_adjoint x) : self_adjoints R := ⟨x, h⟩

lemma star_eq [has_star R] {x : R} (h : is_self_adjoint x) : star x = x := h
lemma star_eq_iff [has_star R] {x : R} : is_self_adjoint x ↔ star x = x := ⟨id, id⟩

section add_monoid

variables [add_monoid R] [star_add_monoid R]
variables {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y)

lemma zero : is_self_adjoint (0 : R) := star_zero R

lemma add : is_self_adjoint (x + y) :=
(hx.to_self_adjoints + hy.to_self_adjoints).is_self_adjoint

end add_monoid

section add_group

variables [add_group R] [star_add_monoid R]
variables {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y)

lemma neg : is_self_adjoint (-x) := (-hx.to_self_adjoints).is_self_adjoint

include hx hy
lemma sub : is_self_adjoint (x - y) := by rw [star_eq_iff, star_sub, star_eq hx, star_eq hy]

end add_group

section monoid

variables [monoid R] [star_monoid R]
variables {x y : R} (hx : is_self_adjoint x) (hy : is_self_adjoint y)

lemma one : is_self_adjoint (1 : R) := star_one R

include hx
lemma conjugate {z : R} : is_self_adjoint (z * x * star z) :=
by simp only [star_eq_iff, mul_assoc, hx.star_eq, star_star, star_mul]

lemma conjugate' {z : R} : is_self_adjoint (star z * x * z) :=
by simp only [star_eq_iff, mul_assoc, hx.star_eq, star_star, star_mul]

end monoid

end is_self_adjoint
