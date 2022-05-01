/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ring.basic
import algebra.group_power.basic
import tactic.nth_rewrite.default

/-!
# Idempotents

This file defines idempotents for an arbitary multiplication and proves some basic results:

* In a semigroup, the product of two commuting idempotents is an idempotent;
* In a (non-associative) ring, p is an idempotent if and only if 1-p is an idempotent.

## Tags

projection, idempotent
-/

variables {M N S M₀ M₁ R G: Type*}
variables [has_mul M] [monoid N] [semigroup S] [mul_zero_class M₀] [mul_one_class M₁]
  [non_assoc_ring R] [group G]

/--
An element `p` is said to be idempotent if `p * p = p`
-/
def is_idempotent_elem (p : M) : Prop := p * p = p

lemma all [is_idempotent M (*)] (a : M) : is_idempotent_elem a := is_idempotent.idempotent a

namespace is_idempotent_elem

lemma eq {p : M} (h : is_idempotent_elem p) : p * p = p := h

lemma mul_of_commute {p q : S} (h : commute p q) (h₁ : is_idempotent_elem p)
  (h₂ : is_idempotent_elem q) : is_idempotent_elem (p * q)  := by rw [is_idempotent_elem, mul_assoc,
    ← mul_assoc q, ←h.eq, mul_assoc p, h₂.eq, ← mul_assoc, h₁.eq]

lemma zero : is_idempotent_elem (0 : M₀) := mul_zero _

lemma one : is_idempotent_elem (1 : M₁) := mul_one _

lemma one_sub {p : R} (h : is_idempotent_elem p) : is_idempotent_elem (1 - p) :=
begin
  rw is_idempotent_elem at h,
  rw [is_idempotent_elem, mul_sub_left_distrib, mul_one, sub_mul, one_mul, h, sub_self, sub_zero],
end

@[simp] lemma one_sub_iff {p : R} : is_idempotent_elem (1 - p) ↔ is_idempotent_elem p :=
⟨ λ h, sub_sub_cancel 1 p ▸ h.one_sub, is_idempotent_elem.one_sub ⟩

lemma powers {p : N} (n : ℕ) (h : is_idempotent_elem p) : p^(n + 1) = p :=
begin
  induction n with n ih,
  { rw [nat.zero_add, pow_one], },
  { rw [pow_succ, ih, h.eq], }
end

lemma group_one {p : G} (h : is_idempotent_elem p) : p = 1 :=
begin
  rw ← mul_left_inv p,
  nth_rewrite_rhs 1 ← h.eq,
  rw [← mul_assoc, mul_left_inv, one_mul],
end

/-! ### Instances on `subtype is_idempotent_elem` -/
section instances

instance : has_zero { p : M₀ // is_idempotent_elem p } := { zero := ⟨ 0, zero ⟩ }

@[simp] lemma coe_zero : ↑(0 : {p : M₀ // is_idempotent_elem p}) = (0 : M₀) := rfl

instance : has_one { p : M₁ // is_idempotent_elem p } := { one := ⟨ 1, one ⟩ }

@[simp] lemma coe_one : ↑(1 : { p : M₁ // is_idempotent_elem p }) = (1 : M₁) := rfl

instance : has_compl { p : R // is_idempotent_elem p } := ⟨λ p, ⟨1 - p, p.prop.one_sub⟩⟩

@[simp] lemma coe_compl (p : { p : R // is_idempotent_elem p }) : ↑(pᶜ) = (1 : R) - ↑p := rfl

@[simp] lemma compl_compl (p : {p : R // is_idempotent_elem p}) : pᶜᶜ = p :=
subtype.ext $ sub_sub_cancel _ _

@[simp] lemma zero_compl : (0 : {p : R // is_idempotent_elem p})ᶜ = 1 := subtype.ext $ sub_zero _

@[simp] lemma one_compl : (1 : {p : R // is_idempotent_elem p})ᶜ = 0 := subtype.ext $ sub_self _

end instances

end is_idempotent_elem
