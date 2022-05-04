/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yaël Dillies
-/
import data.set.pointwise
import order.filter.n_ary

/-!
# Pointwise operations on filters

This file defines pointwise operations on filters. This is useful because usual algebraic operations
distribute over pointwise operations. For example,
* `(f₁ * f₂).map m  = f₁.map m * f₂.map m`
* `𝓝 (x * y) = 𝓝 x * 𝓝 y`

## Main declarations

* `0` (`filter.has_zero`): Principal filter at `0 : α`.
* `1` (`filter.has_one`): Principal filter at `1 : α`.
* `f + g` (`filter.has_add`): Addition, filter generated by all `s + t` where `s ∈ f` and `t ∈ g`.
* `f * g` (`filter.has_mul`): Multiplication, filter generated by all `s * t` where `s ∈ f` and
  `t ∈ g`.
* `-f` (`filter.has_neg`): Negation, filter of all `-s` where `s ∈ f`.
* `f⁻¹` (`filter.has_inv`): Inversion, filter of all `x⁻¹` where `s ∈ f`.
* `f - g` (`filter.has_sub`): Subtraction, filter generated by all `x - y` where `s ∈ f` and
  `t ∈ g`.
* `f / g` (`filter.has_div`): Division, filter generated by all `x / y` where `s ∈ f` and `t ∈ g`.
* `f +ᵥ g` (`filter.has_vadd`): Scalar addition, filter generated by all `x +ᵥ y` where `s ∈ f` and
  `t ∈ g`.
* `f -ᵥ g` (`filter.has_vsub`): Scalar subtraction, filter generated by all `x -ᵥ y` where `s ∈ f`
  and `t ∈ g`.
* `f • g` (`filter.has_scalar`): Scalar multiplication, filter generated by all `x • y` where
  `s ∈ f` and `t ∈ g`.
* `a +ᵥ f` (`filter.has_vadd_filter`): Translation, filter of all `a +ᵥ x` where `s ∈ f`.
* `a • f` (`filter.has_scalar_filter`): Scaling, filter of all `a • s` where `s ∈ f`.

## Tags

filter multiplication, filter addition, pointwise addition, pointwise multiplication,
-/

open function set
open_locale filter pointwise

variables {F α β γ δ ε : Type*}

namespace filter

/-! ### `0`/`1` as filters -/

section one
variables [has_one α] {f : filter α} {s : set α}

/-- `1 : filter α` is defined as the filter of sets containing `1 : α` in locale `pointwise`. -/
@[to_additive "`0 : filter α` is defined as the filter of sets containing `0 : α` in locale
`pointwise`."]
protected def has_one : has_one (filter α) := ⟨pure 1⟩

localized "attribute [instance] filter.has_one filter.has_zero" in pointwise

@[simp, to_additive] lemma mem_one : s ∈ (1 : filter α) ↔ (1 : α) ∈ s := mem_pure
@[to_additive] lemma one_mem_one : (1 : set α) ∈ (1 : filter α) := mem_pure.2 one_mem_one
@[simp, to_additive] lemma pure_one : pure 1 = (1 : filter α) := rfl
@[simp, to_additive] lemma principal_one : 𝓟 1 = (1 : filter α) := principal_singleton _
@[to_additive] lemma one_ne_bot : (1 : filter α).ne_bot := filter.pure_ne_bot
@[simp, to_additive] protected lemma map_one' (f : α → β) : (1 : filter α).map f = pure (f 1) := rfl
@[simp, to_additive] lemma le_one_iff : f ≤ 1 ↔ (1 : set α) ∈ f := le_pure_iff
@[simp, to_additive] lemma eventually_one {p : α → Prop} : (∀ᶠ x in 1, p x) ↔ p 1 := eventually_pure
@[simp, to_additive] lemma tendsto_one {a : filter β} {f : β → α} :
   tendsto f a 1 ↔ ∀ᶠ x in a, f x = 1 :=
tendsto_pure

variables [has_one β]

@[simp, to_additive]
protected lemma map_one [one_hom_class F α β] (φ : F) : map φ 1 = 1 :=
by rw [filter.map_one', map_one, pure_one]

end one

/-! ### Filter addition/multiplication -/

section mul
variables [has_mul α] [has_mul β] {f f₁ f₂ g g₁ g₂ h : filter α} {s t : set α}

/-- The filter `f * g` is generated by `{s * t | s ∈ f, t ∈ g}` in locale `pointwise`. -/
@[to_additive "The filter `f + g` is generated by `{s + t | s ∈ f, t ∈ g}` in locale `pointwise`."]
protected def has_mul : has_mul (filter α) :=
/- This is defeq to `map₂ (*) f g`, but the hypothesis unfolds to `t₁ * t₂ ⊆ s` rather than
`set.image2 (*) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ * t₂ ⊆ s}, ..map₂ (*) f g }⟩

localized "attribute [instance] filter.has_mul filter.has_add" in pointwise

@[simp, to_additive] lemma map₂_mul : map₂ (*) f g = f * g := rfl
@[to_additive] lemma mem_mul_iff : s ∈ f * g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ * t₂ ⊆ s := iff.rfl
@[to_additive] lemma mul_mem_mul : s ∈ f → t ∈ g → s * t ∈ f * g := image2_mem_map₂
@[simp, to_additive] lemma bot_mul : ⊥ * g = ⊥ := map₂_bot_left
@[simp, to_additive] lemma mul_bot : f * ⊥ = ⊥ := map₂_bot_right
@[simp, to_additive] lemma mul_eq_bot_iff : f * g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp, to_additive] lemma mul_ne_bot_iff : (f * g).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
@[to_additive] lemma ne_bot.mul : ne_bot f → ne_bot g → ne_bot (f * g) := ne_bot.map₂
@[simp, to_additive] lemma le_mul_iff : h ≤ f * g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s * t ∈ h :=
le_map₂_iff

@[to_additive] instance covariant_mul : covariant_class (filter α) (filter α) (*) (≤) :=
⟨λ f g h, map₂_mono_left⟩

@[to_additive] instance covariant_swap_mul : covariant_class (filter α) (filter α) (swap (*)) (≤) :=
⟨λ f g h, map₂_mono_right⟩

@[to_additive]
protected lemma map_mul [mul_hom_class F α β] (m : F) : (f₁ * f₂).map m = f₁.map m * f₂.map m :=
map_map₂_distrib $ map_mul m

end mul

open_locale pointwise

/-- `filter α` is a `semigroup` under pointwise operations if `α` is.-/
@[to_additive "`filter α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [semigroup α] : semigroup (filter α) :=
{ mul := (*),
  mul_assoc := λ f g h, map₂_assoc mul_assoc }

/-- `filter α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def comm_semigroup [comm_semigroup α] : comm_semigroup (filter α) :=
{ mul_comm := λ f g, map₂_comm mul_comm,
  ..filter.semigroup }

/-- `filter α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mul_one_class [mul_one_class α] : mul_one_class (filter α) :=
{ one := 1,
  mul := (*),
  one_mul := λ f, by simp only [←pure_one, ←map₂_mul, map₂_pure_left, one_mul, map_id'],
  mul_one := λ f, by simp only [←pure_one, ←map₂_mul, map₂_pure_right, mul_one, map_id'] }

/-- `filter α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid [monoid α] : monoid (filter α) :=
{ ..filter.mul_one_class, ..filter.semigroup }

/-- `filter α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`filter α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def comm_monoid [comm_monoid α] : comm_monoid (filter α) :=
{ ..filter.mul_one_class, ..filter.comm_semigroup }

localized "attribute [instance] filter.mul_one_class filter.add_zero_class filter.semigroup
  filter.add_semigroup filter.comm_semigroup filter.add_comm_semigroup filter.monoid
  filter.add_monoid filter.comm_monoid filter.add_comm_monoid" in pointwise

section map

variables [mul_one_class α] [mul_one_class β]

/-- If `φ : α →* β` then `map_monoid_hom φ` is the monoid homomorphism
`filter α →* filter β` induced by `map φ`. -/
@[to_additive "If `φ : α →+ β` then `map_add_monoid_hom φ` is the monoid homomorphism
`filter α →+ filter β` induced by `map φ`."]
def map_monoid_hom [monoid_hom_class F α β] (φ : F) : filter α →* filter β :=
{ to_fun := map φ,
  map_one' := filter.map_one φ,
  map_mul' := λ _ _, filter.map_mul φ }

-- The other direction does not hold in general.
@[to_additive]
lemma comap_mul_comap_le [mul_hom_class F α β] (m : F) {f₁ f₂ : filter β} :
  f₁.comap m * f₂.comap m ≤ (f₁ * f₂).comap m  :=
λ s ⟨t, ⟨t₁, t₂, ht₁, ht₂, t₁t₂⟩, mt⟩,
  ⟨m ⁻¹' t₁, m ⁻¹' t₂, ⟨t₁, ht₁, subset.rfl⟩, ⟨t₂, ht₂, subset.rfl⟩,
    (preimage_mul_preimage_subset _).trans $ (preimage_mono t₁t₂).trans mt⟩

@[to_additive]
lemma tendsto.mul_mul [mul_hom_class F α β] (m : F) {f₁ g₁ : filter α} {f₂ g₂ : filter β} :
  tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ * g₁) (f₂ * g₂) :=
λ hf hg, (filter.map_mul m).trans_le $ mul_le_mul' hf hg

end map

/-! ### Filter negation/inversion -/

section has_inv
variables [has_inv α] {f g : filter α} {s : set α}

/-- The inverse of a filter is the pointwise preimage under `⁻¹` of its sets. -/
@[to_additive "The negation of a filter is the pointwise preimage under `-` of its sets."]
instance : has_inv (filter α) := ⟨map has_inv.inv⟩

@[simp, to_additive] protected lemma map_inv : f.map has_inv.inv = f⁻¹ := rfl
@[to_additive] lemma mem_inv : s ∈ f⁻¹ ↔ has_inv.inv ⁻¹' s ∈ f := iff.rfl
@[to_additive] protected lemma inv_le_inv (hf : f ≤ g) : f⁻¹ ≤ g⁻¹ := map_mono hf
@[simp, to_additive] lemma ne_bot_inv_iff : f⁻¹.ne_bot ↔ ne_bot f := map_ne_bot_iff _
@[to_additive] lemma ne_bot.inv : f.ne_bot → f⁻¹.ne_bot := λ h, h.map _

end has_inv

section has_involutive_inv
variables [has_involutive_inv α] {f : filter α} {s : set α}

@[to_additive] lemma inv_mem_inv (hs : s ∈ f) : s⁻¹ ∈ f⁻¹ := by rwa [mem_inv, inv_preimage, inv_inv]

/-- Inversion is involutive on `filter α` if it is on `α`. -/
@[to_additive "Negation is involutive on `filter α` if it is on `α`."]
def has_involutive_inv : has_involutive_inv (filter α) :=
{ inv_inv := λ f, map_map.trans $ by rw [inv_involutive.comp_self, map_id],
  ..filter.has_inv }

end has_involutive_inv

section group
variables [group α] [group β]

@[to_additive]
lemma map_inv' [monoid_hom_class F α β] (m : F) {f : filter α} : f⁻¹.map m = (f.map m)⁻¹ :=
map_comm (funext $ map_inv m) _

@[to_additive]
lemma tendsto.inv_inv [monoid_hom_class F α β] (m : F) {f₁  : filter α} {f₂ : filter β} :
  tendsto m f₁ f₂ → tendsto m f₁⁻¹ f₂⁻¹ :=
λ hf, (filter.map_inv' m).trans_le $ filter.inv_le_inv hf

end group

/-! ### Filter subtraction/division -/

section div
variables [has_div α] {f f₁ f₂ g g₁ g₂ h : filter α} {s t : set α}

/-- The filter `f / g` is generated by `{s / t | s ∈ f, t ∈ g}` in locale `pointwise`. -/
@[to_additive "The filter `f - g` is generated by `{s - t | s ∈ f, t ∈ g}` in locale `pointwise`."]
protected def has_div : has_div (filter α) :=
/- This is defeq to `map₂ (/) f g`, but the hypothesis unfolds to `t₁ / t₂ ⊆ s` rather than
`set.image2 (/) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ / t₂ ⊆ s}, ..map₂ (/) f g }⟩

localized "attribute [instance] filter.has_div filter.has_sub" in pointwise

@[simp, to_additive] lemma map₂_div : map₂ (/) f g = f / g := rfl
@[to_additive] lemma mem_div : s ∈ f / g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ / t₂ ⊆ s := iff.rfl
@[to_additive] lemma div_mem_div : s ∈ f → t ∈ g → s / t ∈ f / g := image2_mem_map₂
@[simp, to_additive] lemma bot_div : ⊥ / g = ⊥ := map₂_bot_left
@[simp, to_additive] lemma div_bot : f / ⊥ = ⊥ := map₂_bot_right
@[simp, to_additive] lemma div_eq_bot_iff : f / g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp, to_additive] lemma div_ne_bot_iff : (f / g).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
@[to_additive] lemma ne_bot.div : ne_bot f → ne_bot g → ne_bot (f / g) := ne_bot.map₂
@[simp, to_additive] protected lemma le_div_iff :
  h ≤ f / g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s / t ∈ h :=
le_map₂_iff
@[to_additive] protected lemma div_le_div : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ / g₁ ≤ f₂ / g₂ := map₂_mono
@[to_additive] protected lemma div_le_div_left : g₁ ≤ g₂ → f / g₁ ≤ f / g₂ := map₂_mono_left
@[to_additive] protected lemma div_le_div_right : f₁ ≤ f₂ → f₁ / g ≤ f₂ / g := map₂_mono_right

@[to_additive] instance covariant_div : covariant_class (filter α) (filter α) (/) (≤) :=
⟨λ f g h, map₂_mono_left⟩

@[to_additive] instance covariant_swap_div : covariant_class (filter α) (filter α) (swap (/)) (≤) :=
⟨λ f g h, map₂_mono_right⟩

end div

open_locale pointwise

section group
variables [group α] [group β] {f g  : filter α} {f₂ : filter β}

@[to_additive]
protected lemma map_div [monoid_hom_class F α β] (m : F) : (f / g).map m = f.map m / g.map m :=
map_map₂_distrib $ map_div m

@[to_additive]
lemma tendsto.div_div [monoid_hom_class F α β] (m : F) {f₁ g₁ : filter α} {f₂ g₂ : filter β} :
  tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ / g₁) (f₂ / g₂) :=
λ hf hg, (filter.map_div m).trans_le $ filter.div_le_div hf hg

end group

/-TODO: The below instances are duplicate because there is no typeclass greater than
`div_inv_monoid` and `has_involutive_inv` but smaller than `group` and `group_with_zero`. -/

/-- `f / g = f * g⁻¹` for all `f g : filter α` if `a / b = a * b⁻¹` for all `a b : α`. -/
@[to_additive filter.sub_neg_monoid "`f - g = f + -g` for all `f g : filter α` if `a - b = a + -b`
for all `a b : α`."]
protected def div_inv_monoid [group α] : div_inv_monoid (filter α) :=
{ div_eq_mul_inv := λ f g, map_map₂_distrib_right div_eq_mul_inv,
  ..filter.monoid, ..filter.has_inv, ..filter.has_div }

/-- `f / g = f * g⁻¹` for all `f g : filter α` if `a / b = a * b⁻¹` for all `a b : α`. -/
protected def div_inv_monoid' [group_with_zero α] : div_inv_monoid (filter α) :=
{ div_eq_mul_inv := λ f g, map_map₂_distrib_right div_eq_mul_inv,
  ..filter.monoid, ..filter.has_inv, ..filter.has_div }

localized "attribute [instance] filter.div_inv_monoid filter.sub_neg_monoid filter.div_inv_monoid'"
  in pointwise

/-! ### Scalar addition/multiplication of filters -/

section smul
variables [has_scalar α β] {f f₁ f₂ : filter α} {g g₁ g₂ h : filter β} {s : set α} {t : set β}

@[to_additive filter.has_vadd] instance : has_scalar (filter α) (filter β) :=
/- This is defeq to `map₂ (•) f g`, but the hypothesis unfolds to `t₁ • t₂ ⊆ s` rather than
`set.image2 (•) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ • t₂ ⊆ s}, ..map₂ (•) f g }⟩

@[simp, to_additive] lemma map₂_smul : map₂ (•) f g = f • g := rfl
@[to_additive] lemma mem_smul : t ∈ f • g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ • t₂ ⊆ t := iff.rfl
@[to_additive] lemma smul_mem_smul : s ∈ f → t ∈ g → s • t ∈ f • g :=  image2_mem_map₂
@[simp, to_additive] lemma bot_smul : (⊥ : filter α) • g = ⊥ := map₂_bot_left
@[simp, to_additive] lemma smul_bot : f • (⊥ : filter β) = ⊥ := map₂_bot_right
@[simp, to_additive] lemma smul_eq_bot_iff : f • g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp, to_additive] lemma smul_ne_bot_iff : (f • g).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
@[to_additive] lemma ne_bot.smul : ne_bot f → ne_bot g → ne_bot (f • g) := ne_bot.map₂
@[simp, to_additive] lemma le_smul_iff : h ≤ f • g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s • t ∈ h :=
le_map₂_iff
@[to_additive] lemma smul_le_smul : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ • g₁ ≤ f₂ • g₂ := map₂_mono
@[to_additive] lemma smul_le_smul_left : g₁ ≤ g₂ → f • g₁ ≤ f • g₂ := map₂_mono_left
@[to_additive] lemma smul_le_smul_right : f₁ ≤ f₂ → f₁ • g ≤ f₂ • g := map₂_mono_right

@[to_additive] instance covariant_smul : covariant_class (filter α) (filter β) (•) (≤) :=
⟨λ f g h, map₂_mono_left⟩

end smul

@[to_additive]
instance [monoid α] [mul_action α β] : mul_action (filter α) (filter β) :=
{ one_smul := λ f, by simp only [←pure_one, ←map₂_smul, map₂_pure_left, one_smul, map_id'],
  mul_smul := λ f g h, map₂_assoc mul_smul }

/-! ### Scalar subtraction of filters -/

section vsub
variables [has_vsub α β] {f f₁ f₂ g g₁ g₂ : filter β} {h : filter α} {s t : set β}
include α

/-- The filter `f -ᵥ g` is generated by `{s -ᵥ t | s ∈ f, t ∈ g}` in locale `pointwise`. -/
protected def has_vsub : has_vsub (filter α) (filter β) :=
/- This is defeq to `map₂ (-ᵥ) f g`, but the hypothesis unfolds to `t₁ -ᵥ t₂ ⊆ s` rather than
`set.image2 (-ᵥ) t₁ t₂ ⊆ s`. -/
⟨λ f g, { sets := {s | ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ -ᵥ t₂ ⊆ s}, ..map₂ (-ᵥ) f g }⟩

localized "attribute [instance] filter.has_vsub" in pointwise

@[simp] lemma map₂_vsub : map₂ (-ᵥ) f g = f -ᵥ g := rfl
lemma mem_vsub {s : set α} : s ∈ f -ᵥ g ↔ ∃ t₁ t₂, t₁ ∈ f ∧ t₂ ∈ g ∧ t₁ -ᵥ t₂ ⊆ s := iff.rfl
lemma vsub_mem_vsub : s ∈ f → t ∈ g → s -ᵥ t ∈ f -ᵥ g :=  image2_mem_map₂
@[simp] lemma bot_vsub : (⊥ : filter β) -ᵥ g = ⊥ := map₂_bot_left
@[simp] lemma vsub_bot : f -ᵥ (⊥ : filter β) = ⊥ := map₂_bot_right
@[simp] lemma vsub_eq_bot_iff : f -ᵥ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := map₂_eq_bot_iff
@[simp] lemma vsub_ne_bot_iff : (f -ᵥ g : filter α).ne_bot ↔ f.ne_bot ∧ g.ne_bot := map₂_ne_bot_iff
lemma ne_bot.vsub : ne_bot f → ne_bot g → ne_bot (f -ᵥ g) := ne_bot.map₂
@[simp] lemma le_vsub_iff : h ≤ f -ᵥ g ↔ ∀ ⦃s⦄, s ∈ f → ∀ ⦃t⦄, t ∈ g → s -ᵥ t ∈ h := le_map₂_iff
lemma vsub_le_vsub : f₁ ≤ f₂ → g₁ ≤ g₂ → f₁ -ᵥ g₁ ≤ f₂ -ᵥ g₂ := map₂_mono
lemma vsub_le_vsub_left : g₁ ≤ g₂ → f -ᵥ g₁ ≤ f -ᵥ g₂ := map₂_mono_left
lemma vsub_le_vsub_right : f₁ ≤ f₂ → f₁ -ᵥ g ≤ f₂ -ᵥ g := map₂_mono_right

end vsub

/-! ### Translation/scaling of filters -/

section smul
variables [has_scalar α β] {f f₁ f₂ : filter β} {s : set β} {a : α}

/-- `a • f` is the map of `f` under `a •` in locale `pointwise`. -/
@[to_additive filter.has_vadd_filter
"`a +ᵥ f` is the map of `f` under `a +ᵥ` in locale `pointwise`."]
protected def has_scalar_filter : has_scalar α (filter β) := ⟨λ a, map ((•) a)⟩

localized "attribute [instance] filter.has_scalar_filter filter.has_vadd_filter" in pointwise

@[simp, to_additive] lemma map_smul : map (λ b, a • b) f = a • f := rfl
@[to_additive] lemma mem_smul_filter : s ∈ a • f ↔ (•) a ⁻¹' s ∈ f := iff.rfl

@[to_additive] lemma smul_set_mem_smul_filter : s ∈ f → a • s ∈ a • f := image_mem_map
@[simp, to_additive] lemma smul_filter_bot : a • (⊥ : filter β) = ⊥ := map_bot
@[simp, to_additive] lemma smul_filter_eq_bot_iff : a • f = ⊥ ↔ f = ⊥ := map_eq_bot_iff
@[simp, to_additive] lemma smul_filter_ne_bot_iff : (a • f).ne_bot ↔ f.ne_bot := map_ne_bot_iff _
@[to_additive] lemma ne_bot.smul_filter : f.ne_bot → (a • f).ne_bot := λ h, h.map _
@[to_additive] lemma smul_filter_le_smul_filter (hf : f₁ ≤ f₂) : a • f₁ ≤ a • f₂ :=
map_mono hf

@[to_additive] instance covariant_smul_filter : covariant_class α (filter β) (•) (≤) :=
⟨λ f, map_mono⟩

end smul

open_locale pointwise

@[to_additive]
instance smul_comm_class_filter [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class α (filter β) (filter γ) :=
⟨λ a f g, map_map₂_distrib_right $ smul_comm a⟩

@[to_additive]
instance smul_comm_class_filter' [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (filter α) β (filter γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (filter α) (filter β) (filter γ) :=
⟨λ f g h, map₂_left_comm smul_comm⟩

instance is_scalar_tower [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower α β (filter γ) :=
⟨λ a b f, by simp only [←map_smul, map_map, smul_assoc]⟩

instance is_scalar_tower' [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower α (filter β) (filter γ) :=
⟨λ a f g, by { refine (map_map₂_distrib_left $ λ _ _, _).symm, exact (smul_assoc a _ _).symm }⟩

instance is_scalar_tower'' [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower (filter α) (filter β) (filter γ) :=
⟨λ f g h, map₂_assoc smul_assoc⟩

instance is_central_scalar [has_scalar α β] [has_scalar αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (filter β) :=
⟨λ a f, congr_arg (λ m, map m f) $ by exact funext (λ _, op_smul_eq_smul _ _)⟩

end filter
