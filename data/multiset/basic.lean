/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Multisets.
-/
import data.list.basic data.list.perm order.boolean_algebra algebra.functions
open list subtype nat lattice

variables {α : Type*} {β : Type*} {γ : Type*}

instance list.perm.setoid (α : Type*) : setoid (list α) :=
setoid.mk perm ⟨perm.refl, @perm.symm _, @perm.trans _⟩

def {u} multiset (α : Type u) : Type u :=
quotient (list.perm.setoid α)

namespace multiset

instance : has_coe (list α) (multiset α) := ⟨quot.mk _⟩

@[simp] theorem quot_mk_to_coe (l : list α) : @eq (multiset α) ⟦l⟧ l := rfl

@[simp] theorem quot_mk_to_coe' (l : list α) : @eq (multiset α) (quot.mk (≈) l) l := rfl

@[simp] theorem coe_eq_coe (l₁ l₂ : list α) : (l₁ : multiset α) = l₂ ↔ l₁ ~ l₂ :=
⟨quotient.exact, quot.sound⟩

instance has_decidable_eq [decidable_eq α] : decidable_eq (multiset α)
| s₁ s₂ := quotient.rec_on_subsingleton₂ s₁ s₂ $ λ l₁ l₂,
  decidable_of_iff (perm l₁ l₂) ⟨λ e, quot.sound e, quotient.exact⟩

section mem

def mem (a : α) (s : multiset α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂), propext $ mem_of_perm e)

instance : has_mem α (multiset α) := ⟨mem⟩

@[simp] lemma mem_coe {a : α} {l : list α} : a ∈ (l : multiset α) ↔ a ∈ l := iff.rfl

instance decidable_mem [h : decidable_eq α] (a : α) (s : multiset α) : decidable (a ∈ s) :=
quot.rec_on_subsingleton s $ list.decidable_mem a

end mem


/- subset -/
section subset
-- TODO(Mario): This relation is called subset in list, but for multisets
-- the `le` relation below is a more logical "subset" relation. Keep this or rename?
protected def subset (s₁ s₂ : multiset α) : Prop :=
quotient.lift_on₂ s₁ s₂ (⊆)
  (λ v₁ v₂ w₁ w₂ p₁ p₂, propext (iff.intro
    (λ s₁ a i, perm_subset p₂ (s₁ (perm_subset p₁.symm i)))
    (λ s₂ a i, perm_subset p₂.symm (s₂ (perm_subset p₁ i)))))

instance : has_subset (multiset α) := ⟨multiset.subset⟩

-- theorem subset_univ [h : fintype α] (s : multiset α) : s ⊆ univ :=
-- quot.induction_on s (λ l a i, fintype.complete a)

@[simp] theorem subset.refl (s : multiset α) : s ⊆ s :=
quot.induction_on s (λ l, by refl)

theorem subset.trans {s₁ s₂ s₃ : multiset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
quotient.induction_on₃ s₁ s₂ s₃ (λ l₁ l₂ l₃, list.subset.trans)

theorem subset_iff {s₁ s₂ : multiset α} : s₁ ⊆ s₂ ↔ (∀⦃x⦄, x ∈ s₁ → x ∈ s₂) :=
quotient.induction_on₂ s₁ s₂ $ λ l₁ l₂, iff.rfl

theorem mem_of_subset {s₁ s₂ : multiset α} {a : α} (h : s₁ ⊆ s₂) : a ∈ s₁ → a ∈ s₂ :=
λ m, subset_iff.1 h m

end subset

/- multiset order -/

protected def le (s₁ s₂ : multiset α) : Prop :=
quotient.lift_on₂ s₁ s₂ (<+~) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  propext (p₂.subperm_left.trans p₁.subperm_right)

instance : partial_order (multiset α) :=
{ le := multiset.le,
  le_refl := λ s, quot.induction_on s $ λ l, subperm.refl _,
  le_trans := λ s₁ s₂ s₃, quotient.induction_on₃ s₁ s₂ s₃ $ @subperm.trans _,
  le_antisymm := λ s₁ s₂, quotient.induction_on₂ s₁ s₂ $
    λ l₁ l₂ h₁ h₂, quot.sound (subperm.antisymm h₁ h₂) }

theorem subset_of_le {s₁ s₂ : multiset α} : s₁ ≤ s₂ → s₁ ⊆ s₂ :=
quotient.induction_on₂ s₁ s₂ $ λ l₁ l₂, subset_of_subperm

theorem mem_of_le {s₁ s₂ : multiset α} {a : α} (h : s₁ ≤ s₂) : a ∈ s₁ → a ∈ s₂ :=
mem_of_subset (subset_of_le h)

@[simp] theorem coe_le {l₁ l₂ : list α} : (l₁ : multiset α) ≤ l₂ ↔ l₁ <+~ l₂ := iff.rfl

@[elab_as_eliminator] theorem le_induction_on {C : multiset α → multiset α → Prop}
  {s₁ s₂ : multiset α} (h : s₁ ≤ s₂)
  (H : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → C l₁ l₂) : C s₁ s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂ ⟨l, p, s⟩,
  (show ⟦l⟧ = ⟦l₁⟧, from quot.sound p) ▸ H s) h

/- cardinality -/
def card (s : multiset α) : ℕ :=
quot.lift_on s length $ λ l₁ l₂, perm_length

@[simp] theorem coe_card (l : list α) : card (l : multiset α) = length l := rfl

theorem card_le_of_le {s t : multiset α} (h : s ≤ t) : card s ≤ card t :=
le_induction_on h $ λ l₁ l₂, length_le_of_sublist

theorem eq_of_le_of_card_le {s t : multiset α} (h : s ≤ t) (h₂ : card t ≤ card s) : s = t :=
le_induction_on h (λ l₁ l₂ s h₂, congr_arg coe $
  eq_of_sublist_of_length_eq s (le_antisymm (length_le_of_sublist s) h₂)) h₂

theorem card_lt_of_lt {s t : multiset α} (h : s < t) : card s < card t :=
lt_of_not_ge $ λ h₂, ne_of_lt h $ eq_of_le_of_card_le (le_of_lt h) h₂

/- empty multilist -/
protected def zero : multiset α := @nil α

instance : has_zero (multiset α)   := ⟨multiset.zero⟩
instance : has_emptyc (multiset α) := ⟨0⟩
instance : has_bot (multiset α)    := ⟨0⟩
instance : inhabited (multiset α)  := ⟨0⟩

@[simp] theorem coe_nil_eq_zero : (@nil α : multiset α) = 0 := rfl

@[simp] theorem card_zero : @card α 0 = 0 := rfl

theorem zero_le (s : multiset α) : 0 ≤ s :=
quot.induction_on s $ λ l, subperm_of_sublist $ nil_sublist l

theorem eq_zero_of_le_zero (s : multiset α) (h : s ≤ 0) : s = 0 :=
le_antisymm h (zero_le _)

@[simp] theorem not_mem_empty (a : α) : a ∉ (∅ : multiset α) := id

theorem empty_subset (s : multiset α) : ∅ ⊆ s := subset_of_le (zero_le s)

theorem eq_empty_of_forall_not_mem {s : multiset α} : (∀x, x ∉ s) → s = ∅ :=
quot.induction_on s $ λ l H, by rw eq_nil_of_forall_not_mem H; refl

theorem eq_empty_of_subset_empty {s : multiset α} (h : s ⊆ ∅) : s = ∅ :=
eq_empty_of_forall_not_mem (subset_iff.1 h)

theorem subset_empty_iff {s : multiset α} : s ⊆ ∅ ↔ s = ∅ :=
⟨eq_empty_of_subset_empty, λ xeq, xeq.symm ▸ subset.refl ∅⟩

theorem exists_mem_of_ne_empty {s : multiset α} : s ≠ ∅ → ∃ a : α, a ∈ s :=
quot.induction_on s $ assume l hl,
  match l, hl with
  | [] := assume h, false.elim $ h rfl
  | (a :: l) := assume _, ⟨a, by simp⟩
  end

/- cons -/
def cons (a : α) (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (a :: l : multiset α))
  (λ l₁ l₂ p, quot.sound ((perm_cons a).2 p))

notation a :: b := cons a b

@[simp] theorem cons_coe (a : α) (l : list α) :
  (a::l : multiset α) = (a::l : list α) := rfl

@[simp] theorem singleton_coe (a : α) : (a::0 : multiset α) = ([a] : list α) := rfl

@[simp] theorem cons_inj_left {a b : α} (s : multiset α) :
  a::s = b::s ↔ a = b :=
⟨quot.induction_on s $ λ l e,
  have [a] ++ l ~ [b] ++ l, from quotient.exact e,
  eq_singleton_of_perm $ (perm_app_right_iff _).1 this, congr_arg _⟩

@[simp] theorem cons_inj_right (a : α) {s t : multiset α} :
  a::s = a::t ↔ s = t :=
quotient.induction_on₂ s t $ λ l₁ l₂, by simp [perm_cons]

@[simp] theorem mem_cons {a b : α} {s : multiset α} : a ∈ b :: s ↔ a = b ∨ a ∈ s :=
quot.induction_on s $ λ l, iff.rfl

@[simp] theorem mem_cons_self (a : α) (s : multiset α) : a ∈ a :: s :=
mem_cons.2 (or.inl rfl)

@[recursor 5] protected theorem induction {p : multiset α → Prop}
  (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a :: s)) (s) : p s :=
quot.induction_on s $ λ l, by induction l; [exact h₁, exact h₂ ih_1]

@[elab_as_eliminator] protected theorem induction_on {p : multiset α → Prop}
  (s : multiset α) (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a :: s)) : p s :=
multiset.induction h₁ h₂ s

theorem exists_cons_of_mem {s : multiset α} {a : α} : a ∈ s → ∃ t, s = a :: t :=
quot.induction_on s $ λ l (h : a ∈ l),
let ⟨l₁, l₂, e⟩ := mem_split h in
e.symm ▸ ⟨(l₁++l₂ : list α), quot.sound perm_middle⟩

theorem lt_cons_self (s : multiset α) (a : α) : s < a :: s :=
quot.induction_on s $ λ l,
suffices l <+~ a :: l ∧ ¬l ~ a :: l,
  by simpa [lt_iff_le_and_ne],
⟨subperm_of_sublist (sublist_cons _ _),
 λ p, ne_of_lt (lt_succ_self (length l)) (perm_length p)⟩

theorem le_cons_self (s : multiset α) (a : α) : s ≤ a :: s :=
le_of_lt $ lt_cons_self _ _

theorem cons_le_cons_iff (a : α) {s t : multiset α} : a :: s ≤ a :: t ↔ s ≤ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, subperm_cons a

theorem cons_le_cons (a : α) {s t : multiset α} : s ≤ t → a :: s ≤ a :: t :=
(cons_le_cons_iff a).2

theorem lt_iff_cons_le {s t : multiset α} : s < t ↔ ∃ a, a :: s ≤ t :=
⟨quotient.induction_on₂ s t $ λ l₁ l₂ h,
  subperm.exists_of_length_lt (le_of_lt h) (card_lt_of_lt h),
λ ⟨a, h⟩, lt_of_lt_of_le (lt_cons_self _ _) h⟩

theorem cons_swap (a b : α) (s : multiset α) : a :: b :: s = b :: a :: s :=
quot.induction_on s $ λ l, quotient.sound $ perm.swap _ _ _

theorem card_cons (a : α) (s : multiset α) : card (a :: s) = card s + 1 :=
quot.induction_on s $ λ l, rfl

/- add -/
protected def add (s₁ s₂ : multiset α) : multiset α := 
quotient.lift_on₂ s₁ s₂ (λ l₁ l₂, ((l₁ ++ l₂ : list α) : multiset α)) $
  λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound $ perm_app p₁ p₂

instance : has_add (multiset α) := ⟨multiset.add⟩

@[simp] theorem coe_add (s t : list α) : (s + t : multiset α) = (s ++ t : list α) := rfl

protected theorem add_comm (s t : multiset α) : s + t = t + s :=
quotient.induction_on₂ s t $ λ l₁ l₂, quot.sound perm_app_comm

protected theorem zero_add (s : multiset α) : 0 + s = s :=
quot.induction_on s $ λ l, rfl

theorem singleton_add (a : α) (s : multiset α) : ↑[a] + s = a::s := rfl

protected theorem add_le_add_left (s) {t u : multiset α} : s + t ≤ s + u ↔ t ≤ u :=
quotient.induction_on₃ s t u $ λ l₁ l₂ l₃, subperm_app_left _

protected theorem add_left_cancel (s) {t u : multiset α} (h : s + t = s + u) : t = u :=
le_antisymm ((multiset.add_le_add_left _).1 (le_of_eq h))
  ((multiset.add_le_add_left _).1 (le_of_eq h.symm))

instance : ordered_cancel_comm_monoid (multiset α) :=
{ @multiset.partial_order α with
  zero                  := 0,
  add                   := (+),
  add_comm              := multiset.add_comm,
  add_assoc             := λ s₁ s₂ s₃, quotient.induction_on₃ s₁ s₂ s₃ $ λ l₁ l₂ l₃,
    congr_arg coe $ append_assoc l₁ l₂ l₃,
  zero_add              := multiset.zero_add,
  add_zero              := λ s, by rw [multiset.add_comm, multiset.zero_add],
  add_left_cancel       := multiset.add_left_cancel,
  add_right_cancel      := λ s₁ s₂ s₃ h, multiset.add_left_cancel s₂ $
    by simpa [multiset.add_comm] using h,
  add_le_add_left       := λ s₁ s₂ h s₃, (multiset.add_le_add_left _).2 h,
  le_of_add_le_add_left := λ s₁ s₂ s₃, (multiset.add_le_add_left _).1 }

theorem add_cons (a : α) (s t : multiset α) : a :: s + t = a :: (s + t) :=
by rw [← singleton_add, ← singleton_add, add_assoc]

theorem le_add_right (s t : multiset α) : s ≤ s + t :=
by simpa using add_le_add_left (zero_le t) s

theorem le_add_left (s t : multiset α) : s ≤ t + s :=
by simpa using add_le_add_right (zero_le t) s

theorem card_add (s t : multiset α) : card (s + t) = card s + card t :=
quotient.induction_on₂ s t length_append

theorem le_iff_exists_add {s t : multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
⟨λ h, le_induction_on h $ λ l₁ l₂ s,
  let ⟨l, p⟩ := exists_perm_append_of_sublist s in ⟨l, quot.sound p⟩,
λ⟨u, e⟩, e.symm ▸ le_add_right s u⟩

/- erase -/
section erase
variables [decidable_eq α] {s t : multiset α} {a b : α}

def erase (s : multiset α) (a : α) : multiset α :=
quot.lift_on s (λ l, (l.erase a : multiset α))
  (λ l₁ l₂ p, quot.sound (erase_perm_erase a p))

@[simp] theorem coe_erase (l : list α) (a : α) :
  erase (l : multiset α) a = l.erase a := rfl

@[simp] theorem erase_zero (a : α) : (0 : multiset α).erase a = 0 := rfl

@[simp] theorem erase_cons_head (a : α) (s : multiset α) : (a :: s).erase a = s :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_head a l

@[simp] theorem erase_cons_tail {a b : α} (s : multiset α) (h : b ≠ a) : (b::s).erase a = b :: s.erase a :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_tail l h

@[simp] theorem erase_of_not_mem {a : α} {s : multiset α} : a ∉ s → s.erase a = s :=
quot.induction_on s $ λ l h, congr_arg coe $ erase_of_not_mem h

theorem eq_cons_erase {a : α} {s : multiset α} : a ∈ s → s = a :: s.erase a :=
quot.induction_on s $ λ l h, quot.sound $ perm_erase h

@[simp] theorem card_erase_of_mem {a : α} {s : multiset α} : a ∈ s → card (s.erase a) = pred (card s) :=
quot.induction_on s $ λ l, length_erase_of_mem

theorem erase_add_left_pos {a : α} {s : multiset α} (t) : a ∈ s → (s + t).erase a = s.erase a + t :=
quotient.induction_on₂ s t $ λ l₁ l₂ h, congr_arg coe $ erase_append_left l₂ h

theorem erase_add_right_pos {a : α} (s) {t : multiset α} (h : a ∈ t) : (s + t).erase a = s + t.erase a :=
by rw [add_comm, erase_add_left_pos s h, add_comm]

theorem erase_add_right_neg {a : α} {s : multiset α} (t) : a ∉ s → (s + t).erase a = s + t.erase a :=
quotient.induction_on₂ s t $ λ l₁ l₂ h, congr_arg coe $ erase_append_right l₂ h

theorem erase_add_left_neg {a : α} (s) {t : multiset α} (h : a ∉ t) : (s + t).erase a = s.erase a + t :=
by rw [add_comm, erase_add_right_neg s h, add_comm]

theorem erase_le (a : α) (s : multiset α) : s.erase a ≤ s :=
quot.induction_on s $ λ l, subperm_of_sublist (erase_sublist a l)

theorem erase_subset (a : α) (s : multiset α) : s.erase a ⊆ s :=
subset_of_le (erase_le a s)

theorem mem_erase_of_ne_of_mem {a b : α} {s : multiset α} (ab : a ≠ b) : a ∈ s → a ∈ s.erase b :=
quot.induction_on s $ λ l al, list.mem_erase_of_ne_of_mem ab al

theorem mem_of_mem_erase {a b : α} {s : multiset α} : a ∈ s.erase b → a ∈ s :=
mem_of_subset (erase_subset _ _)

theorem erase_comm (s : multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
quot.induction_on s $ λ l, congr_arg coe $ l.erase_comm a b

end erase

@[simp] theorem coe_reverse (l : list α) : (reverse l : multiset α) = l :=
quot.sound $ reverse_perm _ 

/- map -/
def map (f : α → β) (s : multiset α) : multiset β :=
quot.lift_on s (λ l : list α, (l.map f : multiset β))
  (λ l₁ l₂ p, quot.sound (perm_map f p))

@[simp] theorem mem_map {f : α → β} {b : β} {s : multiset α} :
  b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
quot.induction_on s $ λ l, mem_map

theorem mem_map_of_mem (f : α → β) {a : α} {s : multiset α} (h : a ∈ s) : f a ∈ map f s :=
mem_map.2 ⟨_, h, rfl⟩

@[simp] theorem mem_map_of_inj {f : α → β} (H : function.injective f) {a : α} {s : multiset α} :
  f a ∈ map f s ↔ a ∈ s :=
quot.induction_on s $ λ l, mem_map_of_inj H

/- fold -/
def foldl (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldl f b l)
  (λ l₁ l₂ p, foldl_eq_of_perm H p b)

def foldr (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldr f b l)
  (λ l₁ l₂ p, foldr_eq_of_perm H p b)

theorem coe_foldr (f : α → β → β) (H : left_commutative f) (b : β) (l : list α) :
  foldr f H b l = l.foldr f b := rfl

theorem coe_foldl (f : β → α → β) (H : right_commutative f) (b : β) (l : list α) :
  foldl f H b l = l.foldl f b := rfl

theorem coe_foldr_swap (f : α → β → β) (H : left_commutative f) (b : β) (l : list α) :
  foldr f H b l = l.foldl (λ x y, f y x) b :=
(congr_arg (foldr f H b) (coe_reverse l)).symm.trans $ foldr_reverse _ _ _

theorem foldr_swap (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) :
  foldr f H b s = foldl (λ x y, f y x) (λ x y z, (H _ _ _).symm) b s :=
quot.induction_on s $ λ l, coe_foldr_swap _ _ _ _

theorem foldl_swap (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) :
  foldl f H b s = foldr (λ x y, f y x) (λ x y z, (H _ _ _).symm) b s :=
(foldr_swap _ _ _ _).symm

def prod [comm_monoid α] : multiset α → α :=
foldr (*) (λ x y z, by simp) 1

def prod_eq_foldr [comm_monoid α] (s : multiset α) :
  prod s = foldr (*) (λ x y z, by simp) 1 s := rfl

def prod_eq_foldl [comm_monoid α] (s : multiset α) :
  prod s = foldl (*) (λ x y z, by simp) 1 s :=
(foldr_swap _ _ _ _).trans (by simp)

def sum [add_comm_monoid α] : multiset α → α :=
foldr (+) (λ x y z, by simp) 0

/- join -/
def join : multiset (multiset α) → multiset α := sum

theorem coe_join : ∀ L : list (list α),
  join (L.map (@coe _ (multiset α) _) : multiset (multiset α)) = L.join
| []       := rfl
| (l :: L) := congr_arg (λ s : multiset α, ↑l + s) (coe_join L)

/- subtraction -/
section sub
variables [decidable_eq α] {s t : multiset α} {a b : α}

protected def sub (s t : multiset α) : multiset α :=
quotient.lift_on₂ s t (λ l₁ l₂, (l₁.diff l₂ : multiset α)) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  quot.sound $ (perm_diff_left _ p₁).trans (perm_diff_right _ p₂)

instance : has_sub (multiset α) := ⟨multiset.sub⟩

@[simp] theorem coe_sub (s t : list α) : (s - t : multiset α) = (s.diff t : list α) := rfl

theorem sub_eq_fold_erase (s t : multiset α) : s - t = foldl erase erase_comm s t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
show ↑(l₁.diff l₂) = foldl erase erase_comm ↑l₁ ↑l₂,
by rw diff_eq_foldl l₁ l₂; exact foldl_hom _ _ _ _ (λ x y, rfl) _

@[simp] theorem sub_zero (s : multiset α) : s - 0 = s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem sub_cons (a : α) (s t : multiset α) : s - a::t = s.erase a - t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ diff_cons _ _ _

theorem add_sub_of_le {s t : multiset α} (h : s ≤ t) : s + (t - s) = t :=
begin
  revert t,
  refine multiset.induction_on s (by simp) (λ a s IH t h, _),
  have := eq_cons_erase (mem_of_le h (mem_cons_self _ _)),
  rw [add_cons, sub_cons, IH, ← this],
  exact (cons_le_cons_iff a).1 (this ▸ h)
end

theorem sub_add_cancel {s t : multiset α} (h : s ≥ t) : s - t + t = s :=
by rw [add_comm, add_sub_of_le h]

end sub

section singleton
variables [decidable_eq α] {a b : α} {s : multiset α}

@[simp] theorem mem_singleton : b ∈ a::0 ↔ b = a :=
by simp

theorem mem_singleton_self : a ∈ (a::0 : multiset α) := mem_cons_self _ _

theorem singleton_inj : a::0 = b::0 ↔ a = b := cons_inj_left _

@[simp] theorem singleton_ne_zero : a::0 ≠ 0 :=
ne_of_gt (lt_cons_self _ _)

end singleton

/-
/- union -/
section union
variable [decidable_eq α]

protected def union (s₁ s₂ : multiset α) : multiset α :=
quotient.lift_on₂ s₁ s₂ (λ l₁ l₂, (↑(l₁ ∪ l₂) : multiset α))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm_union p₁ p₂))

instance : has_union (multiset α) := ⟨multiset.union⟩

@[simp] theorem mem_union {a : α} {s₁ s₂ : multiset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂, list.mem_union)

theorem mem_union_left {a : α} {s₁ : multiset α} (s₂ : multiset α) : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
by simp {contextual := tt}

theorem mem_union_right {a : α} {s₂ : multiset α} (s₁ : multiset α) : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
by simp {contextual := tt}

theorem mem_or_mem_of_mem_union {a : α} {s₁ s₂ : multiset α} : a ∈ s₁ ∪ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
mem_union.1

theorem union_subset {s₁ s₂ s₃ : multiset α} : s₁ ⊆ s₃ → s₂ ⊆ s₃ → s₁ ∪ s₂ ⊆ s₃ :=
by simp [subset_iff] {contextual:=tt}; finish

theorem subset_union_left {s₁ s₂ : multiset α} : s₁ ⊆ s₁ ∪ s₂ :=
subset_iff.mpr $ assume x, mem_union_left _

theorem subset_union_right {s₁ s₂ : multiset α} : s₂ ⊆ s₁ ∪ s₂ :=
subset_iff.mpr $ assume x, mem_union_right _

@[simp] theorem union_assoc (s₁ s₂ s₃ : multiset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
_

instance : is_associative (multiset α) (∪) := ⟨union_assoc⟩

@[simp] theorem union_idempotent (s : multiset α) : s ∪ s = s :=
ext $ by simp

instance : is_idempotent (multiset α) (∪) := ⟨union_idempotent⟩

theorem union_left_comm (s₁ s₂ s₃ : multiset α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
ext $ by simp

theorem union_right_comm (s₁ s₂ s₃ : multiset α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
ext $ by simp

@[simp] theorem union_self (s : multiset α) : s ∪ s = s :=
ext $ by simp

@[simp] theorem union_empty (s : multiset α) : s ∪ ∅ = s :=
ext $ by simp

@[simp] theorem empty_union (s : multiset α) : ∅ ∪ s = s :=
ext $ by simp

theorem insert_eq (a : α) (s : multiset α) : insert a s = {a} ∪ s :=
ext $ by simp

@[simp] theorem insert_union (a : α) (s t : multiset α) : insert a s ∪ t = insert a (s ∪ t) :=
ext $ by simp

@[simp] theorem union_insert (a : α) (s t : multiset α) : s ∪ insert a t = insert a (s ∪ t) :=
ext $ by simp

end union

/- inter -/
section inter
variable [decidable_eq α]

protected def inter (s₁ s₂ : multiset α) : multiset α :=
quotient.lift_on₂ s₁ s₂
  (λ l₁ l₂, to_multiset_of_nodup (list.inter l₁.1 l₂.1) (nodup_inter_of_nodup _ l₁.2))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm_inter p₁ p₂))

instance : has_inter (multiset α) := ⟨multiset.inter⟩

@[simp] theorem mem_inter (a : α) (s₁ s₂ : multiset α) : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂, mem_inter)

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : multiset α} : a ∈ s₁ ∩ s₂ → a ∈ s₁ :=
by simp {contextual := tt}

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : multiset α} : a ∈ s₁ ∩ s₂ → a ∈ s₂ :=
by simp {contextual := tt}

theorem mem_inter_of_mem {a : α} {s₁ s₂ : multiset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
by simp {contextual := tt}

theorem inter_subset_left {s₁ s₂ : multiset α} : s₁ ∩ s₂ ⊆ s₁ :=
by simp [subset_iff] {contextual:=tt}; finish

theorem inter_subset_right {s₁ s₂ : multiset α} : s₁ ∩ s₂ ⊆ s₂ :=
by simp [subset_iff] {contextual:=tt}; finish

theorem subset_inter {s₁ s₂ s₃ : multiset α} : s₁ ⊆ s₂ → s₁ ⊆ s₃ → s₁ ⊆ s₂ ∩ s₃ :=
by simp [subset_iff] {contextual:=tt}; finish

@[simp] theorem inter_comm (s₁ s₂ : multiset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext $ by simp

@[simp] theorem inter_assoc (s₁ s₂ s₃ : multiset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext $ by simp

@[simp] theorem inter_left_comm (s₁ s₂ s₃ : multiset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
ext $ by simp

@[simp] theorem inter_right_comm (s₁ s₂ s₃ : multiset α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
ext $ by simp

@[simp] theorem inter_self (s : multiset α) : s ∩ s = s :=
ext $ by simp

@[simp] theorem inter_empty (s : multiset α) : s ∩ ∅ = ∅ :=
ext $ by simp

@[simp] theorem empty_inter (s : multiset α) : ∅ ∩ s = ∅ :=
ext $ by simp

@[simp] theorem insert_inter_of_mem {s₁ s₂ : multiset α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
ext $ by simp; intro x; constructor; finish

@[simp] theorem inter_insert_of_mem {s₁ s₂ : multiset α} {a : α} (h : a ∈ s₁) :
  s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp] theorem insert_inter_of_not_mem {s₁ s₂ : multiset α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
ext $ assume a', by by_cases a' = a with h'; simp [mem_inter, mem_insert, h, h']

@[simp] theorem inter_insert_of_not_mem {s₁ s₂ : multiset α} {a : α} (h : a ∉ s₁) :
  s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp] theorem singleton_inter_of_mem {a : α} {s : multiset α} : a ∈ s → {a} ∩ s = {a} :=
show a ∈ s → insert a ∅ ∩ s = insert a ∅, by simp {contextual := tt}

@[simp] theorem singleton_inter_of_not_mem {a : α} {s : multiset α} : a ∉ s → {a} ∩ s = ∅ :=
show a ∉ s → insert a ∅ ∩ s = ∅, by simp {contextual := tt}

@[simp] theorem inter_singleton_of_mem {a : α} {s : multiset α} (h : a ∈ s) : s ∩ {a} = {a} :=
by rw [inter_comm, singleton_inter_of_mem h]

@[simp] theorem inter_singleton_of_not_mem {a : α} {s : multiset α} (h : a ∉ s) : s ∩ {a} = ∅ :=
by rw [inter_comm, singleton_inter_of_not_mem h]

end inter

section lattice

instance [decidable_eq α] : lattice (multiset α) :=
{ le := (⊆),
  le_refl := subset.refl,
  le_trans := assume a b c, subset.trans,
  le_antisymm := assume a b, subset.antisymm,
  sup := (∪),
  sup_le := assume a b c, union_subset,
  le_sup_left := assume a b, subset_union_left,
  le_sup_right := assume a b, subset_union_right,
  inf := (∩),
  le_inf := assume a b c, subset_inter,
  inf_le_left := assume a b, inter_subset_left,
  inf_le_right := assume a b, inter_subset_right }

instance [decidable_eq α] : semilattice_inf_bot (multiset α) :=
{ multiset.lattice.lattice with
  bot := ∅,
  bot_le := assume a, empty_subset }

instance [decidable_eq α] : distrib_lattice (multiset α) :=
{ multiset.lattice.lattice with
  le_sup_inf := assume a b c, show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c,
    by simp [subset_iff, and_imp, or_imp_distrib] {contextual:=tt} }

end lattice

/- distributivity laws -/
section inter
variable [decidable_eq α]

theorem inter_distrib_left (s t u : multiset α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext $ by simp [mem_inter, mem_union]; intro; split; finish

theorem inter_distrib_right (s t u : multiset α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext $ by simp [mem_inter, mem_union]; intro; split; finish

theorem union_distrib_left (s t u : multiset α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext $ by simp [mem_inter, mem_union]; intro; split; finish

theorem union_distrib_right (s t u : multiset α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext $ by simp [mem_inter, mem_union]; intro; split; finish

end inter

/- erase -/
section erase
variables [decidable_eq α] {a b c : α} {s t : multiset α}

def erase (a : α) (s : multiset α) : multiset α :=
quot.lift_on s
  (λ l, to_multiset_of_nodup (l.1.erase a) (nodup_erase_of_nodup a l.2))
  (λ (l₁ l₂ : nodup_list α) (p : l₁ ~ l₂), quot.sound (erase_perm_erase a p))

@[simp] theorem mem_erase : a ∈ erase b s ↔ a ≠ b ∧ a ∈ s :=
multiset.induction_on_to_multiset s $ λ l hl, mem_erase_iff_of_nodup hl

theorem not_mem_erase : a ∉ erase a s := by simp

@[simp] theorem erase_empty : erase a ∅ = ∅ := rfl

theorem ne_of_mem_erase : b ∈ erase a s → b ≠ a := by simp {contextual:=tt}

theorem mem_of_mem_erase : b ∈ erase a s → b ∈ s := by simp {contextual:=tt}

theorem mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase b s := by simp {contextual:=tt}

theorem erase_insert (h : a ∉ s) : erase a (insert a s) = s :=
ext $ assume x, by simp; constructor; finish

theorem insert_erase (h : a ∈ s) : insert a (erase a s) = s :=
ext $ assume x, by simp; constructor; finish

theorem erase_subset_erase (h : s ⊆ t) : erase a s ⊆ erase a t :=
subset_iff.2 $ assume x, by simp [-and_imp]; exact and.imp_right (mem_of_subset_of_mem h)

theorem erase_subset : erase a s ⊆ s :=
subset_iff.2 $ assume x, by simp {contextual:=tt}

theorem erase_eq_of_not_mem (h : a ∉ s) : erase a s = s :=
ext $ assume b, by by_cases b = a; simp *

theorem erase_insert_subset : erase a (insert a s) ⊆ s :=
by by_cases a ∈ s; simp [h, erase_subset, erase_insert, subset.refl]

theorem erase_subset_of_subset_insert (h : s ⊆ insert a t) : erase a s ⊆ t :=
subset.trans (erase_subset_erase h) erase_insert_subset

theorem insert_erase_subset : s ⊆ insert a (erase a s) :=
decidable.by_cases
  (λ ains : a ∈ s, by rw [insert_erase ains]; apply subset.refl)
  (λ nains : a ∉ s, by rw[erase_eq_of_not_mem nains]; apply subset_insert)

theorem subset_insert_of_erase_subset (h : erase a s ⊆ t) : s ⊆ insert a t :=
subset.trans insert_erase_subset (insert_subset_insert h)

theorem subset_insert_iff (s t : multiset α) (a : α) : s ⊆ insert a t ↔ erase a s ⊆ t :=
iff.intro erase_subset_of_subset_insert subset_insert_of_erase_subset

end erase

section filter
variables [decidable_eq α] {p : α → Prop} [decidable_pred p] {s s₁ s₂ : multiset α} {a : α}

protected def filter (p : α → Prop) [decidable_pred p] (s : multiset α) : multiset α :=
quotient.lift_on s
  (λl, to_multiset_of_nodup (l.val.filter p) $ nodup_filter _ l.property)
  (assume l₁ l₂ (h : perm l₁.val l₂.val), quot.sound $ perm_filter _ h)

@[simp] theorem mem_filter : a ∈ s.filter p ↔ (a ∈ s ∧ p a) :=
multiset.induction_on_to_multiset s $ λl₁ h₁, list.mem_filter

theorem filter_subset : s.filter p ⊆ s := by simp [subset_iff] {contextual := tt}

theorem filter_union : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
ext $ assume a, by simp [and_or_distrib_left]

theorem filter_filter {p' : α → Prop} [decidable_pred p'] :
  (s.filter p).filter p' = s.filter (λa, p a ∧ p' a) :=
ext $ assume a, by simp

@[simp] theorem filter_false {h : decidable_pred $ λa:α, false} :
  @multiset.filter α _ (λa:α, false) h s = ∅ :=
ext $ assume a, by simp

theorem filter_union_filter_neg_eq : s.filter p ∪ s.filter (λa, ¬ p a) = s :=
ext $ assume a, by by_cases p a; simp [iff_iff_implies_and_implies, *] {contextual := tt}

theorem filter_inter_filter_neg_eq : s.filter p ∩ s.filter (λa, ¬ p a) = ∅ :=
ext $ assume a, by by_cases p a; simp * {contextual := tt}

end filter

section sdiff
variables [decidable_eq α] {a : α} {s₁ s₂ t₁ t₂ : multiset α}

instance : has_sdiff (multiset α) := ⟨λs₁ s₂, s₁.filter (λa, a ∉ s₂)⟩

@[simp] theorem mem_sdiff_iff : a ∈ s₁ \ s₂ ↔ (a ∈ s₁ ∧ a ∉ s₂) := mem_filter

lemma sdiff_union_of_subset (h : s₁ ⊆ s₂) : (s₂ \ s₁) ∪ s₁ = s₂ :=
ext $ assume a,
  by rw [subset_iff] at h;
     by_cases a ∈ s₁; simp [iff_iff_implies_and_implies, *] {contextual := tt}

lemma sdiff_inter_self : (s₂ \ s₁) ∩ s₁ = ∅ :=
ext $ by simp {contextual := tt}

lemma sdiff_subset_sdiff : t₁ ⊆ t₂ → s₂ ⊆ s₁ → t₁ \ s₁ ⊆ t₂ \ s₂ :=
begin
  simp [subset_iff, mem_sdiff_iff] {contextual := tt},
  exact assume h₁ h₂ a _ ha₁ ha₂, ha₁ $ h₂ _ ha₂
end

end sdiff

/- range -/
section range
variables {n m l : ℕ}

def range (n : ℕ) : multiset ℕ :=
to_multiset_of_nodup (list.range n) (nodup_range n)

@[simp] theorem mem_range : m ∈ range n ↔ m < n :=
list.mem_range

@[simp] theorem range_zero : range 0 = ∅ := rfl

@[simp] theorem range_succ : range (succ n) = insert n (range n) :=
ext $ by simp [mem_insert, le_iff_lt_or_eq, lt_succ_iff]

@[simp] theorem not_mem_range_self : n ∉ range n :=
not_mem_range_self

@[simp] theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m :=
range_subset

theorem exists_nat_subset_range {s : multiset ℕ} : ∃n : ℕ, s ⊆ range n :=
s.induction_on ⟨0, by simp⟩ $
  assume a s ha ⟨n, hn⟩,
  ⟨max (a + 1) n, subset_iff.mpr $ assume x,
    begin
      simp [subset_iff, mem_range] at hn,
      simp [or_imp_distrib, mem_range, lt_max_iff, hn] {contextual := tt},
      exact assume _, or.inr (lt_succ_self a)
    end⟩

end range

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : multiset α) ∧ p x) ↔ false :=
⟨λ⟨x, hx⟩, not_mem_empty (hx.left), false.elim⟩

theorem exists_mem_insert [d : decidable_eq α]
    (a : α) (s : multiset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ (∃ x, x ∈ s ∧ p x) :=
iff.intro
  (λ H,
    let ⟨x,H1,H2⟩ := H in
    or.elim (mem_insert.mp H1)
      (λ l, or.inl (eq.subst l H2))
      (λ r, or.inr ⟨x, ⟨r, H2⟩⟩))
  (λ H,
    or.elim H
      (λ l, ⟨a, ⟨mem_insert_self, l⟩⟩)
      (λ r, let ⟨x,H2,H3⟩ := r in ⟨x, ⟨mem_insert_of_mem H2, H3⟩⟩))

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : multiset α) → p x) ↔ true :=
iff.intro (λ H, trivial) (λ H x H', absurd H' not_mem_empty)

theorem forall_mem_insert [d : decidable_eq α]
    (a : α) (s : multiset α) (p : α → Prop) :
  (∀ x, x ∈ insert a s → p x) ↔ p a ∧ (∀ x, x ∈ s → p x) :=
by simp [or_imp_distrib, forall_and_distrib]

section image
variables (f : α → β) (s s₁ s₂ : multiset α) [decidable_eq β]

protected def image : multiset β :=
quot.lift_on s (λl, to_multiset $ l.val.map f) $ assume ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ (h : perm l₁ l₂),
  quotient.sound $ perm_erase_dup_of_perm $ perm_map _ $ h

@[simp] lemma image_empty {f : α → β} : (∅ : multiset α).image f = ∅ := rfl

variables {f s s₁ s₂} {b : β} [decidable_eq α]

lemma mem_image_iff : b ∈ s.image f ↔ (∃a∈s, f a = b) :=
multiset.induction_on_to_multiset s $ assume l h,
  show b ∈ to_multiset (l.map f) ↔ _, by simp [mem_to_multiset]

lemma erase_dup_map_erase_dup_eq {f : α → β} :
  ∀{l : list α}, erase_dup (map f (erase_dup l)) = (erase_dup $ map f l)
| [] := by simp
| (x :: xs) :=
  have f x ∈ map f (erase_dup xs) ↔ f x ∈ map f xs, by simp,
  by by_cases x ∈ xs; by_cases f x ∈ map f xs; simp * at *

lemma image_to_multiset {l : list α} : (to_multiset l).image f = to_multiset (l.map f) :=
quot.sound $ show perm (erase_dup $ map f $ erase_dup l) (erase_dup $ map f l),
  by rw [erase_dup_map_erase_dup_eq]

lemma image_to_multiset_of_nodup {l : list α} (hl : nodup l) (h : ∀x∈l, ∀y∈l, f x = f y → x = y) :
  (to_multiset_of_nodup l hl).image f = to_multiset_of_nodup (l.map f) (nodup_map_on h hl) :=
quot.sound $ show perm (erase_dup (map f l)) (l.map f),
  by rw [erase_dup_eq_self.2 (nodup_map_on h hl)]

lemma image_id : s.image id = s :=
quot.induction_on s $ assume ⟨l, hl⟩, show to_multiset (l.map id) = to_multiset_of_nodup l hl,
  by rw [map_id, to_multiset_eq_of_nodup]

lemma image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
quot.induction_on s $ assume ⟨l, hl⟩,
  show ((to_multiset_of_nodup l hl).image f).image g = (to_multiset_of_nodup l hl).image (g ∘ f),
    by simp [to_multiset_eq_of_nodup, image_to_multiset]

lemma image_subset_image : s₁ ⊆ s₂ → s₁.image f ⊆ s₂.image f :=
by simp [subset_iff, mem_image_iff] {contextual:=tt};
from assume h b a h_eq ha, ⟨a, h_eq, h _ ha⟩

lemma image_filter {p : β → Prop} [decidable_pred p] :
  (s.image f).filter p = (s.filter (p ∘ f)).image f :=
ext $ assume b, by simp [mem_image_iff]; exact iff.intro
  (assume ⟨hb, ⟨a, h_eq, ha⟩⟩, ⟨a, h_eq, show p (f a), from h_eq.symm ▸ hb, ha⟩)
  (assume ⟨a, h_eq, ha, has⟩, ⟨h_eq ▸ ha, a, h_eq, has⟩)

lemma image_union {f : α → β} : (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f  :=
ext $ assume b, by simp [mem_image_iff, and_or_distrib_left, exists_or_distrib]

lemma image_inter (hf : ∀x y, f x = f y → x = y) : (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
ext $ assume b,
  by simp [mem_image_iff, iff_def];
  from and.intro
    (assume x x_eq hx y y_eq hy,
      have y = x, from hf _ _ $ by simp *,
      ⟨x, x_eq, hx, this ▸ hy⟩)
    (assume x x_eq h₁ h₂, ⟨⟨x, x_eq, h₁⟩, ⟨x, x_eq, h₂⟩⟩)

@[simp] lemma image_singleton {f : α → β} {a : α} : ({a}: multiset α).image f = {f a} :=
ext $ by simp [mem_image_iff, and_or_distrib_left, exists_or_distrib, iff_def] {contextual := tt}

@[simp] lemma image_insert {f : α → β} {s : multiset α} {a : α} :
  (insert a s).image f = insert (f a) (s.image f) :=
by simp [insert_eq, image_union]

@[simp] lemma image_eq_empty_iff : s.image f = ∅ ↔ s = ∅ :=
iff.intro
  (assume h,
    have ∀a, a ∉ s,
      from assume a ha,
      have f a ∈ s.image f, from mem_image_iff.mpr ⟨a, ha, rfl⟩,
      by simp * at *,
    ext $ by simp *)
  (assume h, by simp *)

end image

section card
variables [decidable_eq α] {a : α} {s : multiset α} {n : ℕ}

/- card -/
def card (s : multiset α) : nat :=
quot.lift_on s (λ l, length l.1) (λ l₁ l₂, perm_length)

@[simp] theorem card_empty : card (∅ : multiset α) = 0 := rfl

lemma ne_empty_of_card_eq_succ : card s = succ n → s ≠ ∅ :=
λ h hn, by rw hn at h; contradiction

@[simp] theorem card_insert_of_not_mem : a ∉ s → card (insert a s) = card s + 1 :=
quot.induction_on s (λ (l : nodup_list α) (nainl : a ∉ ⟦l⟧), list.length_insert_of_not_mem nainl)

theorem card_insert_le : card (insert a s) ≤ card s + 1 :=
if h : a ∈ s then by simp [h, le_add_left] else by rw [card_insert_of_not_mem h]

theorem eq_empty_of_card_eq_zero : card s = 0 → s = ∅ :=
s.induction_on
  (assume _, rfl)
  (assume a s ha ih, by rw [card_insert_of_not_mem ha]; exact assume h, nat.no_confusion h)

theorem card_erase_of_mem : a ∈ s → card (erase a s) = pred (card s) :=
quot.induction_on s (λ l ainl, list.length_erase_of_mem ainl)

theorem card_range : card (range n) = n :=
list.length_range n

end card
-/

end multiset
