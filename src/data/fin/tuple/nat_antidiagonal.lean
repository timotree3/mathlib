/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import data.fin.vec_notation
import algebra.big_operators.basic
import data.list.nat_antidiagonal

/-!
# Collections of tuples of naturals with the same sum

## Main definitions

* `list.nat.antidiagonal_tuple`
-/

namespace list.nat

open_locale big_operators

/-- `list.antidiagonal_tuple k n` is a list of `k`-tuples summing to `n`. -/
def antidiagonal_tuple : Π k, ℕ → list (fin k → ℕ)
| 0 0 := [![]]
| 0 (n + 1) := []
| (k + 1) n := (list.nat.antidiagonal n).bind $ λ ni,
  (antidiagonal_tuple k ni.2).map $ λ x, fin.cons (ni.1) x

@[simp] lemma antidiagonal_tuple_zero_zero : antidiagonal_tuple 0 0 = [![]] := rfl
@[simp] lemma antidiagonal_tuple_zero_succ (n : ℕ) : antidiagonal_tuple 0 n.succ = [] := rfl

#eval antidiagonal_tuple 1 3

@[simp]
lemma _root_.list.bind_eq_nil {α β} (l : list α) (f : α → list β) :
  list.bind l f = [] ↔ ∀ x ∈ l, f x = [] :=
by simp [list.bind]

lemma antidiagonal_tuple_eq_nil {k n : ℕ} : antidiagonal_tuple k n = [] ↔ k = 0 ∧ n ≠ 0 :=
begin
  induction k,
  { cases n,
    { simp [antidiagonal_tuple] },
    { simp [antidiagonal_tuple] }, },
  { 
    simp_rw [antidiagonal_tuple, list.bind_eq_nil, list.map_eq_nil, mem_antidiagonal,
      nat.succ_ne_zero, false_and, iff_false, not_forall],
    refine ⟨(0, n), zero_add _, _⟩,
    simp [k_ih], },
end

@[simp] lemma antidiagonal_tuple_one (n : ℕ) : antidiagonal_tuple 1 n = [![n]] :=
begin
  -- show antidiagonal_tuple 1 n = [(n, 0)].bind (λ x, [![]].map (λ y, fin.cons x.fst y)),
  simp_rw [antidiagonal_tuple, antidiagonal, list.range_succ, list.map_append, list.map_singleton,
    tsub_self, list.bind_append, list.bind_singleton, antidiagonal_tuple_zero_zero,
    list.map_singleton, list.map_bind],
    conv_rhs { rw ← list.nil_append [![n]]},
  congr' 1,
  simp [list.range_succ_eq_map, list.map_bind, list.bind_eq_nil],
  intros x hx,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hx,
  simp,
  refine list.bind_congr,
  rw bind_eq_bin
  rw list.bind,
  rw list.append_eq,
  induction n,
  { refl, },
  rw [antidiagonal_succ, list.cons_bind],
  dsimp only,
  rw [antidiagonal_zero_succ, list.map_nil, list.nil_append, list.map_bind],
  dsimp,
  change (antidiagonal n_n).bind (λ (a : ℕ × ℕ), list.map (fin.cons a.fst.succ) (antidiagonal_tuple 0 a.snd))
    = [![n_n.succ]],
  simp only [←list.map_map _ nat.succ] { single_pass := tt},
  -- rw ←list.map_bind,
  -- refine (list.bind_map (antidiagonal n_n)).symm.trans _,
end

#check list.bind_map

lemma nat.mem_antidiagonal_tuple {n : ℕ} {k : ℕ} (x : fin k → ℕ) :
  x ∈ antidiagonal_tuple k n ↔ ∑ i, x i = n :=
begin
  induction k with k ih generalizing n,
  { cases n,
    { simp },
    { simp [eq_comm] }, },
  { refine fin.cons_induction (λ x₀ x, _) x,
    have : (0 : fin k.succ) ∉ finset.image fin.succ (finset.univ : finset (fin k)) := by simp,
    simp_rw [antidiagonal_tuple, list.mem_bind, list.mem_map, list.nat.mem_antidiagonal,
      fin.univ_succ, finset.sum_insert this, fin.cons_zero,
      finset.sum_image (λ x hx y hy h, fin.succ_injective _ h), fin.cons_succ, fin.cons_eq_cons,
      exists_eq_right_right, ih, prod.exists],
    split,
    { rintros ⟨a, b, rfl, rfl, rfl⟩, refl },
    { rintro rfl, exact ⟨_, _, rfl, rfl, rfl⟩, } },
end

/-- The antidiagonal of `n` does not contain duplicate entries. -/
lemma nodup_antidiagonal_tuple (k n : ℕ) : list.nodup (antidiagonal_tuple k n) :=
begin
  induction k with k ih generalizing n,
  { cases n,
    { simp },
    { simp [eq_comm] }, },
  simp_rw [antidiagonal_tuple, list.nodup_bind],
  split,
  { intros i hi,
    exact (ih i.snd).map (fin.cons_right_injective (i.fst : (λ _, ℕ) 0)), },
  induction n,
  { exact list.pairwise_singleton _ _ },
  { rw list.nat.antidiagonal_succ,
    refine list.pairwise.cons (λ a ha x hx₁ hx₂, _) (n_ih.map _ (λ a b h x hx₁ hx₂, _)),
    { rw list.mem_map at hx₁ hx₂ ha,
      obtain ⟨⟨a, -, rfl⟩, ⟨x₁, -, rfl⟩, ⟨x₂, -, h⟩⟩ := ⟨ha, hx₁, hx₂⟩,
      rw fin.cons_eq_cons at h,
      injection h.1, },
    { rw list.mem_map at hx₁ hx₂,
      obtain ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, h₁₂⟩⟩ := ⟨hx₁, hx₂⟩,
      dsimp at h₁₂,
      rw [fin.cons_eq_cons, nat.succ_inj'] at h₁₂,
      obtain ⟨h₁₂, rfl⟩ := h₁₂,
      rw h₁₂ at h,
      exact h (list.mem_map_of_mem _ hx₁) (list.mem_map_of_mem _ hx₂) }, },
end


lemma antidiagonal_tuple_two (n : ℕ) :
  antidiagonal_tuple 2 n = (antidiagonal n).map (λ i, ![i.1, i.2]) :=
begin
  rw antidiagonal_tuple,
  simp_rw [antidiagonal_tuple_one, list.map_singleton],
  rw [list.map_eq_bind],
  refl,
end


end list.nat
