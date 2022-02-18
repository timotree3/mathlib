/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.big_operators.basic
import data.nat.prime
import data.zmod.basic
import ring_theory.multiplicity
import data.nat.periodic
import algebra.char_p.two
import number_theory.divisors

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/

open finset
open_locale big_operators

namespace nat

/-- Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
def totient (n : ℕ) : ℕ := ((range n).filter n.coprime).card

localized "notation `φ` := nat.totient" in nat

@[simp] theorem totient_zero : φ 0 = 0 := rfl

@[simp] theorem totient_one : φ 1 = 1 :=
by simp [totient]

lemma totient_eq_card_coprime (n : ℕ) : φ n = ((range n).filter n.coprime).card := rfl

lemma totient_le (n : ℕ) : φ n ≤ n :=
calc totient n ≤ (range n).card : card_filter_le _ _
           ... = n              : card_range _

lemma totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
calc totient n ≤ ((range n).filter (≠ 0)).card :
  begin
    apply card_le_of_subset (monotone_filter_right _ _),
    intros n1 hn1 hn1',
    simpa only [hn1', coprime_zero_right, hn.ne'] using hn1,
  end
... = n - 1
    : by simp only [filter_ne' (range n) 0, card_erase_of_mem, card_range, pos_of_gt hn, mem_range]
... < n : nat.sub_lt (pos_of_gt hn) zero_lt_one

lemma totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
| 0 := dec_trivial
| 1 := by simp [totient]
| (n+2) := λ h, card_pos.2 ⟨1, mem_filter.2 ⟨mem_range.2 dec_trivial, coprime_one_right _⟩⟩

lemma filter_coprime_Ico_eq_totient (a n : ℕ) :
  ((Ico n (n+a)).filter (coprime a)).card = totient a :=
begin
  rw [totient, filter_Ico_card_eq_of_periodic, count_eq_card_filter_range],
  exact periodic_coprime a,
end

lemma Ico_filter_coprime_le {a : ℕ} (k n : ℕ) (a_pos : 0 < a) :
  ((Ico k (k + n)).filter (coprime a)).card ≤ totient a * (n / a + 1) :=
begin
  conv_lhs { rw ←nat.mod_add_div n a },
  induction n / a with i ih,
  { rw ←filter_coprime_Ico_eq_totient a k,
    simp only [add_zero, mul_one, mul_zero, le_of_lt (mod_lt n a_pos)],
    mono,
    refine monotone_filter_left a.coprime _,
    simp only [finset.le_eq_subset],
    exact Ico_subset_Ico rfl.le (add_le_add_left (le_of_lt (mod_lt n a_pos)) k), },
  simp only [mul_succ],
  simp_rw ←add_assoc at ih ⊢,
  calc (filter a.coprime (Ico k (k + n % a + a * i + a))).card
      = (filter a.coprime (Ico k (k + n % a + a * i)
                            ∪ Ico (k + n % a + a * i) (k + n % a + a * i + a))).card :
        begin
          congr,
          rw Ico_union_Ico_eq_Ico,
          rw add_assoc,
          exact le_self_add,
          exact le_self_add,
        end
  ... ≤ (filter a.coprime (Ico k (k + n % a + a * i))).card + a.totient :
        begin
          rw [filter_union, ←filter_coprime_Ico_eq_totient a (k + n % a + a * i)],
          apply card_union_le,
        end
  ... ≤ a.totient * i + a.totient + a.totient : add_le_add_right ih (totient a),
end

open zmod

/-- Note this takes an explicit `fintype ((zmod n)ˣ)` argument to avoid trouble with instance
diamonds. -/
@[simp] lemma _root_.zmod.card_units_eq_totient (n : ℕ) [fact (0 < n)] [fintype ((zmod n)ˣ)] :
  fintype.card ((zmod n)ˣ) = φ n :=
calc fintype.card ((zmod n)ˣ) = fintype.card {x : zmod n // x.val.coprime n} :
  fintype.card_congr zmod.units_equiv_coprime
... = φ n :
begin
  apply finset.card_congr (λ (a : {x : zmod n // x.val.coprime n}) _, a.1.val),
  { intro a, simp [(a : zmod n).val_lt, a.prop.symm] {contextual := tt} },
  { intros _ _ _ _ h, rw subtype.ext_iff_val, apply val_injective, exact h, },
  { intros b hb,
    rw [finset.mem_filter, finset.mem_range] at hb,
    refine ⟨⟨b, _⟩, finset.mem_univ _, _⟩,
    { let u := unit_of_coprime b hb.2.symm,
      exact val_coe_unit_coprime u },
    { show zmod.val (b : zmod n) = b,
      rw [val_nat_cast, nat.mod_eq_of_lt hb.1], } }
end

lemma totient_even {n : ℕ} (hn : 2 < n) : even n.totient :=
begin
  haveI : fact (1 < n) := ⟨one_lt_two.trans hn⟩,
  suffices : 2 = order_of (-1 : (zmod n)ˣ),
  { rw [← zmod.card_units_eq_totient, even_iff_two_dvd, this], exact order_of_dvd_card_univ },
  rw [←order_of_units, units.coe_neg_one, order_of_neg_one, ring_char.eq (zmod n) n, if_neg hn.ne'],
end

lemma totient_mul {m n : ℕ} (h : m.coprime n) : φ (m * n) = φ m * φ n :=
if hmn0 : m * n = 0
  then by cases nat.mul_eq_zero.1 hmn0 with h h;
    simp only [totient_zero, mul_zero, zero_mul, h]
  else
  begin
    haveI : fact (0 < (m * n)) := ⟨nat.pos_of_ne_zero hmn0⟩,
    haveI : fact (0 < m) := ⟨nat.pos_of_ne_zero $ left_ne_zero_of_mul hmn0⟩,
    haveI : fact (0 < n) := ⟨nat.pos_of_ne_zero $ right_ne_zero_of_mul hmn0⟩,
    rw [← zmod.card_units_eq_totient, ← zmod.card_units_eq_totient,
      ← zmod.card_units_eq_totient, fintype.card_congr
      (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv).to_equiv,
      fintype.card_congr (@mul_equiv.prod_units (zmod m) (zmod n) _ _).to_equiv,
      fintype.card_prod]
  end


section general_totient

/-- ## A generalised totient function -/

-----------------------------------

-- This is in `PR #12104`
lemma filter_eq_empty_iff {α : Type*} (s : finset α) (p : α → Prop) [decidable_pred p] :
   (s.filter p = ∅) ↔ ∀ x ∈ s, ¬ p x := sorry

-----------------------------------

/-- For any `d : ℕ`, `n.gen_totient d` is the number of positive natural numbers `1 ≤ k ≤ n` with
`gcd n k = d`.  So in particular `n.gen_totient 1 = n.totient`. -/

def gen_totient (n d : ℕ) := ((Icc 1 n).filter (λ k, n.gcd k = d)).card

lemma zero_gen_totient (d : ℕ) : gen_totient 0 d = 0 := rfl

lemma gen_totient_zero (n : ℕ) : gen_totient n 0 = 0 :=
begin
  by_cases hn : n = 0, { simp [hn, zero_gen_totient] },
  simp [gen_totient, hn],
end

/-- In the case where `n ≠ d` it is sometimes convenient to express `gen_totient n d`
as a filter on `range n` instead of on `Icc 1 n`. -/
lemma gen_totient_eq_filter_range_of_ne {n d : ℕ} (hnd : n ≠ d) :
  gen_totient n d = ((range n).filter (λ k, n.gcd k = d)).card :=
begin
  unfold gen_totient,
  refine card_congr (λ k _, k) _ (by simp) _,
  { simp only [mem_filter, mem_Icc, mem_range, and_imp],
    intros a _ ha2 ha3,
    refine ⟨lt_of_le_of_ne ha2 _, ha3⟩,
    { intros H, rw [H, gcd_self n] at ha3, exact hnd ha3 } },
  { simp only [mem_filter, mem_range, mem_Icc, exists_prop, exists_eq_right, and_imp],
    intros b hb1 hb2,
    refine ⟨⟨_, le_of_lt hb1⟩, hb2⟩,
    { rw [succ_le_iff, zero_lt_iff],
      intros H,
      rw [H, gcd_zero_right n] at hb2,
      apply hnd hb2 } },
end

example (n : ℕ) (hn : n ≠ 0) : ((range n).filter (λ k, n.gcd k = n)).card = 1 :=
begin
  simp,
  -- rw filter_eq_empty_iff,
  -- intros x hx H,
  -- rcases eq_or_ne x 0 with rfl | hx0, {
  --   simp at *,
  --   sorry },
  -- simp at hx,
  -- have : n ∣ x, { rw ←H, exact gcd_dvd_right n x },

  sorry,
end

lemma gen_totient_self {n : ℕ} (hn : n ≠ 0) : gen_totient n n = 1 :=
begin
  unfold gen_totient,
  -- have := card_union_eq,
  sorry,
end

-- #eval gcd 12 12
-- #eval gen_totient 12 12
-- #eval Icc 1 0
-- #eval totient 3
-- #eval range 3
-- #eval Icc 1 3

-- #eval to_bool (coprime 0 1)
-- #eval to_bool (coprime 1 1)

lemma gen_totient_one (n : ℕ) : n.gen_totient 1 = n.totient :=
begin
  by_cases hn1 : n = 1, { simp [hn1, gen_totient] },
  rw gen_totient_eq_filter_range_of_ne hn1,
  simp only [totient],
  -- suffices : (filter n.coprime (Icc 1 n)) = (filter n.coprime (range n)), { rw this },
  -- ext,
  -- simp only [mem_filter, mem_range, mem_Icc, and.congr_left_iff],
  -- intros han,
  -- split,
  -- { intros h,
  --   apply lt_of_le_of_ne h.2,
  --   rintros rfl,
  --   exact hn1 ((coprime_self a).mp han) },
  -- { intros h,
  --   refine ⟨one_le_iff_ne_zero.mpr _, le_of_lt h⟩,
  --   rintros rfl,
  --   exact hn1 ((coprime_zero_right n).mp han) },
end

lemma gen_totient_eq_zero_of_not_dvd {n d : ℕ} (hnd : ¬ d ∣ n) : n.gen_totient d = 0 :=
begin
  simp only [gen_totient, card_eq_zero, filter_eq_empty_iff],
  intros x hx H,
  rw ←H at hnd,
  cases hnd (gcd_dvd_left n x),
end

-- Put this in `data/nat/basic`
lemma div_by_eq_iff_eq_of_dvd_dvd {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) : a / d = b / d ↔ a = b :=
begin
  split,
  { intros h, rw [←nat.mul_div_cancel' hda, ←nat.mul_div_cancel' hdb, h] },
  { apply congr_arg },
end

lemma div_by_lt_iff_lt_of_dvd_dvd {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) :
  a / d < b / d ↔ a < b :=
begin
  rcases eq_or_ne d 0 with rfl | hd0, { simp at *, rw [hda, hdb] },
  rcases eq_or_ne a 0 with rfl | ha0, {
    simp at *,


    sorry },
  split,
  {
    intros h,
    sorry},
  {
    intros h,

    -- library_search,

    sorry},
end




example
(n d : ℕ)
(hnd : d ∣ n)
(hn0 : n ≠ 0)
(hd0 : d ≠ 0)
(hnd_ne : n ≠ d)
(b : ℕ)
(hb1 : b < n / d)
-- (hb2 : (n / d).coprime b)
: b * d < n
:=
begin


  sorry,
end

lemma gen_totient_dvd_eq_totient_div {n d : ℕ} (hnd : d ∣ n) : n.gen_totient d = φ (n/d) :=
begin
  rcases eq_or_ne n 0 with rfl | hn0, { simp at *, apply zero_gen_totient },
  rcases eq_or_ne d 0 with rfl | hd0, { simp only [nat.div_zero, totient_zero, gen_totient_zero] },
  rcases eq_or_ne n d with rfl | hnd_ne,
  { simp only [gen_totient_self hd0, nat.div_self (zero_lt_iff.mpr hd0), totient_one] },

  rw gen_totient_eq_filter_range_of_ne hnd_ne,

  simp only [totient],
  apply card_congr (λ k _, k/d),
  {
    simp only [mem_filter, mem_range, and_imp],
    intros k hkn hk1,
    have hdk : d ∣ k, { rw ←hk1, exact gcd_dvd_right n k },
    split,
    { exact (@div_by_lt_iff_lt_of_dvd_dvd k n d hdk hnd).mpr hkn },
    {
      unfold coprime,
      rw gcd_div hnd hdk,
      rw hk1,
      refine @nat.div_self d _,
      exact zero_lt_iff.mpr hd0,
    },
  },
  { simp,
    intros a b h1 h2 h3 h4 h5 ,
    apply (div_by_eq_iff_eq_of_dvd_dvd _ _).mp h5,
    { rw ←h2, exact gcd_dvd_right n a },
    { rw ←h4, exact gcd_dvd_right n b },
  },
  {
    simp,
    intros b hb1 hb2,
    use b*d,
    split,
    { split,
      {
        sorry},
      {
        rw coprime.gcd_mul_left_cancel_right,
        { exact gcd_eq_right hnd },
        {
          rw coprime_comm,



          sorry },
      },
      },
      {
        rw mul_comm,
        apply mul_div_right,
        exact zero_lt_iff.mpr hd0,
      },


     },
-- For any divisor d of n, the elements counted by αd(n) are
-- the positive integers 1 ≤ k ≤ n with gcd(k,n) = d.

-- We can write any such k as qd for some 1 ≤ q ≤ n/d.

-- Each of these values of q gives a multiple of d with gcd(qd, n) = d
-- if and only if the product qd has no further prime powers in common with n,
-- i.e. iff gcd(q, n/d) = 1.

-- So there is a 1-1 correspondence between the elements counted by αd(n)
-- and the integers q satisfying 1 ≤ q ≤ n/d with gcd(q, n/d) = 1.
end
#exit
end general_totient

lemma divisors_subset_range_gt {n m : ℕ} (hnm : n < m) : n.divisors ⊆ range m :=
λ x hx, mem_range.mpr (lt_of_le_of_lt (divisor_le hx) hnm)

lemma sum_totient' (n : ℕ) : n.divisors.sum φ = n :=
begin
  by_cases hn : n = 0, { simp [hn] },
  rw ←sum_div_divisors n φ,
  suffices : ∑ (d : ℕ) in n.divisors, n.gen_totient d = n, {
    nth_rewrite_rhs 0 ←this,
    refine sum_congr rfl (λ x hx, _),
    rw gen_totient_dvd_eq_totient_div,
    exact dvd_of_mem_divisors hx },
  -- Every number 1 .. n has a gcd with n that's a divisor of n,
  -- so this sum just runs over an alternative partitioning of 1 .. n,
  -- and hence the sum is equal to n



-- This is a wrong turn, I think:
  -- suffices : ∑ (d : ℕ) in range n.succ, n.gen_totient d = n, {
  --   nth_rewrite_rhs 0 ←this,
  --   refine finset.sum_subset_zero_on_sdiff (divisors_subset_range_ge (le_succ n)) _ (by simp),
  --   { intros x hx,
  --     apply gen_totient_not_dvd_eq_zero,
  --     exact λ H, (mem_sdiff.mp hx).2 (mem_divisors.mpr ⟨H, hn⟩) } },

  sorry,
end


lemma sum_totient (n : ℕ) : ∑ m in (range n.succ).filter (∣ n), φ m = n :=
if hn0 : n = 0 then by simp [hn0]
else
calc ∑ m in (range n.succ).filter (∣ n), φ m
    = ∑ d in (range n.succ).filter (∣ n), ((range (n / d)).filter (λ m, gcd (n / d) m = 1)).card :
  eq.symm $ sum_bij (λ d _, n / d)
    (λ d hd, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _,
      by conv {to_rhs, rw ← nat.mul_div_cancel' (mem_filter.1 hd).2}; simp⟩)
    (λ _ _, rfl)
    (λ a b ha hb h,
      have ha : a * (n / a) = n, from nat.mul_div_cancel' (mem_filter.1 ha).2,
      have 0 < (n / a), from nat.pos_of_ne_zero (λ h, by simp [*, lt_irrefl] at *),
      by rw [← nat.mul_left_inj this, ha, h, nat.mul_div_cancel' (mem_filter.1 hb).2])
    (λ b hb,
      have hb : b < n.succ ∧ b ∣ n, by simpa [-range_succ] using hb,
      have hbn : (n / b) ∣ n, from ⟨b, by rw nat.div_mul_cancel hb.2⟩,
      have hnb0 : (n / b) ≠ 0, from λ h, by simpa [h, ne.symm hn0] using nat.div_mul_cancel hbn,
      ⟨n / b, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _, hbn⟩,
        by rw [← nat.mul_left_inj (nat.pos_of_ne_zero hnb0),
          nat.mul_div_cancel' hb.2, nat.div_mul_cancel hbn]⟩)
... = ∑ d in (range n.succ).filter (∣ n), ((range n).filter (λ m, gcd n m = d)).card :
  sum_congr rfl (λ d hd,
    have hd : d ∣ n, from (mem_filter.1 hd).2,
    have hd0 : 0 < d, from nat.pos_of_ne_zero (λ h, hn0 (eq_zero_of_zero_dvd $ h ▸ hd)),
    card_congr (λ m hm, d * m)
      (λ m hm, have hm : m < n / d ∧ gcd (n / d) m = 1, by simpa using hm,
        mem_filter.2 ⟨mem_range.2 $ nat.mul_div_cancel' hd ▸
          (mul_lt_mul_left hd0).2 hm.1,
          by rw [← nat.mul_div_cancel' hd, gcd_mul_left, hm.2, mul_one]⟩)
      (λ a b ha hb h, (nat.mul_right_inj hd0).1 h)
      (λ b hb, have hb : b < n ∧ gcd n b = d, by simpa using hb,
        ⟨b / d, mem_filter.2 ⟨mem_range.2
            ((mul_lt_mul_left (show 0 < d, from hb.2 ▸ hb.2.symm ▸ hd0)).1
              (by rw [← hb.2, nat.mul_div_cancel' (gcd_dvd_left _ _),
                nat.mul_div_cancel' (gcd_dvd_right _ _)]; exact hb.1)),
            hb.2 ▸ coprime_div_gcd_div_gcd (hb.2.symm ▸ hd0)⟩,
          hb.2 ▸ nat.mul_div_cancel' (gcd_dvd_right _ _)⟩))
... = ((filter (∣ n) (range n.succ)).bUnion (λ d, (range n).filter (λ m, gcd n m = d))).card :
  (card_bUnion (by intros; apply disjoint_filter.2; cc)).symm
... = (range n).card :
  congr_arg card (finset.ext (λ m, ⟨by simp,
    λ hm, have h : m < n, from mem_range.1 hm,
      mem_bUnion.2 ⟨gcd n m, mem_filter.2
        ⟨mem_range.2 (lt_succ_of_le (le_of_dvd (lt_of_le_of_lt (zero_le _) h)
          (gcd_dvd_left _ _))), gcd_dvd_left _ _⟩, mem_filter.2 ⟨hm, rfl⟩⟩⟩))
... = n : card_range _

/-- When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
lemma totient_prime_pow_succ {p : ℕ} (hp : p.prime) (n : ℕ) :
  φ (p ^ (n + 1)) = p ^ n * (p - 1) :=
calc φ (p ^ (n + 1))
    = ((range (p ^ (n + 1))).filter (coprime (p ^ (n + 1)))).card :
  totient_eq_card_coprime _
... = (range (p ^ (n + 1)) \ ((range (p ^ n)).image (* p))).card :
  congr_arg card begin
    rw [sdiff_eq_filter],
    apply filter_congr,
    simp only [mem_range, mem_filter, coprime_pow_left_iff n.succ_pos,
      mem_image, not_exists, hp.coprime_iff_not_dvd],
    intros a ha,
    split,
    { rintros hap b _ rfl,
      exact hap (dvd_mul_left _ _) },
    { rintros h ⟨b, rfl⟩,
      rw [pow_succ] at ha,
      exact h b (lt_of_mul_lt_mul_left ha (zero_le _)) (mul_comm _ _) }
  end
... = _ :
have h1 : set.inj_on (* p) (range (p ^ n)),
  from λ x _ y _, (nat.mul_left_inj hp.pos).1,
have h2 : (range (p ^ n)).image (* p) ⊆ range (p ^ (n + 1)),
  from λ a, begin
    simp only [mem_image, mem_range, exists_imp_distrib],
    rintros b h rfl,
    rw [pow_succ'],
    exact (mul_lt_mul_right hp.pos).2 h
  end,
begin
  rw [card_sdiff h2, card_image_of_inj_on h1, card_range,
    card_range, ← one_mul (p ^ n), pow_succ, ← tsub_mul,
    one_mul, mul_comm]
end

/-- When `p` is prime, then the totient of `p ^ n` is `p ^ (n - 1) * (p - 1)` -/
lemma totient_prime_pow {p : ℕ} (hp : p.prime) {n : ℕ} (hn : 0 < n) :
  φ (p ^ n) = p ^ (n - 1) * (p - 1) :=
by rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩;
  exact totient_prime_pow_succ hp _

lemma totient_prime {p : ℕ} (hp : p.prime) : φ p = p - 1 :=
by rw [← pow_one p, totient_prime_pow hp]; simp

lemma totient_mul_of_prime_of_dvd {p n : ℕ} (hp : p.prime) (h : p ∣ n) :
  (p * n).totient = p * n.totient :=
begin
  by_cases hzero : n = 0,
  { simp [hzero] },
  { have hfin := (multiplicity.finite_nat_iff.2 ⟨hp.ne_one, zero_lt_iff.2 hzero⟩),
    have h0 : 0 < (multiplicity p n).get hfin := multiplicity.pos_of_dvd hfin h,
    obtain ⟨m, hm, hndiv⟩ := multiplicity.exists_eq_pow_mul_and_not_dvd hfin,
    rw [hm, ← mul_assoc, ← pow_succ, nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd
      hndiv)), nat.totient_mul (coprime_comm.mp (hp.coprime_pow_of_not_dvd hndiv)), ← mul_assoc],
    congr,
    rw [ ← succ_pred_eq_of_pos h0, totient_prime_pow_succ hp, totient_prime_pow_succ hp,
      succ_pred_eq_of_pos h0, ← mul_assoc p, ← pow_succ, ← succ_pred_eq_of_pos h0, nat.pred_succ] }
end

lemma totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.prime :=
begin
  refine ⟨λ h, _, totient_prime⟩,
  replace hp : 1 < p,
  { apply lt_of_le_of_ne,
    { rwa succ_le_iff },
    { rintro rfl,
      rw [totient_one, tsub_self] at h,
      exact one_ne_zero h } },
  rw [totient_eq_card_coprime, range_eq_Ico, ←Ico_insert_succ_left hp.le, finset.filter_insert,
      if_neg (not_coprime_of_dvd_of_dvd hp (dvd_refl p) (dvd_zero p)), ←nat.card_Ico 1 p] at h,
  refine p.prime_of_coprime hp (λ n hn hnz, finset.filter_card_eq h n $ finset.mem_Ico.mpr ⟨_, hn⟩),
  rwa [succ_le_iff, pos_iff_ne_zero],
end

lemma card_units_zmod_lt_sub_one {p : ℕ} (hp : 1 < p) [fintype ((zmod p)ˣ)] :
  fintype.card ((zmod p)ˣ) ≤ p - 1 :=
begin
  haveI : fact (0 < p) := ⟨zero_lt_one.trans hp⟩,
  rw zmod.card_units_eq_totient p,
  exact nat.le_pred_of_lt (nat.totient_lt p hp),
end

lemma prime_iff_card_units (p : ℕ) [fintype ((zmod p)ˣ)] :
  p.prime ↔ fintype.card ((zmod p)ˣ) = p - 1 :=
begin
  by_cases hp : p = 0,
  { substI hp,
    simp only [zmod, not_prime_zero, false_iff, zero_tsub],
    -- the substI created an non-defeq but subsingleton instance diamond; resolve it
    suffices : fintype.card ℤˣ ≠ 0, { convert this },
    simp },
  haveI : fact (0 < p) := ⟨nat.pos_of_ne_zero hp⟩,
  rw [zmod.card_units_eq_totient, nat.totient_eq_iff_prime (fact.out (0 < p))],
end

@[simp] lemma totient_two : φ 2 = 1 :=
(totient_prime prime_two).trans (by norm_num)

end nat
