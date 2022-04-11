/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.mv_polynomial.cardinal
import data.mv_polynomial.equiv
/-!
# Cardinality of Polynomial Ring

The reuslt in this file is that the cardinality of `polynomial R` is at most the maximum
of `#R` and `ω`.
-/
universe u

open_locale cardinal polynomial
open cardinal

namespace polynomial

variables (R : Type u) [comm_semiring R]

lemma cardinal_mk_le_max : #R[X] ≤ max (#R) ω :=
calc #R[X] = #(mv_polynomial punit.{u + 1} R) :
  cardinal.eq.2 ⟨(mv_polynomial.punit_alg_equiv.{u u} R).to_equiv.symm⟩
... ≤ _ : mv_polynomial.cardinal_mk_le_max
... ≤ _ : by rw [max_assoc, max_eq_right (lt_omega_of_fintype punit).le]

@[simp] lemma cardinal_mk_eq_of_infinite [infinite R] : #R[X] = #R :=
le_antisymm (by { convert cardinal_mk_le_max R, simp }) (mk_le_of_injective (λ a b h, C_inj.1 h))

@[simp] lemma cardinal_mk_eq_of_fintype_of_nontrivial [fintype R] [nontrivial R] : #R[X] = ω :=
begin
  apply le_antisymm,
  {
    convert cardinal_mk_le_max R,
    rw [max_eq_right],
    apply le_of_lt,
    apply lt_omega_of_fintype,
    sorry,
  },
  sorry
end

end polynomial
