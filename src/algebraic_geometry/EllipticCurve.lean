/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import algebra.group_power
import data.rat.basic
import tactic.norm_num tactic.ring

/-!
# The category of elliptic curves (over a field or a PID)

We give a working definition of elliptic curves which is mathematically accurate
in many cases, and also good for computation.

## Mathematical background

Let `S` be a scheme. The actual category of elliptic curves over `S` is a large category,
whose objects are schemes `E` equipped with a map `E → S`, a section `S → E`, and some
axioms (the map is smooth and proper and the fibres are geometrically connected group varieties
of dimension 1). In the special case where `S` is `Spec R` for some commutative ring `R`
whose Picard group is trivial (this includes all fields, all principal ideal domains, and many
other commutative rings) then it can be shown (using rather a lot of algebro-geometric machinery)
that every elliptic curve is, up to isomorphism, a projective plane cubic defined by
the equation `y^2+a₁xy+a₃y=x^3+a₂x^2+a₄x+a₆`, with `aᵢ : R`, and such that the discriminant
of the aᵢ is a unit in `R`.

Some more details of the construction can be found on pages 66-69 of
[N. Katz and B. Mazur, *Arithmetic moduli of elliptic curves*][katz_mazur] or pages
53-56 of [P. Deligne, *Courbes elliptiques: formulaire d'après J. Tate*][deligne_formulaire].

## Warning

The definition in this file makes sense for all commutative rings `R`, but it only gives
a type which can be beefed up to a category which is equivalent to the category of elliptic
curves over `Spec R` in the case that `R` has trivial Picard group or, slightly more generally,
when the 12-torsion of Pic(R) is trivial. The issue is that for a general ring R, there
might be elliptic curves over Spec(R) in the sense of algebraic geometry which are not
globally defined by a cubic equation valid over the entire base.

## TODO

Define the R-points (or even A-points if A is an R-algebra). Care will be needed
at infinity if R is not a field. Define the group law on the R-points. (hard) prove associativity.

-/

/-- The discriminant of the plane cubic `Y^2+a1*X*Y+a3*Y=X^3+a2*X^2+a4*X+a6`. If `R` is a field
then this polynomial vanishes iff the cubic curve cut out by this equation is singular. -/
def EllipticCurve.disc_aux {R : Type*} [comm_ring R] (a1 a2 a3 a4 a6 : R) : R :=
-432*a6^2 + ((288*a2 + 72*a1^2)*a4 + (-216*a3^2 + (144*a1*a2 + 36*a1^3)*a3 + (-64*a2^3 -
48*a1^2*a2^2 - 12*a1^4*a2 - a1^6)))*a6 + (-64*a4^3 + (-96*a1*a3 + (16*a2^2 + 8*a1^2*a2 + a1^4))*a4^2
+ ((72*a2 - 30*a1^2)*a3^2 + (16*a1*a2^2 + 8*a1^3*a2 + a1^5)*a3)*a4 + (-27*a3^4 + (36*a1*a2 +
a1^3)*a3^3 + (-16*a2^3 - 8*a1^2*a2^2 - a1^4*a2)*a3^2))

-- If Pic(R)[12]=0 then this definition is mathematically correct
/-- The category of elliptic curves over `R` (note that this definition is only mathematically
correct for certain rings, for example if `R` is a field or a PID). -/
structure EllipticCurve (R : Type*) [comm_ring R] :=
(a1 a2 a3 a4 a6 : R)
(disc_unit : units R)
(disc_unit_eq : (disc_unit : R) = EllipticCurve.disc_aux a1 a2 a3 a4 a6)

namespace EllipticCurve

instance : inhabited (EllipticCurve ℚ) := ⟨⟨0,0,1,-1,0, ⟨37, 37⁻¹, by norm_num, by norm_num⟩,
  show (37 : ℚ) = _ + _, by norm_num⟩⟩

variables {R : Type*} [comm_ring R] (E : EllipticCurve R)

/-- The discriminant of an elliptic curve. Sometimes only defined up to sign in the literature;
  we choose the sign used by the LMFDB. See
  [the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant)
  for more discussion. -/
def disc : R := disc_aux E.a1 E.a2 E.a3 E.a4 E.a6

lemma disc_is_unit : is_unit E.disc :=
begin
  convert units.is_unit E.disc_unit,
  exact E.disc_unit_eq.symm
end


def satisfies_equation (E : EllipticCurve R) (x y : R) : Prop :=
y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6

@[simp]
lemma satisfies_equation_def (E : EllipticCurve R) (x y : R) :
satisfies_equation E x y ↔ y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6 := iff.rfl


lemma no_repeated_roots [nontrivial R] {x y : R} (h : satisfies_equation E x y)
(h' : y + y + E.a1 * x + E.a3 = 0) : 3*x*x + 2*E.a2*x + E.a4 - E.a1 * y ≠ 0 :=
begin
  simp at h,
  replace h : y ^ 2 + E.a1 * x * y + E.a3 * y - x^3 - E.a2 * x^2 - E.a4 * x - E.a6 = 0,
  { rw h, ring },
  intro h'',
  apply is_unit.ne_zero (disc_is_unit E),
  rw disc,
  rw disc_aux,
  set c1 := (E.a1^5*E.a2*x + E.a1^5*x^2 - E.a1^6*y - E.a1^4*E.a2*E.a3 + E.a1^5*E.a4 + 12*E.a1^3*E.a2^2*x
- E.a1^4*E.a3*x + 12*E.a1^3*E.a2*x^2 - 12*E.a1^4*E.a2*y + E.a1^4*x*y - 8*E.a1^2*E.a2^2*E.a3 +
E.a1^3*E.a3^2 + 10*E.a1^3*E.a2*E.a4 + 48*E.a1*E.a2^3*x - 42*E.a1^2*E.a2*E.a3*x - 3*E.a1^3*E.a4*x +
48*E.a1*E.a2^2*x^2 - 36*E.a1^2*E.a3*x^2 - 48*E.a1^2*E.a2^2*y + 37*E.a1^3*E.a3*y +
84*E.a1^2*E.a2*x*y + 72*E.a1^2*x^2*y - 74*E.a1^3*y^2 - 16*E.a2^3*E.a3 + 36*E.a1*E.a2*E.a3^2 +
32*E.a1*E.a2^2*E.a4 - 33*E.a1^2*E.a3*E.a4 + 27*E.a1*E.a3^2*x - 168*E.a1*E.a2*E.a4*x -
144*E.a1*E.a4*x^2 - 32*E.a2^3*y - 72*E.a1*E.a2*E.a3*y + 222*E.a1^2*E.a4*y + 288*E.a2^2*x*y -
108*E.a1*E.a3*x*y + 840*E.a2*x^2*y + 504*x^3*y - 288*E.a1*E.a2*y^2 - 420*E.a1*x*y^2 - 27*E.a3^3 +
72*E.a2*E.a3*E.a4 - 144*E.a1*E.a4^2 + 144*E.a1*E.a2*E.a6 + 216*E.a1*E.a6*x + 54*E.a3^2*y +
288*E.a2*E.a4*y + 312*E.a4*x*y + 108*E.a3*y^2 - 216*E.a3*E.a6 - 216*E.a6*y) with hc1,
set c2 := (E.a1^6 + 12*E.a1^4*E.a2 + 48*E.a1^2*E.a2^2 -
36*E.a1^3*E.a3 + 72*E.a1^3*y + 64*E.a2^3 - 144*E.a1^2*E.a4 + 32*E.a2^2*x - 96*E.a2*x^2 +
272*E.a1*E.a2*y + 504*E.a1*x*y - 272*E.a2*E.a4 - 288*E.a4*x - 216*E.a3*y + 432*E.a6) with hc2,
set c3 := (-E.a1^5*y - 2*E.a1^3*E.a2*E.a3 + E.a1^4*E.a4 -
12*E.a1^3*E.a2*y - 16*E.a1*E.a2^2*E.a3 + 3*E.a1^2*E.a3^2 + 8*E.a1^2*E.a2*E.a4 + 32*E.a2^3*x -
32*E.a2*x^3 - 48*E.a1*E.a2^2*y + 36*E.a1^2*E.a3*y - 76*E.a1^2*y^2 + 16*E.a2^2*E.a4 +
48*E.a1*E.a3*E.a4 - 72*E.a1^2*E.a6 - 144*E.a2*E.a4*x - 96*E.a4*x^2 - 160*E.a2*E.a3*y +
224*E.a1*E.a4*y - 240*E.a3*x*y - 304*E.a2*y^2 - 336*x*y^2 - 64*E.a4^2 + 16*E.a2*E.a6 +
144*E.a6*x) with hc3,
  rw [show 0 = (y + y + E.a1 * x + E.a3) * c1 +
  (y ^ 2 + E.a1 * x * y + E.a3 * y - x ^ 3 - E.a2 * x ^ 2 - E.a4 * x - E.a6) * c2 +
   (3 * x * x + 2 * E.a2 * x + E.a4 - E.a1 * y) * c3, by {
  rw [h, h', h''], ring }],
  rw [hc1,hc2,hc3],
  ring,
end

/-- The j-invariant of an elliptic curve. -/
def j := (-48*E.a4 + (-24*E.a1*E.a3 + (16*E.a2^2 + 8*E.a1^2*E.a2 + E.a1^4)))^3 *
  (E.disc_unit⁻¹ : units R)

end EllipticCurve
