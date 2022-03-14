import algebraic_geometry.EllipticCurve
import tactic
--import algebra.field_power

example (K : Type) [field K] (x : K) (hx : x ≠ 0) : x * (1/x) = 1 := mul_div_cancel' 1 hx

namespace EllipticCurve

variables {K : Type*} [field K] (E : EllipticCurve K)
/-

# Elliptic curves over fields.

-/

/-

## Points on the elliptic curve `[a₁,a₂,a₃,a₄,a₆]`

`K` is a field throughout, and `E` is an elliptic curve over `K`.

The affine curve we're thinking about is `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆`. But the
curve itself is a smooth projective curve, cut out as a subspace of `ℙ²` by
the projectve cubic `Y²Z+a₁XYZ+a₃YZ³=X³+a₂X²Z+a₄XZ²+a₆Z³`, with the affine
solution `(x,y) := (t,s) : K²` corresponding to the projective point
`[X:Y:Z] := [t:s:1] : ℙ²(K)`. To analyse what is happening at infinity
one sets `Z=0`; the line at infinity is then `[*:*:0]`,
and the projective curve meets this line at the solutions to `X³=0`,
which is the point `[0:1:0]` with multiplicity 3.

-/
inductive points (E : EllipticCurve K)
| zero : points -- the so-called "point at infinity".
| some (x y : K) (h : y^2+E.a1*x*y+E.a3*y=x^3+E.a2*x^2+E.a4*x+E.a6) : points

open points

variable {E}

-- use `0` to mean `zero`
instance : has_zero (points E) := ⟨zero⟩

/--

## Lines through infinity.

The line at infinity `[*:*:0]` is the complement of the affine piece `[*:*:1]`.
The lines through the point at infinity `[0:1:0]` correspond to the points on
the line `B=0` in the dual `[A:B:C]` plane. The points in that line are the `[A:0:C]`
with `[A:C]` in projective 1-space, and are hence either `[0:0:1]` or of the
form `[1:0:t]` for some `t` in the field. Hence the lines through the point at
infinity are the line at infinity, and the lines corresponding to the vertical
lines `x=t` as `t` varies.

## Consequences for the group law.

`P + Q = 0 ↔ Q = -P`. Two points sum to zero iff the line through them
goes through the point at infinity. This means that the generic affine
point `P=(t,s)` will have negative `-P=(t,s')`, where `s` and `s'` are the
two roots of `y^2+a₁ty+a₃y-f(t)=0` for `f(x)=x³+a₂x^2+a₄x+a₆`. This
means that `s+s'=-(a₁t+a₃)` and one can then solve for `s'`. Using the
language of algebraic geometry one can make this statement precise in
cases where the roots coincide.

-/

def neg : points E → points E
| zero := zero
| (some t s h) := some t (-E.a3 - E.a1 * t - s) begin
  rw ← h,
  ring,
end

instance : has_neg (points E) := ⟨EllipticCurve.neg⟩

theorem neg_neg : ∀ P : points E, - -P = P
| zero := rfl
| (some x y h) := by simp [has_neg.neg, neg]

/-
Addition needs to split on equality in ℙ²(K) if we work with affine coordinates
-/

variable [decidable_eq K]

/-

## Elliptic curve addition

The point at infinity is the identity. The interesting question
is adding two finite points `P₁=(t₁,s₁)` and `P₂=(t₂,s₂)`.

We first deal with the case `t₁=t₂=t`. Then s₁ and s₂ are the two
roots of a monic quadratic, so either their sum is `-(a₁t+a₃)` or they
are not the two distinct roots of this quadratic and hence must coincide.

If `s₁+s₂=-(a₁t+a₃)` then `P₁+P₂=∞` because `P₂=-P₁`.

The remaining `t₁=t₂=t` case is when `s₁=s₂=s`. The tangent
`y=lx+m` to the curve at `(t,s)` cuts the curve at `(t,s)` with multiplicity
2 (generically); let `P₃=(t₃,s₃)` be the third point of intersection.
Differentiating the cubic wrt `x` and substituting in `l` for `dy/dx` we get
deduce `2yl+a₁xl+a₃l=3x²+2a₂x+a₄`. Recall that we are assuming that
`2s≠-(a₁t+a₃)` and so `l=(3t²+2a₂t+a₄)/(2s+a₁t+a₃)` and `m=s-lt`.
Letting the third point of intersection be `(t₃,s₃)` as before,
we see `t₃:=l²+a₁l+a₃-2t` and then `s₃=lt₃+m`.

Now we deal with `t₁≠t₂`. The line joining the two points is `y=lx+m`
where `l=(s₁-s₂)/(t₁-t₂)` and `m` is some mess. The
line cuts the curve `P₁`, `P₂` and `P₃:=-(P₁+P₂) =:(t₃,s₃)`. Eliminating
`y` we see that the `tᵢ` are the three roots of
`(lx+m)²+a₁x(lx+m)+a₃(lx+m)=x³+a₂x²+a₄x+a₆`, and hence their
sum can be computed to be by `l²+a₁l+a₃` (consider the coefficients of `x²`
in the equation). Hence `t₃:=l²+a₁l+a₃-t₁-t₂` and the simplest way to
compute `s₃` is that it's equal to `lt₃+m` where
`m=s₁-lt₁=s₂-lt₂=(s₁t₂+s₂t₁)/(t₁-t₂)`; now apply `neg`.

-/

lemma pow_three {M : Type*} [monoid M] (m : M) : m^3=m*m*m := by {rw [pow_succ, pow_succ, pow_one, mul_assoc] }

example (a b c : K) (h : b ≠ 0) (h0 : a * b = 0) : a = 0 :=
begin
  rw mul_eq_zero at h0,
  tauto,
end

protected def add : points E → points E → points E
| zero           zero           := zero
| zero           (some x y h)   := some x y h
| (some x y h)   zero           := some x y h
| (some t₁ s₁ h₁) (some t₂ s₂ h₂) :=
if h : (t₁ = t₂) then
  --  `P₁=±P₂`. Let's deal with `P₁=-P₂` first
  if h' : s₁ + s₂ + E.a1 * t₁ + E.a3 = 0 then zero
  -- `P₁=P₂` -- we use variables s₁ and t₁ and can prove s₁=s₂
  else let l := (3*t₁*t₁+2*E.a2*t₁+E.a4 - E.a1*s₁)/(2*s₁+E.a1*t₁+E.a3) in
       let t₃ := l^2+E.a1*l-E.a2-2*t₁ in
  some t₃ (-E.a1 * t₃ - E.a3 - l * t₃ + l * t₁ - s₁) begin
    subst h,
    rename t₁ t,
    -- prove that s₁ = s₂ using h₁ and h₂ and also h'
    have hs : s₁ = s₂,
    { rw [← h₂,← sub_eq_zero,
        show s₁ ^ 2 + E.a1 * t * s₁ + E.a3 * s₁ - (s₂ ^ 2 + E.a1 * t * s₂ + E.a3 * s₂) =
        (s₁-s₂)*((s₁+s₂)+E.a1*t+E.a3), by ring,
      mul_eq_zero, sub_eq_zero] at h₁,
      cases h₁, assumption, contradiction },
    subst hs,
    rename s₁ s,
    rw ← two_mul at h', -- s+s -> 2s because that's the denominator.
    change 2 * s + E.a1 * t + E.a3 ≠ 0 at h',
    suffices : (l * t₃ - l * t + s)^2 + E.a1 * t₃ * (l * t₃ - l * t + s) + E.a3 * (l * t₃ - l * t + s)
      = t₃ ^ 3 + E.a2 * t₃ ^ 2 + E.a4 * t₃ + E.a6,
    {
      rw ←this,
      ring,
    },
    apply eq.symm,
    rw ← sub_eq_zero,
    rw show t₃ ^ 3 + E.a2 * t₃ ^ 2 + E.a4 * t₃ + E.a6 -
    ((l * t₃ - l * t + s) ^ 2 + E.a1 * t₃ * (l * t₃ - l * t + s) + E.a3 * (l * t₃ - l * t + s)) =
    (t₃ - E.a1*l - l^2 + E.a2 + 2*t)*(t₃-t)^2 +
    (-E.a1*t*l + 2*E.a2*t + 3*t^2 - E.a1*s - E.a3*l - 2*s*l + E.a4)*t₃
    + E.a1*t^2*l - E.a2*t^2 - 2*t^3 + E.a3*t*l + 2*t*s*l - E.a3*s - s^2 + E.a6, by ring,
    rw show t₃ - E.a1 * l - l ^ 2 + E.a2 + 2 * t = 0, by {simp [t₃], ring},
    rw show s^2 = t ^ 3 + E.a2 * t ^ 2 + E.a4 * t + E.a6 - E.a1 * t * s - E.a3 * s,
      by {rw ←h₂, ring},
    have h2sl : 2*s*l = 3 * t * t + 2 * E.a2 * t + E.a4 - E.a1 * s - E.a1 * t*l + - E.a3*l,
    {
      field_simp [h'],
      ring,
    },
    norm_num,
    rw show -(E.a1 * t * l) + 2 * E.a2 * t + 3 * t ^ 2 - E.a1 * s - E.a3 * l - 2 * s * l + E.a4 = 0,
      by {simp [h2sl], ring},
    field_simp [h2sl],
    ring,
  end
else let l :=(s₁-s₂)/(t₁-t₂) in
     let m :=  s₁ - l * t₁ in
     let t₃ :=l*l+E.a1*l-E.a2-t₁-t₂ in
     -(some t₃ (l*t₃+m)
     begin
       replace h := sub_ne_zero.mpr h,
       apply eq.symm,
       rw ← sub_eq_zero,
       have hm : m = s₁ - l * t₁, by tauto,
       suffices : (t₃ ^ 3 + E.a2 * t₃ ^ 2 + E.a4 * t₃ + E.a6
       - ((l * t₃ + m) ^ 2 + E.a1 * t₃ * (l * t₃ + m) + E.a3 * (l * t₃ + m)))
       * (t₁-t₂) = 0, by { rw mul_eq_zero at this, tauto,},
       rw show (t₃ ^ 3 + E.a2 * t₃ ^ 2 + E.a4 * t₃ + E.a6 -
       ((l * t₃ + m) ^ 2 + E.a1 * t₃ * (l * t₃ + m) + E.a3 * (l * t₃ + m)))*(t₁-t₂) =
       (t₃ - E.a1*l - l^2 + E.a2 + t₁ + t₂)*(t₃-t₁)*(t₃-t₂)*(t₁-t₂) +
       (t₃-t₁) * ( (l*(t₂-t₁) + s₁-s₂)*(E.a1*t₂ - t₁*l + t₂*l + E.a3 + s₁ + s₂) +
        (s₂ ^ 2 + E.a1 * t₂ * s₂ + E.a3 * s₂ -
       t₂ ^ 3 - E.a2 * t₂ ^ 2 - E.a4 * t₂ - E.a6)
       - (s₁ ^ 2 + E.a1 * t₁ * s₁ + E.a3 * s₁ - t₁ ^ 3 - E.a2 * t₁ ^ 2 - E.a4 * t₁ - E.a6) ) -
        (t₁-t₂)*(s₁ ^ 2 + E.a1 * t₁ * s₁ + E.a3 * s₁ - t₁ ^ 3 - E.a2 * t₁ ^ 2 - E.a4 * t₁ - E.a6),
      {
        rw hm,
        ring,
      },
      rw show (t₃ - E.a1 * l - l ^ 2 + E.a2 + t₁ + t₂) = 0,
      {
        simp [t₃],
        ring,
      },
      rw show s₁ ^ 2 + E.a1 * t₁ * s₁ + E.a3 * s₁ - t₁ ^ 3 - E.a2 * t₁ ^ 2 - E.a4 * t₁ - E.a6 = 0,
        by {rw h₁, ring},
      rw show s₂ ^ 2 + E.a1 * t₂ * s₂ + E.a3 * s₂ - t₂ ^ 3 - E.a2 * t₂ ^ 2 - E.a4 * t₂ - E.a6 = 0,
        by {rw h₂, ring},
      norm_num,
      right,left,
      field_simp [h],
      ring,
     end
     ) -- level 2; add

instance : has_add (points E) := ⟨EllipticCurve.add⟩

@[simp] lemma tell_simplifier_to_use_numerals : (zero : points E) = 0 := rfl
@[simp] lemma add_zero (P : points E) : P + 0 = P := by {cases P; refl }
@[simp] lemma zero_add (P : points E) : 0 + P = P := by {cases P; refl }




lemma add_assoc : ∀ {P Q R : points E}, P + Q + R = P + (Q + R)
| zero           zero           zero           := rfl
| (some a b hab) zero           zero           := rfl
| zero           (some c d hcd) zero           := rfl
| zero           zero           (some e f hef) := rfl
| (some a b hab) (some c d hcd) zero           := by simp
| (some a b hab) zero           (some e f hef) := rfl
| zero           (some c d hcd) (some e f hef) := by simp
| (some a b hab) (some c d hcd) (some e f hef) := sorry -- boss level; add_assoc

end EllipticCurve
