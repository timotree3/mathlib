import algebraic_geometry.EllipticCurve
import tactic

noncomputable theory

namespace EllipticCurve

variables {K : Type*} [field K] {E : EllipticCurve K}
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
@[simp]
def satisfies_equation (E : EllipticCurve K) (x y : K) : Prop :=
y^2 + E.a1*x*y + E.a3*y = x^3 + E.a2*x^2 + E.a4*x + E.a6


inductive points (E : EllipticCurve K)
| zero : points -- the so-called "point at infinity".
| some (x y : K) (h : satisfies_equation E x y) : points

instance [decidable_eq K] : decidable_eq (points E) :=
begin
  rintros (_|⟨_,_,_⟩) (_|⟨_,_,_⟩),
  simpa using classical.dec true,
  simpa using classical.dec false,
  simpa using classical.dec false,
  simpa using and.decidable,
end

open points

def points.x {E : EllipticCurve K} : points E → K
| zero := 0 -- garbage
| (some x y h) := x

def points.y {E : EllipticCurve K} : points E → K
| zero := 0 -- garbage
| (some x y h) := y

-- use `0` to mean `zero`
instance : has_zero (points E) := ⟨zero⟩


lemma mk_coe {P : points E} (h : P ≠ zero) (hxy) :
  some P.x P.y hxy = P :=
begin
  cases P;tauto,
end

@[simp] lemma coe_mk_x {x y : K} (h) : (@points.some _ _ E x y h).x = x := rfl

@[simp] lemma coe_mk_y {x y : K} (h) : (@points.some _ _ E x y h).y = y := rfl

lemma eq_of_eq_xy {P Q : points E} (hPnz : P ≠ 0) (hQnz : Q ≠ 0) (hx : P.x = Q.x)
(hy : P.y = Q.y) : P = Q :=
begin
  cases P, tauto,
  cases Q, tauto,
  congr; assumption,
end

lemma satisfies_equation_of_nonzero {E : EllipticCurve K} {P : points E}
(h : P ≠ 0) : satisfies_equation E P.x P.y :=
begin
  cases P, tauto,
  exact P_h,
end

@[simp]
lemma some_ne_zero {E : EllipticCurve K} {x y : K} {h} : @points.some _ _ E x y h ≠ zero := by tauto

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

variable {E}

lemma neg_formula {x y : K} (h : satisfies_equation E x y) :
satisfies_equation E x (-E.a3 - E.a1 * x - y) :=
begin
  simp only [satisfies_equation] at h ⊢,
  rw ←h,
  ring,
end

def neg : points E → points E
| zero := zero
| (some t s h) := some t (-E.a3 - E.a1 * t - s) (neg_formula h)

instance : has_neg (points E) := ⟨EllipticCurve.neg⟩

@[simp]
theorem neg_neg : ∀ P : points E, neg (neg P) = P
| zero := rfl
| (some x y h) := by simp [has_neg.neg, neg]

@[simp]
lemma eq_neg_iff_neg_eq (P Q : points E) : neg P = Q ↔ P = neg Q :=
begin
  split,
  {
    intro h,
    rw ←h,
    simp,
  },
  {
    intro h,
    rw h,
    simp,
  }
end

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

@[simp] lemma neg_some {x y : K} (h : satisfies_equation E x y) :
neg (some x y h) = some x (-E.a3 - E.a1 * x - y) (neg_formula h) := rfl

lemma add_neg_formula {t₁ t₂ s₁ s₂ : K} (h : t₁ ≠ t₂)
(h₁ : satisfies_equation E t₁ s₁) (h₂ : satisfies_equation E t₂ s₂)
: let l :=(s₁-s₂)/(t₁-t₂) in let m :=  s₁ - l * t₁ in let t₃ :=l*l+E.a1*l-E.a2-t₁-t₂ in
satisfies_equation E t₃ (l*t₃+m) :=
begin
  simp only [satisfies_equation] at h₁ h₂ ⊢,
  set l :=(s₁-s₂)/(t₁-t₂) with ←hl,
  set m :=  s₁ - l * t₁ with ←hm,
  set t₃ :=l*l+E.a1*l-E.a2-t₁-t₂ with ←h₃,
  replace h := sub_ne_zero.mpr h,
  apply eq.symm,
  rw ← sub_eq_zero,
  let z₁ := s₁ ^ 2 + E.a1 * t₁ * s₁ + E.a3 * s₁ - t₁ ^ 3 - E.a2 * t₁ ^ 2 - E.a4 * t₁ - E.a6,
  let z₂ := s₂ ^ 2 + E.a1 * t₂ * s₂ + E.a3 * s₂ - t₂ ^ 3 - E.a2 * t₂ ^ 2 - E.a4 * t₂ - E.a6,
  let z₃ := l * (t₂ - t₁) + s₁ - s₂,
  apply (is_unit.mul_left_eq_zero (is_unit.mk0 _ h)).mp,
  suffices : (t₃ - E.a1*l - l^2 + E.a2 + t₁ + t₂)*(t₃-t₁)*(t₃-t₂)*(t₁-t₂) +
  (t₃-t₁)*((E.a1*t₂ + E.a3 + l*(t₂-t₁)+s₁+s₂)*z₃ + z₂ - z₁)-(t₁-t₂)*z₁ = 0,
  by {simp [←this, z₁, z₂, z₃, m], ring },
  rw show z₁ = 0, by {simp [z₁, h₁], ring},
  rw show z₂ = 0, by {simp [z₂, h₂], ring},
  rw show z₃ = 0, by {simp [z₃], field_simp [h], ring},
  simp only [t₃],
  ring,
end

lemma double_formula {x y : K} (h : satisfies_equation E x y) (h' : y + y + E.a1 * x + E.a3 ≠ 0)
: let l := (3*x*x+2*E.a2*x+E.a4 - E.a1*y)/(2*y+E.a1*x+E.a3) in let t₃ := l^2+E.a1*l-E.a2-2*x in
  satisfies_equation E t₃ (-E.a1 * t₃ - E.a3 - l * t₃ + l * x - y) :=
begin
  simp only [satisfies_equation],
  rw ← two_mul at h', -- s+s -> 2s because that's the denominator.
  set l := (3*x*x+2*E.a2*x+E.a4 - E.a1*y)/(2*y+E.a1*x+E.a3),
  set t₃ := l^2+E.a1*l-E.a2-2*x,
  let z₃ := t₃ - E.a1 * l - l ^ 2 + E.a2 + 2 * x,
  set w := l * t₃ - l * x + y with hw,
  suffices : t₃ ^ 3 + E.a2 * t₃ ^ 2 + E.a4 * t₃ + E.a6 = w^2 + E.a1 * t₃ * w + E.a3 * w,
    by {rw [this, hw], ring},
  suffices : z₃*(t₃-x)^2 + (3*x^2 + 2*E.a2*x + E.a4 - E.a1*(y+x*l) - E.a3*l - 2*y*l)*t₃
  + E.a1*x^2*l - E.a2*x^2 - 2*x^3 + E.a3*x*l + 2*x*y*l - E.a3*y - y^2 + E.a6 = 0,
    by {simp only [z₃] at this, rw [← sub_eq_zero, ←this, hw], ring},
  rw show z₃ = 0, by {simp [z₃, t₃], ring},
  simp at h,
  rw show y^2 = x ^ 3 + E.a2 * x ^ 2 + E.a4 * x + E.a6 - E.a1 * x * y - E.a3 * y,
    by { rw ←h, ring },
  field_simp [h'], ring,
end

lemma double_formula' {P : points E} (h : P ≠ 0) (h' : P.y + P.y + E.a1 * P.x + E.a3 ≠ 0) :
let l := (3*P.x*P.x+2*E.a2*P.x+E.a4 - E.a1*P.y)/(2*P.y+E.a1*P.x+E.a3) in
let t₃ := l^2+E.a1*l-E.a2-2*P.x in
  satisfies_equation E t₃ (-E.a1 * t₃ - E.a3 - l * t₃ + l * P.x - P.y)
:= double_formula (satisfies_equation_of_nonzero h) h'

lemma eq_or_neg_of_eq_x {x y z : K} (hx : satisfies_equation E x y)
(hy : satisfies_equation E x z) : z = y  ∨ z = -E.a1 * x - E.a3 - y :=
begin
  by_cases h' : y + z + E.a1 * x + E.a3 = 0,
  { right,
    rw [←sub_eq_zero, ←h'],
    ring },
  left,
  simp at hx,
  simp at hy,
  rw [←hy, ←sub_eq_zero,
   show y ^ 2 + E.a1 * x * y + E.a3 * y - (z ^ 2 + E.a1 * x * z + E.a3 * z) =
        (y-z)*((y+z)+E.a1*x+E.a3), by ring, mul_eq_zero, sub_eq_zero] at hx,
  cases hx,
  { rw hx },
  { contradiction }
end

lemma eq_y_of_eq_x {x y z : K} (hx : satisfies_equation E x y)
(hy : satisfies_equation E x z) (h' : y + z + E.a1 * x + E.a3 ≠ 0) : y = z :=
begin
  symmetry,
  cases eq_or_neg_of_eq_x hx hy,
  assumption,
  replace h : y + z + E.a1 * x + E.a3 = 0, by { rw h,ring },
  contradiction,
end

lemma eq_y_of_eq_x' {P Q : points E} (hPnz : P ≠ 0) (hQnz : Q ≠ 0) (hx : P.x = Q.x)
(h' : P.y + Q.y + E.a1 * P.x + E.a3 ≠ 0) : P.y = Q.y :=
begin
  have hQ := satisfies_equation_of_nonzero hQnz,
  rw ←hx at hQ,
  apply eq_y_of_eq_x (satisfies_equation_of_nonzero hPnz) hQ,
  assumption,
end

lemma eq_of_eq_x {P Q : points E} (hPnz : P ≠ 0) (hQnz : Q ≠ 0) (hx : P.x = Q.x)
(h' : P.y + Q.y + E.a1 * P.x + E.a3 ≠ 0) : P = Q :=
begin
  have hP := satisfies_equation_of_nonzero hPnz,
  have hy := eq_y_of_eq_x' hPnz hQnz hx h',
  cases P, tauto,
  cases Q, tauto,
  simp at *,
  tauto,
end

def is_two_torsion (P : points E) := P = 0 ∨ P.y + P.y + E.a1 * P.x + E.a3 = 0

@[simp] lemma is_order_two {P : points E} (h : P ≠ 0) (h' : is_two_torsion P)
: P.y + P.y + E.a1 * P.x + E.a3 = 0 :=
begin
  unfold is_two_torsion at h',
  cases h', contradiction,
  exact h',
end

@[simp] lemma is_order_two' {x y : K} {h : satisfies_equation E x y}
(h' : is_two_torsion (some x y h)) : y + y + E.a1 * x + E.a3 = 0 :=
begin
  unfold is_two_torsion at h',
  cases h', contradiction,
  exact h',
end

@[simp]
def add : points E → points E → points E
| zero           zero           := zero
| zero           (some x y h)   := some x y h
| (some x y h)   zero           := some x y h
| (some t₁ s₁ h₁) (some t₂ s₂ h₂) :=
if h : (t₁ = t₂) then
  --  `P₁=±P₂`. Let's deal with `P₁=-P₂` first
  if h' : s₁ + s₂ + E.a1 * t₁ + E.a3 = 0 then zero
  -- `P₁=P₂`
  else let l := (3*t₁*t₁+2*E.a2*t₁+E.a4 - E.a1*s₁)/(2*s₁+E.a1*t₁+E.a3) in
       let t₃ := l^2+E.a1*l-E.a2-2*t₁ in
  some t₃ (-E.a1 * t₃ - E.a3 - l * t₃ + l * t₁ - s₁)
  begin subst h, exact double_formula h₁ (by simpa [eq_y_of_eq_x h₁ h₂ h'] using h') end
else let l :=(s₁-s₂)/(t₁-t₂) in let m :=  s₁ - l * t₁ in let t₃ :=l*l+E.a1*l-E.a2-t₁-t₂ in
some t₃ (-E.a3 - E.a1 * t₃ - (l*t₃+m)) (neg_formula (add_neg_formula h h₁ h₂)) -- level 2; add

@[simp] def sub : points E → points E → points E := λ P Q, add P (neg Q)

instance : has_add (points E) := ⟨EllipticCurve.add⟩
instance : has_sub (points E) := ⟨EllipticCurve.sub⟩

@[simp] lemma points_add_def (P Q : points E) : P + Q = EllipticCurve.add P Q := rfl
@[simp] lemma points_sub_def (P Q : points E) : P - Q = EllipticCurve.sub P Q := rfl
@[simp] lemma points_neg_def (P : points E) : -P = EllipticCurve.neg P := rfl
@[simp] lemma tell_simplifier_to_use_numerals : (zero : points E) = 0 := rfl
@[simp] lemma add_zero (P : points E) : P + 0 = P := by {cases P; refl }
@[simp] lemma zero_add (P : points E) : 0 + P = P := by {cases P; refl }

@[simp] lemma neg_zero :  neg (0 : points E) = 0 := rfl

@[simp]
lemma sub_eq_add_neg (P Q : points E) : P - Q = P + (-Q) := rfl


lemma add_self_order_two (P : points E) (h : is_two_torsion P) : P + P = 0 :=
begin
  cases P, refl,
  simp [is_order_two' h],
end

@[simp]
lemma is_two_torsion_def (P : points E) : is_two_torsion P ↔ P + P = 0 :=
begin
  split,
  {
    exact add_self_order_two P,
  },
  {
    intro h,
    cases P,
    { left, refl },
    { right,
      simp [h],
      by_contradiction hc,
      simp [hc] at h,
      contradiction }
  }
end

@[simp]
lemma add_left_neg (P : points E) : add (neg P) P = 0 :=
begin
  cases P, refl,
  simp [show P_y + (-E.a3 - E.a1 * P_x - P_y) + E.a1 * P_x + E.a3 = 0, by ring],
end

@[simp]
lemma add_right_neg (P : points E) : add P (neg P) = 0 :=
begin
  cases P, refl,
  simp [show P_y + (-E.a3 - E.a1 * P_x - P_y) + E.a1 * P_x + E.a3 = 0, by ring],
end

@[simp]
lemma add_self_eq_zero_iff (P : points E) : P + P = 0 ↔ P = -P :=
begin
  split,
  {
    intro h,
    cases P, tauto,
    simp at ⊢,
    by_cases hc : P_y + P_y + E.a1 * P_x + E.a3 = 0,
    { rw [←sub_eq_zero, ←hc], ring },
    { simp [hc] at h, contradiction }
  },
  {
    intro h,
    nth_rewrite 0 h,
    simp,
  }
end


lemma add_comm : ∀ (P Q : points E), P + Q = Q + P
| zero           zero           := rfl
| (some a b hab) zero           := rfl
| zero           (some c d hcd) := rfl
| (some a b hab) (some c d hcd) :=
begin
  simp,
  by_cases h : a = c,
  {
    subst h,
    by_cases H : b + d + E.a1 * a + E.a3 = 0,
    {
      have H' : d + b + E.a1 * a + E.a3 = 0, by {rw ←H, ring,},
      simp [H, H'],
    },
    have H' : d + b + E.a1 * a + E.a3 ≠ 0, by { rw show d + b = b + d, by ring, exact H },
    simp [H, H'],
    have htt := eq_or_neg_of_eq_x hab hcd,
    cases htt,
    { subst htt, split;refl },
    subst htt,
    exfalso,
    apply H',
    ring,
  },
  have h' : c ≠ a := ne.symm h,
  simp only [h, h', dif_neg, not_false_iff],
  have h1 : (b - d) / (a - c) = (d - b) / (c - a), by
  rw [←neg_div_neg_eq, show -(b-d) = (d-b), by ring, show -(a-c) = (c-a), by ring],
  have hx : (b - d) / (a - c) * ((b - d) / (a - c)) + E.a1 * ((b - d) / (a - c)) - E.a2 - a - c =
  (d - b) / (c - a) * ((d - b) / (c - a)) + E.a1 * ((d - b) / (c - a)) - E.a2 - c - a,
  {
    field_simp [h, h'],
    rw show (a-c)*(a-c) = (c-a)*(c-a), by ring,
    rw show E.a1 * (b - d) / (a - c) = E.a1 * (d - b) / (c - a), by simp [h1, mul_div_assoc],
    ring,
  },
  split, exact hx,
  rw hx,
  simp only [h1, add_right_inj, sub_right_inj],
  rw ←sub_eq_zero,
  field_simp [sub_ne_zero.mpr h'],
  ring,
end

@[simp]
lemma add_eq_zero_iff (P Q : points E) : P + Q = 0 ↔ P = -Q :=
begin
  split,
  {
    intro h,
    cases P,
    {
      simp at h ⊢,
      subst h,
      exact neg_zero.symm,
    },
    cases Q,
    {
      simpa using h,
    },
    by_cases hPQ : P_x = Q_x,
    {
      subst hPQ,
      by_cases hPQ': P_y + Q_y + E.a1 * P_x + E.a3 = 0,
      {
        simp only [true_and, points_neg_def, eq_self_iff_true, neg_some],
        rw [←sub_eq_zero, ←hPQ'],
        ring,
      },
      simp [hPQ'] at h,
      contradiction,
    },
    simp [hPQ] at h,
    contradiction,
  },
  {
    intro h,
    subst h,
    rw add_comm,
    apply add_right_neg,
  }
end

lemma add_neq_zero_iff {P Q : points E} : P + Q ≠ 0 ↔ P ≠ -Q :=
begin
  split,
  {
    intros h hc,
    apply h,
    rw hc,
    simp,
  },
    {
    intros h hc,
    apply h,
    rw ←add_eq_zero_iff,
    exact hc,
  },
end
lemma points_is_in_E {P : points E} (h : P ≠ zero) :
P.y ^ 2 + E.a1 * P.x * P.y + E.a3 * P.y = P.x ^ 3 + E.a2 * P.x ^ 2 + E.a4 * P.x + E.a6 :=
begin
  cases P,tauto,
  exact P_h,
end

@[simp]
lemma add_self {x y : K}
(h : y ^ 2 + E.a1 * x * y + E.a3 * y = x ^ 3 + E.a2 * x ^ 2 + E.a4 * x + E.a6)
(h': y + y + E.a1 * x + E.a3 ≠ 0 ) : let l := (3*x*x+2*E.a2*x+E.a4 - E.a1*y)/(2*y+E.a1*x+E.a3) in
let t₃ := l^2+E.a1*l-E.a2-2*x in some x y h + some x y h = some t₃ (-E.a1 * t₃ - E.a3 - l * t₃ + l * x - y)
(double_formula h h') := by simp [h, h']

@[simp]
lemma add_self_zero {x y : K}
(h : y ^ 2 + E.a1 * x * y + E.a3 * y = x ^ 3 + E.a2 * x ^ 2 + E.a4 * x + E.a6)
(h': y + y + E.a1 * x + E.a3 = 0 ) : some x y h + some x y h = 0 := by simp [h']

@[simp]
lemma add_self' {P : points E} (h : P ≠ 0) (h' : P.y + P.y + E.a1 * P.x + E.a3 ≠ 0) :
let l := (3*P.x*P.x+2*E.a2*P.x+E.a4 - E.a1*P.y)/(2*P.y+E.a1*P.x+E.a3) in
let t₃ := l^2+E.a1*l-E.a2-2*P.x in
P + P = some t₃ (-E.a1 * t₃ - E.a3 - l * t₃ + l * P.x - P.y) (double_formula' h h') :=
begin
  cases P with Px Py hP H, tauto,
  simpa using add_self hP h',
end

@[simp]
lemma add_self_zero' {P : points E} (h : P ≠ 0)
(h': P.y + P.y + E.a1 * P.x + E.a3 = 0 ) :
P + P = 0 :=
begin
  cases P, tauto,
  apply add_self_zero,
  simpa using h',
end

lemma add_def_x  {t₁ t₂ s₁ s₂ : K} (h : t₁ ≠ t₂)
(h₁ : satisfies_equation E t₁ s₁) (h₂ : satisfies_equation E t₂ s₂)
: let l :=(s₁-s₂)/(t₁-t₂) in let m :=  s₁ - l * t₁ in
(some t₁ s₁ h₁ + some t₂ s₂ h₂).x = l*l+E.a1*l-E.a2-t₁-t₂ := by simp [h]

lemma add_def_y  {t₁ t₂ s₁ s₂ : K} (h : t₁ ≠ t₂)
(h₁ : satisfies_equation E t₁ s₁) (h₂ : satisfies_equation E t₂ s₂)
: let l :=(s₁-s₂)/(t₁-t₂) in let m :=  s₁ - l * t₁ in
let t₃ := l*l+E.a1*l-E.a2-t₁-t₂ in
(some t₁ s₁ h₁ + some t₂ s₂ h₂).y = (-E.a3 - E.a1 * t₃ - (l*t₃+m)) := by simp [h]

lemma add_def {t₁ t₂ s₁ s₂ : K} (h₁ h₂) (h : t₁ ≠ t₂) :
let l :=(s₁-s₂)/(t₁-t₂) in let m :=  s₁ - l * t₁ in let t₃ :=l*l+E.a1*l-E.a2-t₁-t₂ in
some t₁ s₁ h₁ + some t₂ s₂ h₂ =
some t₃ (-E.a3-E.a1*t₃-(l*t₃ + m)) (neg_formula (add_neg_formula h h₁ h₂)) :=
begin
  have h₁nz : some t₁ s₁ h₁ ≠ 0, by contradiction,
  have h₂nz : some t₂ s₂ h₂ ≠ 0, by contradiction,
  have h₃nz : some t₁ s₁ h₁ + some t₂ s₂ h₂ ≠ 0,
  {
    simp [h],
    apply some_ne_zero,
  },
  apply eq_of_eq_xy h₃nz some_ne_zero,
  apply add_def_x h,
  apply add_def_y h,
end

/-
Some preliminary lemmas
-/

lemma neg_unique (P Q R : points E) (hQ : P + Q = 0) (hR : P + R = 0) : Q = R :=
begin
  rw [add_comm, add_eq_zero_iff] at hQ hR,
  simp [hQ, hR],
end

@[simp]
lemma two_mul_eq_zero_iff (P : points E) (h : P ≠ 0) :
P + P = 0 ↔ P.y + P.y + E.a1 * P.x + E.a3 = 0 :=
begin
  split,
  {
    intro hP,
    rw points.has_add at hP,
    cases P, tauto,
    by_cases h' : P_y + P_y + E.a1 * P_x + E.a3 = 0,
    {
      exact h',
    },
    {
      simp [h'] at hP,
      contradiction,
    }
  },
  {
    intro hP,
    cases P, tauto,
    simp at hP,
    simp [hP],
  }
end

@[simp]
lemma eq_or_neg_of_eq_x' {P Q : points E} (h : P.x = Q.x) (hP : P ≠ 0) (hQ : Q ≠ 0) :
Q.y = P.y ∨ Q.y = -E.a1 * P.x - E.a3 - P.y :=
begin
  apply eq_or_neg_of_eq_x,
  exact satisfies_equation_of_nonzero hP,
  rw h,
  exact satisfies_equation_of_nonzero hQ,
end

@[simp]
lemma eq_or_neg_of_eq_x'' {P Q : points E} (h : P.x = Q.x) (hP : P ≠ 0) (hQ : Q ≠ 0) :
P = Q ∨ P = -Q :=
begin
  cases eq_or_neg_of_eq_x' h hP hQ,
  {
    left,
    exact eq_of_eq_xy hP hQ h (eq.symm h_1),
  },
  {
    right,
    rw points.has_neg,
    dsimp,
    cases Q, contradiction,
    simp at h_1,
    unfold neg,
    cases P, contradiction,
    simp at h h_1,
    simp [h, h_1],
    ring,
  }
end

@[simp]
lemma neg_of_eq_x {P Q : points E} (hP : P ≠ 0) (hQ : Q ≠ 0)
(hx : P.x = Q.x) (hy : Q.y = -E.a1 * P.x - E.a3 - P.y) :
P + Q = 0 :=
begin
  cases P, contradiction,
  cases Q, contradiction,
  simp at hx hy,
  have hh : P_y + Q_y + E.a1 * P_x + E.a3 = 0,
  by {rw hy, ring},
  simp [←hx, hh],
end

/-
We prove here all the results in 2.2 of https://arxiv.org/pdf/1710.00214.pdf
-/

lemma div_square_mul_eq_square_div {x y : K} (h : y ≠ 0) : (x / y)^2 * y = x^2 / y :=
begin
  rw show (x / y)^2 = x^2 / y^2,
  {
    field_simp [h],
    rw show (x/y)^2 * y^2 = (x/y*y)^2, by ring,
    congr,
    exact (eq_div_iff h).mp rfl,
  },
  field_simp [h],
  ring,
end

variables {P Q R : points E}

@[simp]
lemma neg_add'  : -(P+Q) = -P - Q :=
begin
  symmetry,
  cases P, {simp,},
  rw sub_eq_add_neg,
  cases Q, refl,
  by_cases hPQ : P_x = Q_x,
  {
    subst hPQ,
    cases (eq_or_neg_of_eq_x P_h Q_h),
    { -- case P = Q
      subst h,
      by_cases h : Q_y + Q_y + E.a1 * P_x + E.a3 = 0,
      {
        have h' : -E.a3 - E.a1 * P_x - Q_y + (-E.a3 - E.a1 * P_x - Q_y) + E.a1 * P_x + E.a3 = 0,
        { rw [←zero_eq_neg, ←h], ring },
        simp [h,h'],
      },
      {
        have h1 : -E.a3 - E.a1 * P_x - Q_y + (-E.a3 - E.a1 * P_x - Q_y) + E.a1 * P_x + E.a3
         = -(2 * Q_y + E.a1 * P_x + E.a3), by ring,
        have h' : -E.a3 - E.a1 * P_x - Q_y + (-E.a3 - E.a1 * P_x - Q_y) + E.a1 * P_x + E.a3 ≠ 0,
        { intro hc, apply h, rw ←zero_eq_neg at hc, rw hc, ring },
        simp [h, h', h1],
        set δ := (2 * Q_y + E.a1 * P_x + E.a3) with hδ,
        replace h : δ ≠ 0, by simpa [two_mul, hδ] using h,
        rw [show 2 * (-E.a3 - E.a1 * P_x - Q_y) + E.a1 * P_x + E.a3 = -δ,
            by {rw hδ, ring}, div_neg_eq_neg_div],
        split,
        {
          field_simp [h, div_square_mul_eq_square_div h],
          rw [←sub_eq_zero],
          repeat {rw ←hδ},
          field_simp [h],
          rw hδ,
          ring,
        },
        {
          rw ←sub_eq_zero,
          have hkey : (E.a1 * (δ - E.a1*P_x - E.a3 - 2*Q_y) *
          ((E.a2 + 3*P_x)*δ^2 + (E.a1^3*P_x + E.a1^2*E.a3 + 2*E.a1*E.a2*P_x +
           3*E.a1*P_x^2 + E.a1^2*Q_y + E.a1*E.a4)*δ - E.a1^4*P_x^2 - 2*E.a1^3*E.a3*P_x -
           6*E.a1^2*E.a2*P_x^2 - 9*E.a1^2*P_x^3 - E.a1^3*P_x*Q_y - E.a1^2*E.a3^2 -
           6*E.a1*E.a2*E.a3*P_x - 3*E.a1^2*E.a4*P_x - 12*E.a2^2*P_x^2 - 9*E.a1*E.a3*P_x^2 -
           36*E.a2*P_x^3 - 27*P_x^4 - E.a1^2*E.a3*Q_y - E.a1^2*Q_y^2 - 3*E.a1*E.a3*E.a4 -
           12*E.a2*E.a4*P_x - 18*E.a4*P_x^2 - 3*E.a4^2)) / δ^3 = 0,
          { rw hδ, ring },
          rw ←hkey,
          norm_num,
          field_simp [h, div_square_mul_eq_square_div h],
          ring,
        }
      }
    },
    { -- Case Q = -P
      subst h,
      have h' : -(E.a1 * P_x) - E.a3 + E.a1 * P_x + E.a3 = 0, by ring,
      have h'' : -E.a3 - E.a1 * P_x - P_y +
      (-E.a3 - E.a1 * P_x - (-(E.a1 * P_x) - E.a3 - P_y)) + E.a1 * P_x + E.a3 = 0, by ring,
      simp [h', h''],
    },
  },
  {
    simp [hPQ],
    replace hPQ : P_x - Q_x ≠ 0 := sub_ne_zero.mpr hPQ,
    split; { field_simp [hPQ], ring },
  }
end

lemma eq_neg_of_add_eq_sub (h1 : P ≠ -P) (h2 : P + Q = P - Q) : Q = -Q :=
begin
  by_cases h : P = Q,
  {
    subst h,
    rw ←add_eq_zero_iff,
    simpa using h2,
  },
  by_cases h' : P = -Q,
  {
    subst h',
    rw sub_eq_add_neg at h2,
    have H : -Q + Q = 0 := (add_eq_zero_iff (-Q) Q).mpr rfl,
    have H' : -Q + -Q = 0 := (rfl.congr H).mp (eq.symm h2),
    apply neg_unique (-Q) _ _ H H',
  },
  {
    cases P, tauto,
    cases Q, tauto,
    rw ←add_self_eq_zero_iff,
    have hPQx : P_x ≠ Q_x,
    {
      by_contradiction hc,
      subst hc,
      simp at h h' h1,
      have hc' := eq_or_neg_of_eq_x Q_h P_h,
      cases hc',
      {contradiction},
      { subst hc',
        apply h',
        ring }
    },
    have hPQx' : P_x - Q_x ≠ 0, by {intro hc, apply hPQx, rw ←sub_eq_zero, exact hc},
    simp [hPQx] at h2,
    cases h2 with h2x h2y,
    field_simp [hPQx'] at h2x,
    clear h2y,
    have hPy : 2*P_y + E.a1*P_x + E.a3 ≠ 0,
    {
      intro hc,
      simp [hc] at h1,
      apply h1,
      rw [←sub_eq_zero, ←hc],
      ring,
    },
    replace h2x : -(P_x - Q_x) * (E.a1*Q_x + E.a3 + 2*Q_y) * (2*P_y + E.a1*P_x + E.a3) = 0,
    {
      rw ←sub_eq_zero at h2x,
      rw ←h2x,
      ring,
    },
    have hkey : (Q_y + Q_y + E.a1 * Q_x + E.a3) = 0,
    {
      simp only [mul_eq_zero] at h2x,
      cases h2x,
      cases h2x,
      { rw neg_eq_zero at h2x,
        contradiction },
      { rw ←h2x,ring },
      { contradiction }
    },
    simp [hkey],
  }
end

-- This one needs computation, uses that curve is nonsingular!
lemma zero_unique' (h : P + Q = P) : Q = 0 :=
begin
  by_cases hP : P = 0, { subst hP, rw ←h, simp },
  by_cases hPQ1 : P = -Q,
  { subst hPQ1,
    simp at h,
    specialize hP (eq.symm h),
    contradiction },
  by_cases hPQ : P = Q,
  {
    subst hPQ,
    have : P + P ≠ 0,
    {
      sorry
    },
    cases P, tauto,
    simp only [true_and, points_neg_def, eq_self_iff_true, neg_some] at hPQ1,
    replace hPQ1 :  P_y + P_y + E.a1 * P_x + E.a3 ≠ 0,
    {
      intro hc,
      apply hPQ1,
      rw [←sub_eq_zero, ←hc],
      ring,
    },
    simp [hPQ1] at *,
    sorry
  },
  sorry
end

@[simp]
lemma zero_unique : P + Q = P ↔ Q = 0 :=
begin
  split,
  { exact zero_unique' },
  { intro h, simp [h] }
end


lemma add_sub_self_cancel (h1 : P ≠ -P) (h2 : P + P ≠ -P) : P + P - P = P :=
begin
  cases P, tauto,
  by_cases h : P_y + P_y + E.a1 * P_x + E.a3 = 0,
  {
    simp only [h, true_and, points_neg_def, add_self_zero,
    eq_self_iff_true, zero_add, sub_eq_add_neg, neg_some],
    rw [←sub_eq_zero, ←neg_eq_zero, ←h],
    ring },

  have hkey : -(E.a1 * P_x) - E.a3 - P_y + (-E.a3 - E.a1 * P_x - P_y) + E.a1 * P_x + E.a3 ≠ 0,
  {
    intro hc,
    apply h,
    rw ←neg_eq_zero,
    rw ←hc,
    ring,
  },
  -- Needs a calculation
  sorry
end

lemma two_eight (h : P + Q = -P) : Q = -P - P :=
begin
  -- Needs a calculation
  sorry
end

@[simp]
lemma add_left_cancel (P Q R : points E) : P + Q = P + R ↔ Q = R := -- lemma 2.9
begin
  split,
  {intro h,
  -- Needs a calculation
  sorry
  },
  { intro h,
    subst h }
end

@[simp]
lemma add_right_cancel (P Q R : points E) : P + R = Q + R ↔ P = Q := -- lemma 2.9 bis
begin
  rw show P + R = R + P, by rw add_comm,
  rw show Q + R = R + Q, by rw add_comm,
  apply add_left_cancel,
end

@[simp] lemma neg_eq_iff : -P = Q ↔ P = -Q := by simp

@[simp]
lemma add_sub_cancel (P Q : points E) : P + Q - Q = P := -- lemma 2.10
begin
  by_cases hPQ : P = -Q,
  {
    subst hPQ,
    simp,
  },
  by_cases hPQ' : P = Q,
  {
    subst hPQ',
    by_cases h' : P + P = -P,
    {
      rw h',
      replace h' := h'.symm,
      rw neg_eq_iff at h',
      nth_rewrite_rhs 0 h',
      rw neg_add',
    },
    apply add_sub_self_cancel hPQ h',
  },
  cases P, { cases Q; simp },
  cases Q,
  { simp },
  sorry
end

@[simp]
lemma sub_add_cancel : (P - Q) + Q = P :=
begin
  rw sub_eq_add_neg,
  nth_rewrite 1 ←neg_neg Q,
  change P + -Q + - (- Q) = P,
  rw ←sub_eq_add_neg (P+-Q),
  apply add_sub_cancel,
end

lemma add_eq_iff_eq_sub : P + Q = R ↔ P = R - Q := -- corollary 2.11
begin
  split,
  { intro h,
    have : Q = R - P,
    {
      rw ←add_sub_cancel Q P,
      rw add_comm at h,
      rw h,
    },
    rw this at h,
    rw [←add_left_cancel (R-P) P (R-Q), sub_add_cancel, ←this, add_comm, sub_add_cancel],
  },
  {
    intro h,
    subst h,
    exact sub_add_cancel,
  }
end

@[simp]
lemma sub_eq_zero (P Q : points E): P - Q = 0 ↔ P = Q :=
begin
  split,
  { intro h,
    symmetry,
    replace h := eq.symm h,
    rw ←add_eq_iff_eq_sub at h,
    simpa using h },
  { intro h,
    simp [h] }
end

/-
Here goes the main proof
-/

lemma assoc_aux { P Q R : points E} (hPz : P ≠ 0) (hQz : Q ≠ 0) (hRz : R ≠ 0)
(hPQ1 : P ≠ Q) (hPQ2 : P ≠ -Q) (hQR1 : Q ≠ R) (hQR2 : Q ≠ -R) (hPQR1 : P + Q ≠ R) (hPQR2 : P + Q ≠ -R)
(hQRP1 : Q + R ≠ P) (hQRP2 : Q + R ≠ -P) : P + Q + R = P + (Q + R) :=
begin
  sorry
end

lemma assoc_aux' {P Q : points E} (hPz : P ≠ 0) (hQz : Q ≠ 0) (hneg : P + P ≠ 0)
(hPQ1 : P ≠ Q) (hPQ2 : P ≠ -Q) (h2PQ1 : (P + P) ≠ Q) (h2PQ2 : (P + P) ≠ -Q)
(hPQP1 : P + Q ≠ P) (hPQP1 : P + Q ≠ -P) : P + P + Q = P + (P + Q) :=
begin
  sorry
end

lemma assoc_aux'' {P : points E} (hz : P ≠ 0) (hneg : P + P ≠ 0)
(htwo : (P + P) + (P + P) ≠ 0) (hPP1 : P + P ≠ P) (hPP2 : P + P ≠ -P)
(hPPP1 : P + P + P ≠ P) (hPPP2 : P + P + P ≠ -P) : (P + P) + (P + P) = P + (P + (P + P)) :=
begin
  sorry
end

lemma two_twelve
(h : ((P + Q ≠ R) ∧ (Q + R ≠ P)) ∨ P = 0 ∨ Q = 0 ∨ R = 0 ∨ P+Q = 0 ∨ Q+R = 0 ∨ P + Q + R = 0 ∨ P + (Q + R) = 0 ∨
P = Q ∨ Q = R ∨ P = R )
 : P + Q + R = P + (Q + R) :=
begin
  by_cases hPz : P = 0,
  {subst hPz, simp },
  by_cases hQz : Q = 0,
  {subst hQz, simp },
  by_cases hRz : R = 0,
  {subst hRz, simp },
  by_cases hPR1 : P = R,
  { subst hPR1,
    nth_rewrite 1 add_comm,
    nth_rewrite_rhs 0 add_comm },
  by_cases hPPR : P + Q = -R,
  { rw hPPR,
    rw [add_eq_iff_eq_sub, ←neg_add', add_comm] at hPPR,
    nth_rewrite 0 hPPR,
    simp },
  by_cases hQRP2 : Q + R = -P,
  { rw hQRP2,
    rw [add_eq_iff_eq_sub, ←neg_add', add_comm] at hQRP2,
    nth_rewrite 0 hQRP2,
    nth_rewrite 1 add_comm,
    rw [neg_add', sub_add_cancel],
    simp },
  by_cases hPR2 : P = -R,
  { replace hPR2 : R = -P := neg_eq_iff.mp (eq.symm hPR2),
    subst hPR2,
    rw [←sub_eq_add_neg, add_comm, add_sub_cancel, add_comm, ←sub_eq_add_neg, sub_add_cancel],
  },
  by_cases hPQ' : P = -Q,
  { replace hPQ' : Q = -P := neg_eq_iff.mp (eq.symm hPQ'),
    subst hPQ',
    nth_rewrite_rhs 0 add_comm,
    nth_rewrite_rhs 1 add_comm,
    nth_rewrite_rhs 0 ←sub_eq_add_neg,
    rw sub_add_cancel,
    simp },
  by_cases hQR' : Q = -R,
  { subst hQR',
    rw ←sub_eq_add_neg,
    rw sub_add_cancel,
    simp },
  by_cases hPQ : P + Q = 0,
  { simp only [hPQ, zero_add],
    rw add_comm at hPQ,
    have hPneg : Q = -P := (add_eq_zero_iff Q P).mp hPQ,
    rw hPneg,
    nth_rewrite 0 add_comm,
    nth_rewrite 1 add_comm,
    rw [←sub_eq_add_neg, sub_add_cancel] },
  by_cases hQR : Q + R = 0,
  { simp only [hQR, zero_add],
    have hQneg : Q = -R := (add_eq_zero_iff Q R).mp hQR,
    rw [hQneg, ←sub_eq_add_neg, sub_add_cancel],
    simp },
  -- end of first block of cases
  by_cases hPQ1 : P = Q,
  { subst hPQ1,
    by_cases hPPR' : R = P + P,
    { subst hPPR',
      replace hPPR : P + P + (P + P) ≠ 0 := add_neq_zero_iff.mpr hPPR,
      replace hPR1 : P + P ≠ P, by tauto,
      replace hQR' : P + P ≠ -P, by { rw [←add_neq_zero_iff, add_comm], exact hQR },
      have hP4 : P + P + P ≠ P,
      {
        intro hc,
        apply hPQ,
        nth_rewrite_rhs 0 ←(add_sub_cancel P P) at hc,
        rw sub_eq_add_neg at hc,
        rw add_left_cancel at hc,
        nth_rewrite_lhs 0 hc,
        simp,
      },
      rw add_comm at hQRP2,
      apply assoc_aux''; assumption },
    { replace hPPR' : P + P ≠ R := ne.symm hPPR',
      have hR' : P + R ≠ P,
      { by_contradiction hc,
        rw zero_unique at hc,
        contradiction },
      apply assoc_aux'; assumption } },
  by_cases hQR1 : Q = R,
  { clear h,
    subst hQR1,
    by_cases hPQQ' : P = Q + Q,
    {
      subst hPQQ',
      symmetry,
      nth_rewrite_rhs 0 add_comm,
      nth_rewrite_rhs 1 add_comm,
      replace hQRP2 :  Q + Q + (Q + Q) ≠ 0 := add_neq_zero_iff.mpr hQRP2,
      have htmp' : Q + Q + Q ≠ Q,
      { by_contradiction hc,
        apply hQR,
        rw [←add_left_cancel Q, add_comm, hc],
        simp },
      apply assoc_aux''; assumption,
    },
    {
      nth_rewrite_rhs 0 add_comm,
      nth_rewrite_lhs 0 add_comm,
      nth_rewrite_lhs 1 add_comm,
      symmetry,
      replace hPQ1 : Q ≠ P := ne.symm hPQ1,
      have htmp : Q ≠ -P,
      { apply ne.symm,
        by_contradiction hc,
        rw ←hc at hPQ',
        simpa using hPQ' },
      replace hPQQ' : Q + Q ≠ P := ne.symm hPQQ',
      have htmp : Q + P ≠ Q,
      { by_contradiction,
        apply hPz,
        rw [←add_left_cancel Q, h],
        simp },
      rw add_comm at hPPR,
      apply assoc_aux', all_goals {try{assumption}} },
  },
  have hPPR' := hPPR,
  rw ←add_eq_zero_iff at hPPR',
  have hQRP2' := hQRP2,
  rw [←add_eq_zero_iff, add_comm] at hQRP2',
  have h : P + Q ≠ R ∧ Q + R ≠ P, by tauto,
  apply assoc_aux hPz hQz hRz hPQ1 hPQ' hQR1 hQR' h.1 hPPR h.2 hQRP2,
end

lemma main_assoc' (h : P + Q = R) : P + Q + R = P + (Q + R) :=
begin
  by_cases h0 : ((P + Q ≠ R) ∧ (Q + R ≠ P)) ∨ P = 0 ∨ Q = 0 ∨ R = 0 ∨ P+Q = 0 ∨ Q+R = 0 ∨ P + Q + R = 0 ∨ P + (Q + R) = 0 ∨
P = Q ∨ Q = R ∨ P = R,
  { exact two_twelve h0 },
  push_neg at h0,
  rw ←h,
  by_cases H : (P+Q)+(P+Q) = -P,
  {
    have hkey : P + Q = -Q + (-P - P),
    {
      calc P + Q = (-Q-P)-P : by {
        rw add_eq_iff_eq_sub at H,
        rw H,
        repeat {rw ←neg_add'},
        nth_rewrite_rhs 0  add_comm,
        nth_rewrite_rhs 1  add_comm,
      }
      ... = -Q + (-P - P) : by {
        repeat {rw sub_eq_add_neg},
        symmetry,
        rw add_comm,
        nth_rewrite_rhs 1 add_comm,
        nth_rewrite_rhs 0 add_comm,
        apply two_twelve,
        right, right, right, right, right, right, right, right, left, refl,
      }
    },
    calc (P + Q) + (P + Q) = -P : H
    ... = P + (-P - P) : by {
      apply (add_left_cancel (P + P) _ _).mp,
      rw [←sub_eq_add_neg, add_sub_cancel, ←neg_add'],
      nth_rewrite_rhs 0 add_comm,
      rw [←sub_eq_add_neg, sub_add_cancel],
    }
    ... = P + (Q + (-Q + (-P - P))) : by {
      nth_rewrite_rhs 2 add_comm,
      rw ←sub_eq_add_neg,
      nth_rewrite_rhs 1 add_comm,
      rw sub_add_cancel,
    }
    ... = P + (Q + (P + Q)) : by {rw hkey}
  },
  { -- (P + Q) + (P + Q) ≠ - P
    suffices : (P + Q + (P + Q)) + -P = (P + (Q + (P + Q))) + -P,
    { rw add_right_cancel at this, exact this },
    calc
    ((P + Q) + (P + Q)) + -P = (P + Q) + ((P + Q) + -P) :
    by { apply two_twelve, right, right, right, right, right, right, right, right, left, refl }
    ... = (P + Q) + (P + Q - P) : by rw sub_eq_add_neg
    ... = (P + Q) + (Q + P - P) : by rw add_comm Q P
    ... = (P + Q) + Q  : by rw add_sub_cancel
    ... = Q + (P + Q) : by rw add_comm
    ... = Q + (P + Q) + P - P : by rw add_sub_cancel
    ... = (P + (Q + (P + Q))) - P : by rw add_comm (Q + (P + Q))
    ... = (P + (Q + (P + Q))) + -P : by rw sub_eq_add_neg
  }
end

lemma add_assoc : ∀ P Q R : points E, P + Q + R = P + (Q + R) :=
begin
  intros,
  by_cases h0 : ((P + Q ≠ R) ∧ (Q + R ≠ P))
    ∨ P = 0 ∨ Q = 0 ∨ R = 0
    ∨ P+Q = 0 ∨ Q+R = 0
    ∨ P + Q + R = 0 ∨ P + (Q + R) = 0 ∨ P = Q ∨ Q = R ∨ P = R, { exact two_twelve h0 },
  by_cases h1 : P + Q = R, { exact main_assoc' h1 },
  have h : Q + R = P, by {simp at h0, tauto},
  rw ←h,
  symmetry,
  nth_rewrite_lhs 1 add_comm,
  nth_rewrite_lhs 2 add_comm,
  nth_rewrite_rhs 0 add_comm,
  nth_rewrite_rhs 1 add_comm,
  nth_rewrite_rhs 2 add_comm,
  apply main_assoc', refl,
end

instance : add_comm_group (points E) := {
  add := EllipticCurve.add,
  add_assoc := add_assoc,
  zero := zero,
  zero_add := λ P, by {cases P; refl},
  add_zero := λ P, by {cases P; refl},
  nsmul := nsmul_rec,
  nsmul_zero' := λ P, rfl,
  nsmul_succ' := λ n P, rfl,
  neg := EllipticCurve.neg,
  sub := EllipticCurve.sub,
  sub_eq_add_neg := λ P Q, rfl,
  zsmul := zsmul_rec,
  zsmul_zero' := λ P, rfl,
  zsmul_succ' := λ n P, rfl,
  zsmul_neg' := λ n P, rfl,
  add_left_neg := add_left_neg,
  add_comm := add_comm }

end EllipticCurve
