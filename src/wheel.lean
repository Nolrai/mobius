/-
Copyright (c) 2020 Christopher A. Upshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Christopher A. Upshaw.
-/

import algebra
import data.quot

/-!
# The theory of wheels
As described at https://en.wikipedia.org/wiki/Wheel_theory.
-/

universe u

class wheel (w : Type u) extends add_comm_monoid w, comm_monoid w, has_inv w, has_bot w :=
(inv_inv : ∀ x : w, x⁻¹⁻¹ = x)
(mul_inv : ∀ x y : w, (x * y) ⁻¹ = x⁻¹ * y⁻¹)
(add_mul_add_zero_mul : ∀ x y z : w, (x + y) * z + 0 * z = x * z + y * z)
(add_mul_mul_inv : ∀ x y z : w, (x + y * z) * y⁻¹ = x * y⁻¹ + z + 0 * y)
(zero_mul_zero : (0 * 0 : w) = 0)
(add_zero_mul_mul : ∀ x y z : w, (x + 0 * y) * z = x * z + 0 * y)
(zero_mul_zero_inv : (0 * 0⁻¹ : w) = ⊥)
(bot_add : ∀ x : w, ⊥ + x = ⊥)

class sub_wheel (w : Type u) extends wheel w, has_sub w :=
(one_sub_one : (1 - 1 : w) = 0)
(zero_sub : ∀ x : w, 0 - x = (0 - 1) * x )

namespace fraction_wheel
/- Every comm_ring can be extened to a wheel by taking ratios, and quotienting by a multiplicative submonoid (which needs to not include zero for the construction to be non-trivial.) Usually one takes the submonoid of all nonzero values, this gets you the extended rationals from the integers for example. -/

variables (w : Type) [comm_ring w] (s : submonoid w)

inductive fraction_equiv (l r : w × w) : Prop
| intro : ∀ (sl sr : w) (sl_in_s : sl ∈ s) (sr_in_s : sr ∈ s),
    ∀ (fst_eq : sl * l.fst = sr * r.fst) (snd_eq : sl * l.snd = sr * r.snd),
    fraction_equiv

open fraction_equiv

lemma is_reflexive : reflexive (fraction_equiv w s) :=
λ x, ⟨1, 1, s.one_mem, s.one_mem, rfl, rfl⟩

lemma is_symmetric : symmetric (fraction_equiv w s)
| x y ⟨sl, sr, sl_h, sr_h, fst_eq, snd_eq⟩ := ⟨sr, sl, sr_h, sl_h, fst_eq.symm, snd_eq.symm⟩

lemma is_transitive : transitive (fraction_equiv w s)
| x y z ⟨s1, s2, hs1, hs2, hs3, hs4⟩ ⟨t1, t2, ht1, ht2, ht3, ht4⟩ :=
    ⟨s1 * t1, s2 * t2, s.mul_mem hs1 ht1, s.mul_mem hs2 ht2,
      by rw [mul_right_comm, hs3, mul_right_comm, mul_assoc, ht3, mul_assoc],
      by rw [mul_right_comm, hs4, mul_right_comm, mul_assoc, ht4, mul_assoc]⟩

lemma is_equivalence : equivalence (fraction_equiv w s) :=
⟨is_reflexive w s, is_symmetric w s, is_transitive w s⟩

def fraction_setoid : setoid (w × w) :=
{ r := fraction_equiv w s, iseqv := is_equivalence w s }

def fraction_wheel (w : Type) [comm_ring w] (s : submonoid w) : Type :=
quotient (fraction_setoid w s)

open wheel

def pre_add (x y : w × w) : w × w :=
(x.1 * y.2 + x.2 * y.1, x.2 * y.2)

lemma pre_add_assoc [comm_ring w] (x y z : w × w) : x ++ y ++ z = x ++ (y ++ z) :=
prod.ext
(calc (x.1 * y.2 + x.2 * y.1) * z.2            + x.2 * y.2 * z.1
    = x.1 * y.2 * z.2   +  x.2 * y.1 * z.2     + x.2 * y.2 * z.1    : by rw add_mul
... = x.1 * (y.2 * z.2) +  x.2 * y.1 * z.2     + x.2 * y.2 * z.1    : by rw mul_assoc
... = x.1 * (y.2 * z.2) + (x.2 * y.1 * z.2     + x.2 * y.2 * z.1)   : by rw add_assoc
... = x.1 * (y.2 * z.2) + (x.2 * (y.1 * z.2)   + x.2 * (y.2 * z.1)) : by rw [mul_assoc, mul_assoc]
... = x.1 * (y.2 * z.2) +  x.2 * (y.1 * z.2 + y.2 * z.1)            : by rw mul_add)
(mul_assoc _ _ _)

local infix `++`:65 := λ x y, pre_add w x y

variables {w}
lemma mul_rearange (a b c d : w) : a * b * (c * d) = a * c * (b * d) :=
by simp_rw [mul_assoc, mul_left_comm b]
variables (w)

def add : fraction_wheel w s → fraction_wheel w s → fraction_wheel w s :=
quotient.map₂' (pre_add w) begin
  intros x₀ x₁ x y₀ y₁ y, cases x, cases y,
  use [x_sl * y_sl, x_sr * y_sr, s.mul_mem ‹_› ‹_›, s.mul_mem ‹_› ‹_›], --use `use`
  -- space after opening curly bracket
  { dsimp only [pre_add], repeat { rw left_distrib }, congr' 1,
    calc  x_sl * y_sl * (x₀.1 * y₀.2) = x_sl * x₀.1 * (y_sl * y₀.2) : mul_rearange _ _ _ _
    ... = x_sr * x₁.1 * (y_sl * y₀.2) : by rw x_fst_eq
    ... = x_sr * x₁.1 * (y_sr * y₁.2) : by rw y_snd_eq
    ... = x_sr * y_sr * (x₁.1 * y₁.2) : mul_rearange _ _ _ _,
    calc  x_sl * y_sl * (x₀.2 * y₀.1) = x_sl * x₀.2 * (y_sl * y₀.1) : mul_rearange _ _ _ _
    ... = x_sr * x₁.2 * (y_sl * y₀.1) : by rw x_snd_eq
    ... = x_sr * x₁.2 * (y_sr * y₁.1) : by rw y_fst_eq
    ... = x_sr * y_sr * (x₁.2 * y₁.1) : mul_rearange _ _ _ _ }, --closing curly bracket on the same line
  { calc  x_sl * y_sl * (x₀.2 * y₀.2) = x_sl * x₀.2 * (y_sl * y₀.2) : mul_rearange _ _ _ _
    ... = x_sr * x₁.2 * (y_sl * y₀.2) : by {rw x_snd_eq}
    ... = x_sr * x₁.2 * (y_sr * y₁.2) : by {rw y_snd_eq}
    ... = x_sr * y_sr * (x₁.2 * y₁.2) : mul_rearange _ _ _ _ },
end

local notation `add'` := add w s

@[simp] def of (x : w) : fraction_wheel w s :=
quotient.mk' (x, 1) -- spaces

instance : has_coe w (fraction_wheel w s) :=
⟨of w s⟩

instance : has_zero (fraction_wheel w s) :=
⟨(0 : w)⟩

-- extra brackets
lemma zero_add (x) : add' 0 x = x :=
quotient.induction_on' x $ λ x, congr_arg quotient.mk' $ show (_, _) = _, from prod.ext
  (show 0 * x.2 + 1 * x.1 = x.1, by rw [zero_mul, one_mul, zero_add])
  (one_mul _)

-- arugments before colon
lemma add_comm (x y) : add' x y = add' y x :=
quotient.induction_on₂' x y $ λ x y, congr_arg quotient.mk' $ show (_, _) = (_, _), from prod.ext
  (show _ + _ = _ + _, by rw [mul_comm x.1, mul_comm x.2, add_comm])
  (mul_comm _ _)

-- use zero_add by moving add_comm before this
lemma add_zero (x) : add' x 0 = x :=
by rw [add_comm, zero_add]

-- use pre_add_assoc
lemma add_assoc (x y z) : add' (add' x y) z = add' x (add' y z) :=
quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $ pre_add_assoc _ _ _ _

instance : has_one (fraction_wheel w s) :=
⟨(1 : w)⟩

-- use auto name
instance : add_comm_monoid (fraction_wheel w s) :=
{ add := add',
  add_assoc := add_assoc w s,
  zero := 0,
  zero_add := zero_add w s,
  add_zero := add_zero w s,
  add_comm := add_comm w s }

def raw_mul [comm_ring w]
  : w×w -> w×w -> w×w
| ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ := ⟨x₁ * y₁, x₂ * y₂⟩

def mul : fraction_wheel w s → fraction_wheel w s → fraction_wheel w s :=
quotient.map₂' (raw_mul w) $
begin
  intros x₀ x₁ x y₀ y₁ y,
  induction x; induction y,
  apply (fraction_equiv.intro (x_sl * y_sl) (x_sr * y_sr)),
  refine submonoid.mul_mem s _ _; assumption,
  refine submonoid.mul_mem s _ _; assumption,
  all_goals {cases x₀; cases y₀; cases x₁; cases y₁; unfold raw_mul; simp only []},
  {    calc x_sl * y_sl * (x₀_fst * y₀_fst) = x_sl * x₀_fst * (y_sl * y₀_fst) : mul_rearange _ _ _ _
    ... = x_sr * x₁_fst * (y_sl * y₀_fst) : by {rw x_fst_eq}
    ... = x_sr * x₁_fst * (y_sr * y₁_fst) : by {rw y_fst_eq}
    ... = x_sr * y_sr * (x₁_fst * y₁_fst) : mul_rearange _ _ _ _,},
  {    calc x_sl * y_sl * (x₀_snd * y₀_snd) = x_sl * x₀_snd * (y_sl * y₀_snd) : mul_rearange _ _ _ _
    ... = x_sr * x₁_snd * (y_sl * y₀_snd) : by {rw x_snd_eq}
    ... = x_sr * x₁_snd * (y_sr * y₁_snd) : by {rw y_snd_eq}
    ... = x_sr * y_sr * (x₁_snd * y₁_snd) : mul_rearange _ _ _ _,}
end

local infix `**`:60 := mul w s

lemma one_mul : ∀ x, 1 ** x = x :=
begin
  intros,
  unfold mul,
  unfold1 has_one.one,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  rw quotient.map₂'_mk',
  apply quotient.induction_on' x, clear x, intros x,
  rw quotient.map'_mk',
  apply congr_arg,
  cases x,
  unfold raw_mul,
  norm_num,
end

lemma mul_one :
  ∀ x, x ** 1 = x :=
  begin
  intros,
  unfold mul,
  apply quotient.induction_on' x, clear x, intros x,
  rw quotient.map₂'_mk',
  unfold1 has_one.one,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  rw quotient.map'_mk',
  apply congr_arg,
  cases x,
  unfold raw_mul,
  norm_num
  end

lemma mul_comm : ∀ x y, x ** y = (y ** x) :=
  begin
  intros,
  unfold mul,
  apply quotient.induction_on₂' x y, clear x y, intros x y,
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  cases x, cases y,
  unfold raw_mul,
  apply congr_arg,
  apply congr_arg2; ring,
  end

lemma mul_assoc : ∀ x y z, x ** y ** z = x ** (y ** z) :=
  begin
  intros,
  unfold mul,
  apply quotient.induction_on₃' x y z, clear x y z, intros x y z,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  apply congr_arg,
  cases x, cases y, cases z,
  unfold raw_mul,
  apply congr_arg2; ring,
  end

instance fraction_wheel_is_comm_monoid : comm_monoid (fraction_wheel w s) :=
{ mul := mul w s,
  mul_assoc := mul_assoc w s,
  one := has_one.one,
  one_mul := one_mul w s,
  mul_one := mul_one w s,
  mul_comm := mul_comm w s }

def raw_inv : w×w -> w×w
| ⟨l, r⟩ := ⟨r, l⟩

lemma raw_inv_involution : ∀ x, raw_inv w (raw_inv w x) = x
| ⟨l, r⟩ := rfl

def inv : fraction_wheel w s -> fraction_wheel w s :=
  quotient.map' (raw_inv w) $
  begin
  intros x₀ x₁ x,
  cases x₀; cases x₁; cases x,
  apply intro x_sl x_sr ; assumption
  end

local postfix  `ᵃ`:60 := inv w s

lemma inv_involution : ∀ x : fraction_wheel w s, (xᵃ)ᵃ = x :=
  begin
  intros,
  unfold inv,
  apply quotient.induction_on' x,
  clear x; intros x; cases x,
  rw [quotient.map'_mk', quotient.map'_mk'],
  unfold raw_inv,
  end

lemma inv_swap_mul : ∀ x y : fraction_wheel w s, (x * y)ᵃ = (xᵃ) * (yᵃ) :=
  begin
  intros,
  unfold inv,
  apply quotient.induction_on₂' x y,
  clear x y; intros x y; cases x; cases y,
  repeat {rw quotient.map₂'_mk'},
  unfold has_mul.mul semigroup.mul monoid.mul comm_monoid.mul mul,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  unfold raw_mul raw_inv,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  unfold raw_mul,
  end

instance has_bot : has_bot (fraction_wheel w s) := ⟨quotient.mk' ⟨0,0⟩ ⟩

lemma bot_absorbsive : ∀ (x : fraction_wheel w s), ⊥ + x = ⊥ :=
  begin
  intros,
  unfold has_add.add add_semigroup.add add_monoid.add add_comm_monoid.add add,
  unfold has_bot.bot,
  apply quotient.induction_on' x,
  clear x, intro x, cases x,
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  unfold raw_add,
  rw [zero_mul, zero_mul, ring.zero_add],
  end

lemma left_distrib
  : ∀ (x y z : fraction_wheel w s),
    (x + y) * z + 0 * z = x * z + y * z :=
  begin
  intros x y z,
  apply quotient.induction_on₃' x y z,
  unfold has_mul.mul semigroup.mul monoid.mul comm_monoid.mul mul,
  unfold has_add.add add_semigroup.add add_monoid.add add_comm_monoid.add add,
  unfold1 has_zero.zero,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  clear x y z, intros x y z, cases x, cases y, cases z,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  repeat {rw quotient.map₂'_mk'},
  unfold raw_add raw_mul,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  unfold raw_add raw_mul,
  apply congr_arg,
  apply congr_arg2; ring
  end

lemma left_distrib_cancel
  : ∀ (x y z : fraction_wheel w s),
  (x + y * z) * (yᵃ) = x * (yᵃ) + z + 0 * y :=
  begin
  intros x y z,
  apply quotient.induction_on₃' x y z,
  unfold has_mul.mul semigroup.mul monoid.mul comm_monoid.mul mul,
  unfold has_add.add add_semigroup.add add_monoid.add add_comm_monoid.add add,
  unfold inv,
  unfold1 has_zero.zero,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  clear x y z, intros x y z, cases x, cases y, cases z,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  unfold raw_add raw_mul raw_inv,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  apply congr_arg, apply congr_arg2,
  ring,
  norm_num,
  ring,
  end

lemma zero_mul_zero : 0 * 0 = (0 : fraction_wheel w s) :=
  begin
  unfold has_mul.mul semigroup.mul monoid.mul comm_monoid.mul mul,
  unfold1 has_zero.zero,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  unfold raw_mul,
  apply congr_arg, apply congr_arg2; ring
  end

lemma pull_out_zero
  : ∀ (x y z : fraction_wheel w s),
  (x + 0 * y) * z = x * z + 0 * y :=
  begin
  intros x y z,
  apply quotient.induction_on₃' x y z,
  unfold has_mul.mul semigroup.mul monoid.mul comm_monoid.mul mul,
  unfold has_add.add add_semigroup.add add_monoid.add add_comm_monoid.add add,
  unfold1 has_zero.zero,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  clear x y z, intros x y z, cases x, cases y, cases z,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  apply congr_arg,
  unfold raw_add raw_mul,
  norm_num, split; ring,
end

lemma bot_def : (0 : fraction_wheel w s) * (0ᵃ) = ⊥ :=
begin
unfold1 has_zero.zero,
unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
unfold has_bot.bot,
unfold has_mul.mul semigroup.mul monoid.mul comm_monoid.mul mul,
rw quotient.map₂'_mk',
unfold inv,
rw quotient.map'_mk',
unfold raw_inv,
rw quotient.map'_mk',
unfold raw_mul,
apply congr_arg,
norm_num,
end

instance inhabited : inhabited (fraction_wheel w s) := ⟨1⟩

instance fraction_wheel_is_wheel : wheel (fraction_wheel w s) :=
{ inv := inv w s,
  inv_involution := inv_involution w s,
  inv_swap_mul := inv_swap_mul w s,
  left_distrib := left_distrib w s,
  left_distrib_cancel := left_distrib_cancel w s,
  zero_mul_zero := zero_mul_zero w s,
  pull_out_zero := pull_out_zero w s,
  bot_def := bot_def w s,
  bot_absorbsive := bot_absorbsive w s }

end fraction_wheel

#lint