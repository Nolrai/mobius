/-
Copyright (c) 2020 Christopher A. Upshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Christopher A. Upshaw.
-/

import algebra
import data.quot

universe u

/--
# The theory of wheels
As described at https://en.wikipedia.org/wiki/Wheel_theory.

The core idea is alow division by zero by weaking the notion of mutiplicative inverse.
-/

class wheel (w : Type u) extends add_comm_monoid w, comm_monoid w, has_inv w, has_bot w :=
(inv_inv : ∀ x : w, x⁻¹⁻¹ = x)
(mul_inv : ∀ x y : w, (x * y) ⁻¹ = x⁻¹ * y⁻¹)
(add_mul_add_zero_mul : ∀ x y z : w, (x + y) * z + 0 * z = x * z + y * z)
(add_mul_mul_inv : ∀ x y z : w, (x + y * z) * y⁻¹ = x * y⁻¹ + z + 0 * y)
(zero_mul_zero : (0 * 0 : w) = 0)
(add_zero_mul_mul : ∀ x y z : w, (x + 0 * y) * z = x * z + 0 * y)
(zero_mul_zero_inv : (0 * 0⁻¹ : w) = ⊥)
(bot_add : ∀ x : w, ⊥ + x = ⊥)

/--
 If there exists an x s.t. 1 + x = 0, then we can also introduce a subtraction.
 Note however that x - x = 0 is only true when 0 * x * x = 0, i.e. 'finite' values of the wheel.
-/

class sub_wheel (w : Type u) extends wheel w, has_sub w :=
(one_sub_one : (1 - 1 : w) = 0)
(zero_sub : ∀ x : w, 0 - x = (0 - 1) * x )

namespace fraction_wheel

variables (w : Type) [comm_ring w] (s : submonoid w)

/-- Every comm_ring can be extened to a wheel by taking ratios, and quotienting by a multiplicative submonoid (which needs to not include zero for the construction to be non-trivial.) Usually one takes the submonoid of all nonzero values, this gets you the extended rationals from the integers for example. -/

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

def pre_add (x y : w × w) : w × w := (x.1 * y.2 + x.2 * y.1, x.2 * y.2)

local infix `++` := λ x y, pre_add w x y

lemma pre_add_assoc [comm_ring w] (x y z : w × w) : x ++ y ++ z = x ++ (y ++ z) :=
prod.ext
(calc (x.1 * y.2 + x.2 * y.1) * z.2            + x.2 * y.2 * z.1
    = x.1 * y.2 * z.2   +  x.2 * y.1 * z.2     + x.2 * y.2 * z.1    : by rw add_mul
... = x.1 * (y.2 * z.2) +  x.2 * y.1 * z.2     + x.2 * y.2 * z.1    : by rw mul_assoc
... = x.1 * (y.2 * z.2) + (x.2 * y.1 * z.2     + x.2 * y.2 * z.1)   : by rw add_assoc
... = x.1 * (y.2 * z.2) + (x.2 * (y.1 * z.2)   + x.2 * (y.2 * z.1)) : by rw [mul_assoc, mul_assoc]
... = x.1 * (y.2 * z.2) +  x.2 * (y.1 * z.2 + y.2 * z.1)            : by rw mul_add)
(mul_assoc _ _ _)

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

local infix `+'`:65 := add w s

@[simp] def of (x : w) : fraction_wheel w s :=
quotient.mk' (x, 1)

instance : has_coe w (fraction_wheel w s) :=
⟨of w s⟩

instance : has_zero (fraction_wheel w s) :=
⟨(0 : w)⟩

lemma zero_add (x) : 0 +' x = x :=
quotient.induction_on' x $ λ x, congr_arg quotient.mk' $ show (_, _) = _, from prod.ext
  (show 0 * x.2 + 1 * x.1 = x.1, by rw [zero_mul, one_mul, zero_add])
  (one_mul _)

-- arugments before colon
lemma add_comm (x y) : x +' y = y +' x :=
quotient.induction_on₂' x y $ λ x y, congr_arg quotient.mk' $ show (_, _) = (_, _), from prod.ext
  (show _ + _ = _ + _, by rw [mul_comm x.1, mul_comm x.2, add_comm])
  (mul_comm _ _)

lemma add_zero (x) : x +' 0 = x :=
by rw [add_comm, zero_add]

lemma add_assoc (x y z) : x +' y +' z = x +' (y +' z) :=
quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $ pre_add_assoc _ _ _ _

instance : has_one (fraction_wheel w s) :=
⟨(1 : w)⟩

instance : add_comm_monoid (fraction_wheel w s) :=
{ add := add w s,
  add_assoc := add_assoc w s,
  zero := 0,
  zero_add := zero_add w s,
  add_zero := add_zero w s,
  add_comm := add_comm w s }

def pre_mul [comm_ring w] (x y : w×w) : w×w
  := ⟨x.1 * y.1, x.2 * y.2⟩

local infix `**`:60 := pre_mul w

lemma pre_mul_assoc [comm_ring w] (x y z: w×w)
  : x ** y ** z = x ** (y ** z) :=
  show (_, _) = (_, _), from prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)

def mul : fraction_wheel w s → fraction_wheel w s → fraction_wheel w s :=
quotient.map₂' (pre_mul w) $
begin
  intros x₀ x₁ x y₀ y₁ y, obtain := x, obtain := y,
  use [x_sl * y_sl, x_sr * y_sr, s.mul_mem ‹_› ‹_›, s.mul_mem ‹_› ‹_›],
  all_goals
    { obtain := x₀, obtain := y₀, obtain := x₁, obtain := y₁, unfold pre_mul; dsimp only [] },
  {    calc x_sl * y_sl * (x₀_fst * y₀_fst) = x_sl * x₀_fst * (y_sl * y₀_fst) : mul_rearange _ _ _ _
    ... = x_sr * x₁_fst * (y_sl * y₀_fst) : by {rw x_fst_eq}
    ... = x_sr * x₁_fst * (y_sr * y₁_fst) : by {rw y_fst_eq}
    ... = x_sr * y_sr * (x₁_fst * y₁_fst) : mul_rearange _ _ _ _,},
  {    calc x_sl * y_sl * (x₀_snd * y₀_snd) = x_sl * x₀_snd * (y_sl * y₀_snd) : mul_rearange _ _ _ _
    ... = x_sr * x₁_snd * (y_sl * y₀_snd) : by {rw x_snd_eq}
    ... = x_sr * x₁_snd * (y_sr * y₁_snd) : by {rw y_snd_eq}
    ... = x_sr * y_sr * (x₁_snd * y₁_snd) : mul_rearange _ _ _ _,}
end

local infix `*'`:60 := mul w s

lemma one_mul (x) : 1 *' x = x :=
quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  show (_, _) = _, from prod.ext (one_mul _) (one_mul _)

lemma mul_one (x) : x *' 1 = x :=
  quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  show (_, _) = _, from prod.ext (mul_one _) (mul_one _)

lemma mul_comm (x y) : x *' y = y *' x :=
  quotient.induction_on₂' x y $ λ x y, congr_arg quotient.mk' $
  show (_, _) = (_, _), from prod.ext (mul_comm _ _) (mul_comm _ _)

lemma mul_assoc (x y z) : x *' y *' z = x *' (y *' z) :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  pre_mul_assoc _ _ _ _

instance : comm_monoid (fraction_wheel w s) :=
{ mul := mul w s,
  mul_assoc := mul_assoc w s,
  one := has_one.one,
  one_mul := one_mul w s,
  mul_one := mul_one w s,
  mul_comm := mul_comm w s }

def pre_inv (x : w×w) : w×w := ⟨x.2, x.1⟩

lemma pre_inv_inv : ∀ x, pre_inv w (pre_inv w x) = x
| ⟨l, r⟩ := rfl

def inv : fraction_wheel w s -> fraction_wheel w s :=
  quotient.map' (pre_inv w) $
  begin
  intros x₀ x₁ x, obtain := x₀; obtain := x₁; obtain := x,
  use [x_sl, x_sr]; assumption
  end

instance : has_inv (fraction_wheel w s) := ⟨inv w s⟩

lemma inv_inv (x : fraction_wheel w s) : (x⁻¹)⁻¹ = x :=
  quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  begin
  unfold pre_inv,
  apply prod.ext; dsimp only [prod.fst, prod.snd]; refl
  end

lemma mul_inv (x y : fraction_wheel w s) : (x * y)⁻¹ = (x⁻¹) * (y⁻¹) :=
  quotient.induction_on₂' x y $ λ x y, congr_arg quotient.mk' rfl

instance : has_bot (fraction_wheel w s) :=
  ⟨quotient.mk' ⟨0,0⟩ ⟩

lemma bot_add (x : fraction_wheel w s) : ⊥ + x = ⊥ :=
  quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  begin
  unfold pre_add;
  apply prod.ext;
  norm_num
  end

lemma add_mul_add_zero_mul
  (x y z : fraction_wheel w s) : (x + y) * z + 0 * z = x * z + y * z :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  apply prod.ext; norm_num; ring,
  end

lemma add_mul_mul_inv
  (x y z : fraction_wheel w s) : (x + y * z) * (y⁻¹) = x * (y⁻¹) + z + 0 * y :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  apply prod.ext; norm_num; ring,
  end

lemma zero_mul_zero : (0 * 0 : fraction_wheel w s) = 0 :=
  congr_arg quotient.mk' $
  begin
  unfold pre_mul,
  apply prod.ext; dsimp,
  refine mul_zero _,
  ring,
  end

lemma add_zero_mul_mul
  (x y z : fraction_wheel w s) : (x + 0 * y) * z = x * z + 0 * y :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  apply prod.ext; norm_num; ring,
  end

lemma zero_mul_zero_inv : (0 : fraction_wheel w s) * (0⁻¹) = ⊥ :=
 congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul pre_inv,
  apply prod.ext; norm_num,
  end

instance : inhabited (fraction_wheel w s) := ⟨1⟩

instance : wheel (fraction_wheel w s) :=
{ inv := inv w s,
  inv_inv := inv_inv w s,
  mul_inv := mul_inv w s,
  add_mul_add_zero_mul := add_mul_add_zero_mul w s,
  add_mul_mul_inv := add_mul_mul_inv w s,
  zero_mul_zero := zero_mul_zero w s,
  add_zero_mul_mul := add_zero_mul_mul w s,
  zero_mul_zero_inv := zero_mul_zero_inv w s,
  bot_add := bot_add w s }

end fraction_wheel