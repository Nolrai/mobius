-- as described at https://en.wikipedia.org/wiki/Wheel_theory

import algebra
import data.quot

universe u

namespace wheel
variables (w : Type u)

class wheel extends add_comm_monoid w, comm_monoid w, has_sub w, has_inv w :=
( inv_involution : ∀ x : w, (x⁻¹)⁻¹ = x)
( inv_mult : ∀ x y : w, (x * y) ⁻¹ = x⁻¹ * y⁻¹)
( left_distrib : ∀ x y z: w, (x + y) * z + 0 * z = (x * z) + (y * z))
( left_distrib_cancel : ∀ x y z: w, (x + y * z) * y⁻¹ = x * y⁻¹ + z + 0 * y )
( zero_mult_zero : 0 * 0 = 0)
( pull_out_zero : ∀ x y z : w, (x + 0 * y) * z = x * z + 0 * y)
( bot_absorbsive : ∀ x : w, 0 * 0⁻¹ + x = 0 * 0⁻¹)

end wheel

namespace fraction_wheel

variables (w : Type) [h : comm_ring w] (s : submonoid w)

inductive equiv
  : (w × w) -> (w × w) → Prop
|  intro : ∀
    {l r : w × w}
    {sl sr : w}
    (sl_in_s : sl ∈ s)
    (sr_in_s : sr ∈ s)
    (fst_eq : sl * l.fst = sr * r.fst)
    (snd_eq : sl * l.snd = sr * r.snd),
    equiv l r

open fraction_wheel.equiv

local infix `≈` := @equiv w h s

lemma is_reflexive : reflexive (≈)
| x := intro
  (submonoid.one_mem s)
  (submonoid.one_mem s) rfl rfl

lemma is_symmetric : symmetric (≈)
| _ _ ⟨sl_in_s, sr_in_s, fst_eq, snd_eq⟩ :=
  intro sr_in_s sl_in_s (symm fst_eq) (symm snd_eq)

lemma is_transitive : transitive (≈) :=
begin intros x y z x_y y_z
, simp
, cases x_y; cases y_z
, have fst_eq : y_z_sl * x_y_sl * x.fst = x_y_sr * y_z_sr * z.fst
, calc
    y_z_sl * x_y_sl * x.fst = y_z_sl * (x_y_sl * x.fst) : by {apply mul_assoc}
    ... = y_z_sl * x_y_sr * y.fst : by {rw x_y_fst_eq, apply symm, apply mul_assoc}
    ... = x_y_sr * y_z_sl * y.fst : by {rw (mul_comm x_y_sr)}
    ... = x_y_sr * (y_z_sl * y.fst) : by {apply mul_assoc}
    ... = x_y_sr * (y_z_sr * z.fst) : by {rw y_z_fst_eq}
    ... = x_y_sr * y_z_sr * z.fst : by {apply symm, apply mul_assoc}
, have snd_eq : y_z_sl * x_y_sl * x.snd = x_y_sr * y_z_sr * z.snd
, {calc
    y_z_sl * x_y_sl * x.snd = y_z_sl * (x_y_sl * x.snd) : by {apply mul_assoc}
    ... = y_z_sl * x_y_sr * y.snd : by {rw x_y_snd_eq, apply symm, apply mul_assoc}
    ... = x_y_sr * y_z_sl * y.snd : by {rw (mul_comm x_y_sr)}
    ... = x_y_sr * (y_z_sl * y.snd) : by {apply mul_assoc}
    ... = x_y_sr * (y_z_sr * z.snd) : by {rw y_z_snd_eq}
    ... = x_y_sr * y_z_sr * z.snd : by {apply symm, apply mul_assoc}}
, have sl_in_s : y_z_sl * x_y_sl ∈ s
, {apply submonoid.mul_mem' s, repeat {assumption}}
, have sr_in_s : x_y_sr * y_z_sr ∈ s
, {apply submonoid.mul_mem' s, repeat {assumption}}
, apply (intro sl_in_s sr_in_s); assumption
end

lemma is_equivalence
: equivalence (≈) :=
⟨ is_reflexive w s,
  is_symmetric w s,
  is_transitive w s⟩

lemma fraction_setoid : setoid (w×w) :=
  { r := (≈), iseqv := is_equivalence w s }

abbreviation fractionWheel := quotient (fraction_setoid w s)

open wheel

def raw_add [comm_ring w]
  : w×w -> w×w -> w×w
| ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ := ⟨x₁ * y₂ + x₂ * y₁, x₂ * y₂⟩

local infix ++ := λ x y, raw_add w x y

lemma raw_add_assoc [comm_ring w] (x y z : w×w) : x ++ y ++ z = x ++ (y ++ z) :=
begin cases x with x₁ x₂; cases y with y₁ y₂; cases z with z₁ z₂
, unfold raw_add
, rw prod.eq_iff_fst_eq_snd_eq
, split; simp
, rotate, {apply mul_assoc}
, calc
       (x₁ * y₂ + x₂ * y₁) * z₂     + x₂ * y₂ * z₁
      = x₁ * y₂ * z₂   + x₂ * y₁ * z₂ + x₂ * y₂ * z₁ : by {rw right_distrib}
  ... = x₁ * (y₂ * z₂) + x₂ * y₁ * z₂ + x₂ * y₂ * z₁ : by {rw mul_assoc}
  ... = x₁ * (y₂ * z₂) + (x₂ * y₁ * z₂ + x₂ * y₂ * z₁) : by {rw add_assoc}
  ... = x₁ * (y₂ * z₂) + (x₂ * y₁ * z₂ + x₂ * y₂ * z₁) : by {rw [mul_assoc, mul_assoc]}
  ... = x₁ * (y₂ * z₂) + x₂ * (y₁ * z₂ + y₂ * z₁) : by {rw ← left_distrib}
end


instance fractionWheel_is_Wheel : wheel (fractionWheel w s) :=
{ add := _,
  add_assoc := _,
  zero := _,
  zero_add := _,
  add_zero := _,
  add_comm := _,
  mul := _,
  mul_assoc := _,
  one := _,
  one_mul := _,
  mul_one := _,
  mul_comm := _,
  sub := _,
  inv := _,
  inv_involution := _,
  inv_mult := _,
  left_distrib := _,
  left_distrib_cancel := _,
  zero_mult_zero := _,
  pull_out_zero := _,
  bot_absorbsive := _ }

end fraction_wheel
