/-
Copyright (c) 2020 Christopher A. Upshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Christopher A. Upshaw.
-/

import algebra
import data.quot
import group_theory.group_action

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

instance wheel_has_div (w : Type u) [wheel w] : has_div w :=
  ⟨λ x y, x * y⁻¹⟩

lemma div_def (w : Type u) [wheel w] (x y : w) : x / y = x * y⁻¹ :=
  begin
  unfold has_div.div,
  end

/--
 If there exists an x σ.t. 1 + x = 0, then we can also introduce a subtraction.
 Note however that x - x = 0 is only true when 0 * x * x = 0, i.e. 'finite' values of the wheel.
-/

class sub_wheel (w : Type u) extends wheel w, has_sub w, has_neg w :=
(one_sub_one : (1 - 1 : w) = 0)
(zero_sub : ∀ x : w, 0 - x = (0 - 1) * x )
(neg_from_sub : ∀ x : w, -x = 0 - x)
(sub_from_neg : ∀ x y : w, x - y = x + (- y))

open wheel

lemma bot_mul_zero (w : Type) [wheel w] : (⊥ : w) * 0 = ⊥ :=
  begin
  rw ← zero_mul_zero_inv,
  calc (0 : w) * (0 : w)⁻¹ * 0 = 0 * ((0:w)⁻¹ * 0) : by rw mul_assoc
  ... = 0 * (0 * (0 : w)⁻¹) : by rw (mul_comm ((0 : w)⁻¹) 0)
  ... = 0 * 0 * (0:w)⁻¹ : by rw mul_assoc
  ... = 0 * (0 : w)⁻¹ : by rw zero_mul_zero
  end

lemma bot_inv (w : Type) [wheel w] : (⊥ : w)⁻¹ = ⊥ :=
  begin
  rw ← zero_mul_zero_inv,
  rw [wheel.mul_inv, wheel.inv_inv],
  apply mul_comm,
  end

lemma zero_inv_mul_zero (w : Type) [wheel w] : (0 : w)⁻¹ * 0 = ⊥ :=
  begin
  rw mul_comm,
  apply zero_mul_zero_inv,
  end

namespace fraction

variables {α : Type} [comm_ring α] (σ : submonoid α)

/-- Every comm_ring can be extened to a wheel by taking ratios, and quotienting by a multiplicative submonoid (which needs to not include zero for the construction to be non-trivial.) Usually one takes the submonoid of all nonzero values, this gets you the extended rationals from the integers for example. -/

structure fraction (σ : submonoid α) := (up : α) (down : α)

@[simp] lemma mk.eta : ∀{p : fraction σ}, fraction.mk p.up p.down = p
| ⟨a, b⟩ := rfl

@[ext] lemma fraction.ext (p q : fraction σ)
  (eq_up : p.up = q.up) (eq_down : p.down = q.down) : p = q :=
  begin
  cases p, cases q, simp, split; assumption,
  end

@[simp]
def scale (s : α) (p : fraction σ) : fraction σ :=
  ⟨s * p.up, s * p.down⟩

lemma one_scale (p : fraction σ) : scale σ 1 p = p :=
  begin
  cases p,
  unfold scale,
  simp,
  end

lemma mul_scale (s t : α) (p : fraction σ) : scale σ (s * t) p = scale σ s (scale σ t p) :=
  fraction.ext _ (scale σ (s * t) p) (scale σ s (scale σ t p)) (mul_assoc _ _ _) (mul_assoc _ _ _)

instance : mul_action α (fraction σ) :=
{ smul := scale σ,
  one_smul := one_scale σ,
  mul_smul := mul_scale σ
  }

@[simp]
def scale_def (s : α) (p : fraction σ) : s • p = ⟨s * p.up, s * p.down⟩ :=
rfl

@[ext]
lemma ext {p q : fraction σ} (h₁ : p.up = q.up) (h₂ : p.down = q.down)
  : p = q :=
  begin
  cases p; cases q,
  simp at *, apply and.intro h₁ h₂
  end

inductive fraction_equiv (l r : fraction σ) : Prop
| intro : ∀ (sl sr : α) (sl_in_s : sl ∈ σ) (sr_in_s : sr ∈ σ) (scale_eq : sl • l = sr • r), fraction_equiv

@[refl]
lemma is_reflexive (x : fraction σ) : fraction_equiv σ x x :=
  ⟨1, 1, σ.one_mem, σ.one_mem, rfl⟩

@[symm]
lemma is_symmetric (l r) : fraction_equiv σ l r → fraction_equiv σ r l
  | ⟨sl, sr, sl_in_s, sr_in_s, scale_eq⟩ :=
   ⟨sr, sl, sr_in_s, sl_in_s, symm (scale_eq)⟩

@[trans]
lemma is_transitive (x y z)
  : fraction_equiv σ x y → fraction_equiv σ y z → fraction_equiv σ x z
  | ⟨xy_sl, xy_sr, xy_sl_in_s, xy_sr_in_s, xy_scale_eq⟩
    ⟨yz_sl, yz_sr, yz_sl_in_s, yz_sr_in_s, yz_scale_eq⟩ :=
  begin
  use [yz_sl * xy_sl , xy_sr * yz_sr],
  repeat {refine σ.mul_mem _ _; assumption},
  simp_rw mul_smul,
  rw xy_scale_eq,
  rw ← yz_scale_eq,
  simp_rw ← mul_smul,
  rw mul_comm,
  end

lemma is_equivalence : equivalence (fraction_equiv σ) :=
⟨is_reflexive σ, is_symmetric σ, is_transitive σ⟩

def fraction_setoid : setoid (fraction σ) :=
{ r :=fraction_equiv σ, iseqv := is_equivalence σ }

@[simp]
instance fraction_setoid' : setoid (fraction σ) := fraction_setoid σ

def fraction_wheel {α : Type} [comm_ring α] (σ : submonoid α) : Type :=
  quotient (fraction_setoid σ)

open wheel

def pre_add (x y : fraction σ) : fraction σ := ⟨x.up * y.down + x.down * y.up, x.down * y.down⟩

local infix `++` := λ x y, pre_add σ x y

@[simp]
lemma pre_add_def (x y : fraction σ) : x ++ y = ⟨x.up * y.down + x.down * y.up, x.down * y.down⟩
  := rfl

lemma pre_add_assoc (x y z : fraction σ) : x ++ y ++ z = x ++ (y ++ z) :=
fraction.ext σ _ _
(calc (x.up * y.down + x.down * y.up) * z.down            + x.down * y.down * z.up
    = x.up * y.down * z.down   +  x.down * y.up * z.down     + x.down * y.down * z.up    : by rw add_mul
... = x.up * (y.down * z.down) +  x.down * y.up * z.down     + x.down * y.down * z.up    : by rw mul_assoc
... = x.up * (y.down * z.down) + (x.down * y.up * z.down     + x.down * y.down * z.up)   : by rw add_assoc
... = x.up * (y.down * z.down) + (x.down * (y.up * z.down)   + x.down * (y.down * z.up)) : by rw [mul_assoc, mul_assoc]
... = x.up * (y.down * z.down) +  x.down * (y.up * z.down + y.down * z.up)            : by rw mul_add)
(mul_assoc _ _ _)

lemma mul_rearange (a b c d : α) : a * b * (c * d) = a * c * (b * d) :=
by simp_rw [mul_assoc, mul_left_comm b]

def add' : fraction_wheel σ → fraction_wheel σ → fraction_wheel σ :=
quotient.map₂ (λ x y, x ++ y) begin
  intros x₀ x₁ x y₀ y₁ y, cases x, cases y,
  use [x_sl * y_sl, x_sr * y_sr, σ.mul_mem ‹_› ‹_›, σ.mul_mem ‹_› ‹_›],
  { simp only [pre_add, scale_def] at *,
    cases x_scale_eq with x_scale_up x_scale_down,
    cases y_scale_eq with y_scale_up y_scale_down,
    split; repeat {rw left_distrib},
    { congr' 1;
      rw [mul_rearange x_sl, mul_rearange x_sr];
      congr' 1; assumption,
    },
    {rw [mul_rearange x_sl, mul_rearange x_sr], congr' 1; assumption,}
  },
end

local infix `+'`:65 := @add' α _ σ

@[simp]
lemma add_def' (x y : fraction σ) :
  ⟦x⟧ +' ⟦y⟧ = quotient.mk ⟨x.up * y.down + x.down * y.up, x.down * y.down⟩
  := rfl

@[simp]
lemma sound (a b : fraction σ)
  :fraction_equiv σ a b →
  (quotient.mk' a) = (quotient.mk' b : fraction_wheel σ) :=
  begin intro h,
  apply quot.sound,
  change (fraction_equiv σ a b),
  exact h,
  end

def of (x : α) : fraction_wheel σ :=
  quotient.mk ⟨x, 1⟩

@[simp] def of_def (x : α) : of σ x = quotient.mk ⟨x, 1⟩ :=
rfl

instance : has_coe α (fraction_wheel σ) :=
⟨of σ⟩

instance : has_lift α (fraction_wheel σ) :=
⟨coe⟩

@[simp]
def lift_def (x : α) : (↑x : fraction_wheel σ) = quotient.mk ⟨x, 1⟩ :=
  rfl

instance [has_zero α] : has_zero (fraction_wheel σ) :=
⟨⟦⟨(0 : α),1⟩ ⟧⟩

@[simp]
lemma zero_def : (0 : fraction_wheel σ) = ⟦ ⟨ 0, 1⟩ ⟧ := rfl

lemma zero_add (x) : 0 +' x = x :=
  quotient.induction_on x $ λ x', by {simp}

lemma refl_to_eq {α} {a b : α} {r : α → α → Prop} (is_refl : reflexive r) (h : a = b) : r a b :=
    begin
    rw h, apply is_refl
    end

-- arugments before colon
lemma add_comm (x y) : x +' y = y +' x :=
  begin
  apply quotient.induction_on₂ x y, intros a b, clear x y,
  simp; apply refl_to_eq (setoid.iseqv).1,
  congr' 1; ring
  end

lemma add_zero (x) : x +' 0 = x :=
by rw [add_comm, zero_add]


lemma add_assoc (x y z) : x +' y +' z = x +' (y +' z) :=
  quotient.induction_on₃ x y z $ λ x y z, congr_arg quotient.mk' $ pre_add_assoc _ x y z

instance : has_one (fraction_wheel σ) :=
⟨(1 : α)⟩

@[simp]
lemma one_def : (1 : fraction_wheel σ) = ⟦ ⟨ 1, 1⟩ ⟧ := rfl

instance : add_comm_monoid (fraction_wheel σ) :=
{ add := add' σ,
  add_assoc := add_assoc σ,
  zero := 0,
  zero_add := zero_add σ,
  add_zero := add_zero σ,
  add_comm := add_comm σ }

@[simp]
lemma add_def (x y : fraction σ) :
  (⟦x⟧ + ⟦y⟧ : fraction_wheel σ) =
    quotient.mk ⟨x.up * y.down + x.down * y.up, x.down * y.down⟩
  := rfl

@[simp]
def pre_mul (x y : fraction  σ) : fraction  σ
  := ⟨x.up * y.up, x.down * y.down⟩

local infix `**`:60 := pre_mul σ

@[simp]
lemma pre_mul_def (x y : fraction σ) : x ** y = ⟨x.up * y.up, x.down * y.down⟩
  := rfl

lemma pre_mul_assoc (x y z: fraction  σ)
  : x ** y ** z = x ** (y ** z) :=
  fraction.ext σ _ _ (mul_assoc _ _ _) (mul_assoc _ _ _)

def mul : fraction_wheel σ → fraction_wheel σ → fraction_wheel σ :=
quotient.map₂' (pre_mul σ) $
begin
  intros x₀ x₁ x y₀ y₁ y, obtain := x, obtain := y,
  simp only [scale_def] at *,
  obtain ⟨x_up_eq, x_down_eq⟩ := x_scale_eq,
  obtain ⟨y_up_eq, y_down_eq⟩ := y_scale_eq,
  use [x_sl * y_sl, x_sr * y_sr, σ.mul_mem ‹_› ‹_›, σ.mul_mem ‹_› ‹_›],
  unfold pre_mul;
  simp only [scale_def],
  split,
  all_goals
    { rw mul_rearange x_sl,
      rw mul_rearange x_sr,
      congr' 1; assumption
    },
end

local infix `*'`:60 := mul σ

@[simp]
lemma mul_def' {x y : fraction σ} :
  ⟦x⟧ *' ⟦y⟧ = quotient.mk ⟨x.up * y.up, x.down * y.down⟩
  := rfl

lemma one_mul (x) : 1 *' x = x :=
  quotient.induction_on x $ λ x', by simp

lemma mul_one (x) : x *' 1 = x :=
  quotient.induction_on x $ λ x', congr_arg quotient.mk $
  begin
  ext; simp; apply mul_one,
  end

lemma mul_comm (x y) : x *' y = y *' x :=
  quotient.induction_on₂ x y $ λ x y, congr_arg quotient.mk $
  begin
  ext; simp; apply mul_comm,
  end

lemma mul_assoc (x y z) : x *' y *' z = x *' (y *' z) :=
  quotient.induction_on₃ x y z $ λ x y z, congr_arg quotient.mk' $
  pre_mul_assoc σ x y z

instance : comm_monoid (fraction_wheel σ) :=
{ mul := mul σ,
  mul_assoc := mul_assoc σ,
  one := has_one.one,
  one_mul := one_mul σ,
  mul_one := mul_one σ,
  mul_comm := mul_comm σ }

@[simp]
lemma mul_def (x y : fraction σ) :
  (⟦x⟧ * ⟦y⟧ : fraction_wheel σ) =
    quotient.mk ⟨x.up * y.up, x.down * y.down⟩
  := rfl

def pre_inv (x : fraction  σ) : fraction  σ := ⟨x.down, x.up⟩

@[simp]
lemma pre_inv_def (x : fraction σ) : pre_inv σ x = fraction.mk x.down x.up :=
  rfl

@[simp]
lemma pre_inv_inv (x : fraction σ) : pre_inv σ (pre_inv σ x) = x :=
  begin simp end

def inv : fraction_wheel σ -> fraction_wheel σ :=
  quotient.map (pre_inv σ) $
  begin
  intros x₀ x₁ x, obtain := x₀; obtain := x₁; obtain := x,
  use [x_sl, x_sr]; try {assumption},
  simp only [scale]
  end

instance : has_inv (fraction_wheel σ) := ⟨inv α σ⟩

@[simp]
lemma inv_def (x : fraction σ) :
  (⟦x⟧⁻¹ : fraction_wheel σ)  = quotient.mk ⟨x.down, x.up⟩ := rfl

@[simp]
lemma inv_inv (x : fraction_wheel σ) : (x⁻¹)⁻¹ = x :=
  quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  begin
  simp; refl
  end

lemma mul_inv (x y : fraction_wheel σ) : (x * y)⁻¹ = (x⁻¹) * (y⁻¹) :=
  quotient.induction_on₂' x y $ λ x y, congr_arg quotient.mk rfl

instance : has_bot (fraction_wheel σ) :=
  ⟨quotient.mk ⟨0,0⟩ ⟩

@[simp]
lemma bot_def : (⊥ : fraction_wheel σ) = quotient.mk ⟨0,0⟩ := rfl

@[simp]
lemma bot_add (x : fraction_wheel σ) : ⊥ + x = ⊥ :=
  quotient.induction_on x $ λ x', begin clear x, cases x', simp end

lemma add_mul_add_zero_mul
  (x y z : fraction_wheel σ) : (x + y) * z + 0 * z = x * z + y * z :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
    begin
    unfold pre_add,
    simp,
    split; ring
    end

lemma add_mul_mul_inv
  (x y z : fraction_wheel σ) : (x + y * z) * (y⁻¹) = x * (y⁻¹) + z + 0 * y :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  simp, split; ring,
  end

lemma zero_mul_zero : (0 * 0 : fraction_wheel σ) = 0 :=
  congr_arg quotient.mk' $
  begin
  unfold pre_mul,
  ext; dsimp,
  refine mul_zero _,
  ring,
  end

lemma add_zero_mul_mul
  (x y z : fraction_wheel σ) : (x + 0 * y) * z = x * z + 0 * y :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  ext; norm_num; ring,
  end

lemma zero_mul_zero_inv : (0 : fraction_wheel σ) * (0⁻¹) = ⊥ :=
 congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul pre_inv,
  ext; norm_num,
  end

instance : inhabited (fraction_wheel σ) := ⟨1⟩

instance : wheel (fraction_wheel σ) :=
{ inv := inv σ,
  inv_inv := inv_inv σ,
  mul_inv := mul_inv σ,
  add_mul_add_zero_mul := add_mul_add_zero_mul σ,
  add_mul_mul_inv := add_mul_mul_inv σ,
  zero_mul_zero := zero_mul_zero σ,
  add_zero_mul_mul := add_zero_mul_mul σ,
  zero_mul_zero_inv := zero_mul_zero_inv σ,
  bot_add := bot_add σ }
-/
end fraction