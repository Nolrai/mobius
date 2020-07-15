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

variables (α : Type) [comm_ring α] (σ : submonoid α)

/-- Every comm_ring can be extened to a wheel by taking ratios, and quotienting by a multiplicative submonoid (which needs to not include zero for the construction to be non-trivial.) Usually one takes the submonoid of all nonzero values, this gets you the extended rationals from the integers for example. -/

structure fraction (σ : submonoid α) := (up : α) (down : α)

@[simp] lemma mk.eta : ∀{p : fraction α σ}, fraction.mk p.up p.down = p
| ⟨a, b⟩ := rfl

@[ext]
lemma ext {p q : fraction α σ} (h₁ : p.up = q.up) (h₂ : p.down = q.down)
  : p = q :=
  begin
  cases p; cases q,
  simp at *, apply and.intro h₁ h₂
  end

inductive fraction_equiv (l r : fraction α σ) : Prop
| intro : ∀ (sl sr : α) (sl_in_s : sl ∈ σ) (sr_in_s : sr ∈ σ),
    ∀ (up_eq : sl * l.up = sr * r.up) (down_eq : sl * l.down = sr * r.down),
    fraction_equiv

open fraction_equiv

@[refl]
lemma is_reflexive (x : fraction α σ) : fraction_equiv α σ x x :=
  ⟨1, 1, σ.one_mem, σ.one_mem, rfl, rfl⟩

@[symm]
lemma is_symmetric (l r) : fraction_equiv α σ l r → fraction_equiv α σ r l
| ⟨sl, sr, sl_h, sr_h, up_eq, down_eq⟩ := ⟨sr, sl, sr_h, sl_h, up_eq.symm, down_eq.symm⟩

@[trans]
lemma is_transitive (x y z)
  : fraction_equiv α σ x y → fraction_equiv α σ y z → fraction_equiv α σ x z
| ⟨s1, s2, hs1, hs2, hs3, hs4⟩ ⟨t1, t2, ht1, ht2, ht3, ht4⟩ :=
    ⟨s1 * t1, s2 * t2, σ.mul_mem hs1 ht1, σ.mul_mem hs2 ht2,
      by rw [mul_right_comm, hs3, mul_right_comm, mul_assoc, ht3, mul_assoc],
      by rw [mul_right_comm, hs4, mul_right_comm, mul_assoc, ht4, mul_assoc]⟩

lemma is_equivalence : equivalence (fraction_equiv α σ) :=
⟨is_reflexive α σ, is_symmetric α σ, is_transitive α σ⟩

def fraction_setoid : setoid (fraction α σ) :=
{ r := fraction_equiv α σ, iseqv := is_equivalence α σ }

@[simp]
instance fraction_setoid' : setoid (fraction α σ) := fraction_setoid α σ

def fraction_wheel (α : Type) [comm_ring α] (σ : submonoid α) : Type :=
  quotient (fraction_setoid α σ)

open wheel

def pre_add (x y : fraction α σ) : fraction α  σ := ⟨x.up * y.down + x.down * y.up, x.down * y.down⟩

local infix `++` := λ x y, pre_add α σ x y

@[simp]
lemma pre_add_def (x y : fraction α σ) : x ++ y = ⟨x.up * y.down + x.down * y.up, x.down * y.down⟩
  := rfl

lemma pre_add_assoc (x y z : fraction α σ) : x ++ y ++ z = x ++ (y ++ z) :=
fraction.ext α σ
(calc (x.up * y.down + x.down * y.up) * z.down            + x.down * y.down * z.up
    = x.up * y.down * z.down   +  x.down * y.up * z.down     + x.down * y.down * z.up    : by rw add_mul
... = x.up * (y.down * z.down) +  x.down * y.up * z.down     + x.down * y.down * z.up    : by rw mul_assoc
... = x.up * (y.down * z.down) + (x.down * y.up * z.down     + x.down * y.down * z.up)   : by rw add_assoc
... = x.up * (y.down * z.down) + (x.down * (y.up * z.down)   + x.down * (y.down * z.up)) : by rw [mul_assoc, mul_assoc]
... = x.up * (y.down * z.down) +  x.down * (y.up * z.down + y.down * z.up)            : by rw mul_add)
(mul_assoc _ _ _)

variables {α}
lemma mul_rearange (a b c d : α) : a * b * (c * d) = a * c * (b * d) :=
by simp_rw [mul_assoc, mul_left_comm b]
variables (α)

def add : fraction_wheel α σ → fraction_wheel α σ → fraction_wheel α σ :=
quotient.map₂ (pre_add α σ) begin
  intros x₀ x₁ x y₀ y₁ y, cases x, cases y,
  use [x_sl * y_sl, x_sr * y_sr, σ.mul_mem ‹_› ‹_›, σ.mul_mem ‹_› ‹_›],
  -- space after opening curly bracket
  { dsimp only [pre_add], repeat { rw left_distrib }, congr' 1,
    calc  x_sl * y_sl * (x₀.up * y₀.down) = x_sl * x₀.up * (y_sl * y₀.down) : mul_rearange _ _ _ _
    ... = x_sr * x₁.up * (y_sl * y₀.down) : by rw x_up_eq
    ... = x_sr * x₁.up * (y_sr * y₁.down) : by rw y_down_eq
    ... = x_sr * y_sr * (x₁.up * y₁.down) : mul_rearange _ _ _ _,
    calc  x_sl * y_sl * (x₀.down * y₀.up) = x_sl * x₀.down * (y_sl * y₀.up) : mul_rearange _ _ _ _
    ... = x_sr * x₁.down * (y_sl * y₀.up) : by rw x_down_eq
    ... = x_sr * x₁.down * (y_sr * y₁.up) : by rw y_up_eq
    ... = x_sr * y_sr * (x₁.down * y₁.up) : mul_rearange _ _ _ _ }, --closing curly bracket on the same line
  { calc  x_sl * y_sl * (x₀.down * y₀.down) = x_sl * x₀.down * (y_sl * y₀.down) : mul_rearange _ _ _ _
    ... = x_sr * x₁.down * (y_sl * y₀.down) : by {rw x_down_eq}
    ... = x_sr * x₁.down * (y_sr * y₁.down) : by {rw y_down_eq}
    ... = x_sr * y_sr * (x₁.down * y₁.down) : mul_rearange _ _ _ _ },
end

local infix `+'`:65 := add α σ

@[simp]
lemma quotient.map₂_mk {α β γ} (f : α → β → γ) [sa : setoid α] [sb : setoid β] [sc : setoid γ] (h : ((≈) ⇒ (≈) ⇒ (≈)) f f) (x : α) (y : β) :
  quotient.map₂ f h (⟦x⟧ : quotient sa) (⟦y⟧ : quotient sb) = (⟦f x y⟧ : quotient sc) := rfl

@[simp]
lemma add_def' (x' y' : fraction_wheel α σ) (x y : fraction α σ) :
  (x' = quotient.mk x) → (y' = quotient.mk y) →
  x' +' y' = quotient.mk ⟨x.up * y.down + x.down * y.up, x.down * y.down⟩
  :=
  begin
  unfold add,
  intros xh yh,
  subst_vars,
  dsimp [fraction],
  end

lemma sound (a b : fraction α σ)
  : fraction_equiv α σ a b →
  (quotient.mk' a) = (quotient.mk' b : fraction_wheel α σ) :=
  begin intro h,
  apply quot.sound,
  change (fraction_equiv α σ a b),
  exact h,
  end

@[simp] def of (x : α) : fraction_wheel α σ :=
quotient.mk ⟨x, 1⟩

instance : has_coe α (fraction_wheel α σ) :=
⟨of α σ⟩

instance : has_zero (fraction_wheel α σ) :=
⟨ of α σ 0⟩

lemma zero_add (x) : 0 +' x = x :=
quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  fraction.ext α σ
  (show 0 * x.down + 1 * x.up = x.up, by rw [zero_mul, one_mul, zero_add])
  (one_mul _)

-- arugments before colon
lemma add_comm (x y) : x +' y = y +' x :=
quotient.induction_on₂' x y $ λ x y, congr_arg quotient.mk' $ show (_, _) = (_, _), from prod.ext
  (show _ + _ = _ + _, by rw [mul_comm x.up, mul_comm x.down, add_comm])
  (mul_comm _ _)

lemma add_zero (x) : x +' 0 = x :=
by rw [add_comm, zero_add]

lemma add_assoc (x y z) : x +' y +' z = x +' (y +' z) :=
quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $ pre_add_assoc _ _ _ _

instance : has_one (fraction_wheel α σ) :=
⟨(1 : α)⟩

instance : add_comm_monoid (fraction_wheel α σ) :=
{ add := add α σ,
  add_assoc := add_assoc α σ,
  zero := 0,
  zero_add := zero_add α σ,
  add_zero := add_zero α σ,
  add_comm := add_comm α σ }

def pre_mul [comm_ring α] (x y : fraction  α σ) : fraction  α σ
  := ⟨x.up * y.up, x.down * y.down⟩

local infix `**`:60 := pre_mul α

lemma pre_mul_assoc [comm_ring α] (x y z: fraction  α σ)
  : x ** y ** z = x ** (y ** z) :=
  show (_, _) = (_, _), from prod.ext (mul_assoc _ _ _) (mul_assoc _ _ _)

def mul : fraction_wheel α σ → fraction_wheel α σ → fraction_wheel α σ :=
quotient.map₂' (pre_mul α) $
begin
  intros x₀ x₁ x y₀ y₁ y, obtain := x, obtain := y,
  use [x_sl * y_sl, x_sr * y_sr, σ.mul_mem ‹_› ‹_›, σ.mul_mem ‹_› ‹_›],
  all_goals
    { obtain := x₀, obtain := y₀, obtain := x₁, obtain := y₁, unfold pre_mul; dsimp only [] },
  {    calc x_sl * y_sl * (x₀_up * y₀_up) = x_sl * x₀_up * (y_sl * y₀_up) : mul_rearange _ _ _ _
    ... = x_sr * x₁_up * (y_sl * y₀_up) : by {rw x_up_eq}
    ... = x_sr * x₁_up * (y_sr * y₁_up) : by {rw y_up_eq}
    ... = x_sr * y_sr * (x₁_up * y₁_up) : mul_rearange _ _ _ _,},
  {    calc x_sl * y_sl * (x₀_down * y₀_down) = x_sl * x₀_down * (y_sl * y₀_down) : mul_rearange _ _ _ _
    ... = x_sr * x₁_down * (y_sl * y₀_down) : by {rw x_down_eq}
    ... = x_sr * x₁_down * (y_sr * y₁_down) : by {rw y_down_eq}
    ... = x_sr * y_sr * (x₁_down * y₁_down) : mul_rearange _ _ _ _,}
end

local infix `*'`:60 := mul α σ

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

instance : comm_monoid (fraction_wheel α σ) :=
{ mul := mul α σ,
  mul_assoc := mul_assoc α σ,
  one := has_one.one,
  one_mul := one_mul α σ,
  mul_one := mul_one α σ,
  mul_comm := mul_comm α σ }

def pre_inv (x : fraction  α σ) : fraction  α σ := ⟨x.down, x.up⟩

lemma pre_inv_inv : ∀ x, pre_inv α (pre_inv α x) = x
| ⟨l, r⟩ := rfl

def inv : fraction_wheel α σ -> fraction_wheel α σ :=
  quotient.map' (pre_inv α) $
  begin
  intros x₀ x₁ x, obtain := x₀; obtain := x₁; obtain := x,
  use [x_sl, x_sr]; assumption
  end

instance : has_inv (fraction_wheel α σ) := ⟨inv α s⟩

lemma inv_inv (x : fraction_wheel α σ) : (x⁻¹)⁻¹ = x :=
  quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  begin
  unfold pre_inv,
  apply prod.ext; dsimp only [prod.up, prod.down]; refl
  end

lemma mul_inv (x y : fraction_wheel α σ) : (x * y)⁻¹ = (x⁻¹) * (y⁻¹) :=
  quotient.induction_on₂' x y $ λ x y, congr_arg quotient.mk' rfl

instance : has_bot (fraction_wheel α σ) :=
  ⟨quotient.mk' ⟨0,0⟩ ⟩

lemma bot_add (x : fraction_wheel α σ) : ⊥ + x = ⊥ :=
  quotient.induction_on' x $ λ x, congr_arg quotient.mk' $
  begin
  unfold pre_add;
  apply prod.ext;
  norm_num
  end

lemma add_mul_add_zero_mul
  (x y z : fraction_wheel α σ) : (x + y) * z + 0 * z = x * z + y * z :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  apply prod.ext; norm_num; ring,
  end

lemma add_mul_mul_inv
  (x y z : fraction_wheel α σ) : (x + y * z) * (y⁻¹) = x * (y⁻¹) + z + 0 * y :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  apply prod.ext; norm_num; ring,
  end

lemma zero_mul_zero : (0 * 0 : fraction_wheel α σ) = 0 :=
  congr_arg quotient.mk' $
  begin
  unfold pre_mul,
  apply prod.ext; dsimp,
  refine mul_zero _,
  ring,
  end

lemma add_zero_mul_mul
  (x y z : fraction_wheel α σ) : (x + 0 * y) * z = x * z + 0 * y :=
  quotient.induction_on₃' x y z $ λ x y z, congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul,
  apply prod.ext; norm_num; ring,
  end

lemma zero_mul_zero_inv : (0 : fraction_wheel α σ) * (0⁻¹) = ⊥ :=
 congr_arg quotient.mk' $
  begin
  unfold pre_add pre_mul pre_inv,
  apply prod.ext; norm_num,
  end

instance : inhabited (fraction_wheel α σ) := ⟨1⟩

instance : wheel (fraction_wheel α σ) :=
{ inv := inv α σ,
  inv_inv := inv_inv α σ,
  mul_inv := mul_inv α σ,
  add_mul_add_zero_mul := add_mul_add_zero_mul α σ,
  add_mul_mul_inv := add_mul_mul_inv α σ,
  zero_mul_zero := zero_mul_zero α σ,
  add_zero_mul_mul := add_zero_mul_mul α σ,
  zero_mul_zero_inv := zero_mul_zero_inv α σ,
  bot_add := bot_add α σ }

end fraction_wheel