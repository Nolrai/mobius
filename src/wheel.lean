-- as described at https://en.wikipedia.org/wiki/Wheel_theory

import algebra
import data.quot

universe u

namespace wheel
variables (w : Type u)

class wheel extends add_comm_monoid w, comm_monoid w, has_inv w, has_bot w :=
( inv_involution : ∀ x : w, (x⁻¹)⁻¹ = x)
( inv_swap_mul : ∀ x y : w, (x * y) ⁻¹ = x⁻¹ * y⁻¹)
( left_distrib : ∀ x y z: w, (x + y) * z + 0 * z = (x * z) + (y * z))
( left_distrib_cancel : ∀ x y z: w, (x + y * z) * y⁻¹ = x * y⁻¹ + z + 0 * y )
( zero_mul_zero : 0 * 0 = (0 : w))
( pull_out_zero : ∀ x y z : w, (x + 0 * y) * z = x * z + 0 * y)
( bot_def : (0 : w) * 0⁻¹ = ⊥ )
( bot_absorbsive : ∀ x : w, ⊥ + x = ⊥)

class subtraction_wheel extends wheel w, has_sub w :=
(one_minus_one : (1 : w) - 1 = 0)
(zero_minus : ∀ x : w, 0 - x = (0 - 1) * x )

end wheel

namespace fraction_wheel
/- Every comm_ring can be extened to a wheel by taking ratios, and quotienting by a multiplicative submonoid (which needs to not include zero for the construction to be non-trivial.) Usually one takes the submonoid of all nonzero values, this gets you the extended rationals from the integers for example. -/

variables (w : Type) [h : comm_ring w] (s : submonoid w)

inductive fraction_equiv (l r : w × w) : Prop
| intro : ∀ (sl sr : w) (sl_in_s : sl ∈ s) (sr_in_s : sr ∈ s),
    ∀ (fst_eq : sl * l.fst = sr * r.fst) (snd_eq : sl * l.snd = sr * r.snd),
    fraction_equiv

open fraction_equiv

lemma is_reflexive : reflexive (fraction_equiv w s) :=
  begin intros x,
  apply (fraction_equiv.intro); try {exact submonoid.one_mem s},
  all_goals {norm_num},
  end

lemma is_symmetric : symmetric (fraction_equiv w s)
| x y ⟨sl, sr, sl_h, sr_h, fst_eq, snd_eq⟩ :=
  ⟨sr, sl, sr_h, sl_h, symm fst_eq, symm snd_eq⟩

lemma is_transitive : transitive (fraction_equiv w s)
| x y z xy yz :=
  begin
  cases xy; cases yz,
  apply (fraction_equiv.intro (yz_sl * xy_sl) (xy_sr * yz_sr)),
  {apply submonoid.mul_mem; assumption},
  {apply submonoid.mul_mem; assumption},
  all_goals {repeat {rw mul_assoc}},
  {rw xy_fst_eq, rw ← yz_fst_eq, repeat {rw ← mul_assoc}, rw mul_comm _ yz_sl},
  {rw xy_snd_eq, rw ← yz_snd_eq, repeat {rw ← mul_assoc}, rw mul_comm _ yz_sl}
  end

lemma is_equivalence
: equivalence (fraction_equiv w s) :=
⟨ is_reflexive w s,
  is_symmetric w s,
  is_transitive w s⟩

def fraction_setoid : setoid (w×w) :=
  { r := fraction_equiv w s, iseqv := is_equivalence w s }

def fraction_wheel (w : Type) [comm_ring w] (s : submonoid w) : Type := quotient (fraction_setoid w s)

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
       (x₁ * y₂ + x₂ * y₁) * z₂           + x₂ * y₂ * z₁
      = x₁ * y₂ * z₂   +  x₂ * y₁ * z₂     + x₂ * y₂ * z₁    : by {rw right_distrib}
  ... = x₁ * (y₂ * z₂) +  x₂ * y₁ * z₂     + x₂ * y₂ * z₁    : by {rw mul_assoc}
  ... = x₁ * (y₂ * z₂) + (x₂ * y₁ * z₂     + x₂ * y₂ * z₁)   : by {rw add_assoc}
  ... = x₁ * (y₂ * z₂) + (x₂ * (y₁ * z₂) + x₂ * (y₂ * z₁))  : by {norm_num, repeat {rw mul_assoc}}
  ... = x₁ * (y₂ * z₂) +  x₂ * (y₁ * z₂ + y₂ * z₁)           : by {rw ← left_distrib}
end

lemma mul_rearange {t} [comm_ring t] : ∀ a b c d : t, a * b * (c * d) = a * c * (b * d) :=
  by {intros, ring1}


def add : fraction_wheel w s → fraction_wheel w s → fraction_wheel w s :=
quotient.map₂' (raw_add w) $
begin
  intros x₀ x₁ x y₀ y₁ y,
  induction x; induction y,
  apply (fraction_equiv.intro (x_sl * y_sl) (x_sr * y_sr)),
  refine submonoid.mul_mem s _ _; assumption,
  refine submonoid.mul_mem s _ _; assumption,
  all_goals {cases x₀; cases y₀; cases x₁; cases y₁; unfold raw_add; simp at *},
  {repeat {rw left_distrib}, apply congr_arg2,
    calc x_sl * y_sl * (x₀_fst * y₀_snd) = x_sl * x₀_fst * (y_sl * y₀_snd) : mul_rearange _ _ _ _
    ... = x_sr * x₁_fst * (y_sl * y₀_snd) : by {rw x_fst_eq}
    ... = x_sr * x₁_fst * (y_sr * y₁_snd) : by {rw y_snd_eq}
    ... = x_sr * y_sr * (x₁_fst * y₁_snd) : mul_rearange _ _ _ _,
    calc x_sl * y_sl * (x₀_snd * y₀_fst) = x_sl * x₀_snd * (y_sl * y₀_fst) : mul_rearange _ _ _ _
    ... = x_sr * x₁_snd * (y_sl * y₀_fst) : by {rw x_snd_eq}
    ... = x_sr * x₁_snd * (y_sr * y₁_fst) : by {rw y_fst_eq}
    ... = x_sr * y_sr * (x₁_snd * y₁_fst) : mul_rearange _ _ _ _
  },
  {    calc x_sl * y_sl * (x₀_snd * y₀_snd) = x_sl * x₀_snd * (y_sl * y₀_snd) : mul_rearange _ _ _ _
    ... = x_sr * x₁_snd * (y_sl * y₀_snd) : by {rw x_snd_eq}
    ... = x_sr * x₁_snd * (y_sr * y₁_snd) : by {rw y_snd_eq}
    ... = x_sr * y_sr * (x₁_snd * y₁_snd) : mul_rearange _ _ _ _,},
end

local notation `add'` := add w s

@[simp]
def lift_ : w → fraction_wheel w s := λ x , quotient.mk' (x,1)

instance fraction_has_lift : has_lift w (fraction_wheel w s) :=
  ⟨lift_ w s⟩

instance fraction_has_zero : has_zero (fraction_wheel w s) :=
  {has_zero . zero := ↑ (0 : w)}

lemma zero_add (x) :
  (add' 0 x) = x :=
  begin
  intros,
  unfold add,
  unfold1 has_zero.zero,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  rw quotient.map₂'_mk',
  apply quotient.induction_on' x, clear x, intros x,
  rw quotient.map'_mk',
  apply congr_arg,
  cases x,
  unfold raw_add,
  norm_num,
  end

lemma add_zero (x) :
  (add' x 0) = x :=
  begin
  intros,
  unfold add,
  apply quotient.induction_on' x, clear x, intros x,
  rw quotient.map₂'_mk',
  unfold1 has_zero.zero,
  unfold coe lift_t has_lift_t.lift lift has_lift.lift lift_,
  rw quotient.map'_mk',
  apply congr_arg,
  cases x,
  unfold raw_add,
  norm_num
  end

lemma add_comm : ∀ x y, add' x y = add' y x :=
  begin
  intros,
  unfold add,
  apply quotient.induction_on₂' x y, clear x y, intros x y,
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  cases x, cases y,
  unfold raw_add,
  apply congr_arg,
  apply congr_arg2; ring,
  end

lemma add_assoc : ∀ x y z, add' (add' x y) z = add' x (add' y z) :=
  begin
  intros,
  unfold add,
  apply quotient.induction_on₃' x y z, clear x y z, intros x y z,
  repeat {rw quotient.map₂'_mk'},
  repeat {rw quotient.map'_mk'},
  rw quotient.map₂'_mk',
  rw quotient.map'_mk',
  apply congr_arg,
  cases x, cases y, cases z,
  unfold raw_add,
  apply congr_arg2; ring,
  end

instance fraction_wheel.has_one : has_one (fraction_wheel w s) :=
  {has_one . one := ↑(1:w)}

instance fraction_wheel_is_add_comm_monoid : add_comm_monoid (fraction_wheel w s) :=
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
  apply intro x_sl x_sr ; try {assumption}
  end

local postfix  `ᵃ`:60 := inv w s

def inv_involution : ∀ x : fraction_wheel w s, (xᵃ)ᵃ = x :=
  begin
  intros,
  unfold inv,
  apply quotient.induction_on' x,
  clear x; intros x; cases x,
  rw [quotient.map'_mk', quotient.map'_mk'],
  unfold raw_inv,
  end

def inv_swap_mul : ∀ x y : fraction_wheel w s, (x * y)ᵃ = (xᵃ) * (yᵃ) :=
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

def bot_absorbsive : ∀ (x : fraction_wheel w s), ⊥ + x = ⊥ :=
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