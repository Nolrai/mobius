import data.matrix.basic
import data.matrix.notation
import data.complex.basic
import wheel

noncomputable def non_zero : submonoid ℂ :=
{ carrier := (≠ 0),
  one_mem' := by {unfold has_mem.mem set.mem, norm_num},
  mul_mem' :=
  begin unfold has_mem.mem set.mem, intros a b a0 b0 ab0
  , have h : a = 0 ∨ b = 0
  , {apply eq_zero_or_eq_zero_of_mul_eq_zero ab0}
  , cases h; contradiction
  end
}

-- the Reimann sphere with an addition point to represent 0/0.
-- The term wheel is inspired by the topological picture ⊙ of the projective line together with an extra point ⊥ = 0/0.

inductive ReimannWheel
| mk : ℂ → ReimannWheel
| inf : ReimannWheel
| bot : ReimannWheel

notation `ℂ∞` := ReimannWheel

open ReimannWheel

def add : ℂ∞ → ℂ∞ → ℂ∞
| (mk z₀) (mk z₁) := mk (z₀ + z₁)
| bot _ := bot
| _ bot := bot
| inf _ := inf
| _ inf := inf

lemma ReimannWheel.add_assoc : associative add :=
  begin intros x y z
  , cases x; cases y; cases z; unfold add
  , rw add_assoc
  end

instance ReimannWheel.has_zero : has_zero ReimannWheel := ⟨mk 0⟩

lemma mk_0_eq_0 : mk 0 = 0 := by {unfold has_zero.zero}

lemma ReimannWheel.add_zero : ∀ x, add x 0 = x
| (mk z) := by {rw ← mk_0_eq_0, unfold add, rw add_zero}
| inf := by {rw ← mk_0_eq_0, unfold add}
| bot := by {rw ← mk_0_eq_0, unfold add}

lemma ReimannWheel.zero_add : ∀ x, add 0 x = x
| (mk z) := by {rw ← mk_0_eq_0, unfold add, rw zero_add}
| inf := by {rw ← mk_0_eq_0, unfold add}
| bot := by {rw ← mk_0_eq_0, unfold add}

lemma ReimannWheel.add_comm : ∀ x y, add x y = add y x
| x y := by {cases x; cases y; unfold add; rw add_comm}

noncomputable def mul : ℂ∞ → ℂ∞ → ℂ∞
| (mk z₀) (mk z₁) := mk (z₀ * z₁)
| bot _ := bot
| _ bot := bot
| inf (mk z) := if z = 0 then bot else inf
| (mk z) inf := if z = 0 then bot else inf
| inf inf := inf

lemma ReimannWheel.mul_assoc : associative mul :=
  begin intros x y z
  , cases x; cases y; cases z; unfold mul
  , {rw mul_assoc}
  end

instance ReimannWheelIsWheel : wheel ReimannWheel :=
{ add := add,
  add_assoc := by {unfold has_add.add, apply ReimannWheel.add_assoc},
  zero_add := by {unfold has_add.add, apply ReimannWheel.zero_add},
  add_zero := by {unfold has_add.add, apply ReimannWheel.add_zero},
  add_comm := by {unfold has_add.add, apply ReimannWheel.add_comm},
  mul := mul,
  mul_assoc := by {unfold has_mul.mul, apply ReimannWheel.mul_assoc},
  one := mk 1,
  one_mul := _,
  mul_one := _,
  mul_comm := _,
  inv := _,
  inv_involution := _,
  inv_mult := _,
  left_distrib := _,
  left_distrib_cancel := _,
  zero_mult_zero := _,
  pull_out_zero := _,
  bot_absorbsive := _ }

notation `M2` T := matrix (fin 2) (fin 2) T



