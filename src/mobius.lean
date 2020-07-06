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

def ReimannWheel := fraction_wheel ℂ non_zero.