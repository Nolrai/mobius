import data.matrix.basic
import data.matrix.notation
import data.complex.basic
import wheel

#print integral_domain

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

-- the Reiman sphere with an addition point to represent 0/0.
-- The term wheel is inspired by the topological picture ⊙ of the projective line together with an extra point ⊥ = 0/0.

notation `RiemannWheel` := fractionWheel ℂ non_zero

notation `M2` T := matrix (fin 2) (fin 2) T



