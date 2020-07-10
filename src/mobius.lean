import data.matrix.basic
import data.matrix.notation
import data.complex.basic
import wheel
import linear_algebra.determinant

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

open wheel

abbreviation reimann_wheel := fraction_wheel ℂ non_zero

notation `ℂ⊙` := reimann_wheel
notation `ℂ∞` := {x : ℂ⊙ | x ≠ 0/0}

universe u

lemma of_div_of (x y : ℂ) : (↑x : ℂ⊙)/y = quotient.mk' ⟨x, y⟩ :=
  begin
  apply quotient.sound,
  unfold fraction_wheel.pre_inv fraction_wheel.pre_mul,
  dsimp, rw [one_mul y, mul_one x],
  end

lemma inf_eq {x : ℂ} : x ≠ 0 → (x : ℂ⊙)/↑(0 : ℂ) = 1/0 :=
  begin
  intro h,
  apply quotient.sound,
  unfold fraction_wheel.pre_inv fraction_wheel.pre_mul,
  dsimp, rw [one_mul (0 : ℂ), mul_one x],
  use [1, x, one_ne_zero, h]; dsimp,
  rw [comm_monoid.one_mul], repeat {rw [comm_monoid.mul_one]},
  rw [mul_zero _, mul_zero _],
  end

lemma finite_eq {x y : ℂ} : y ≠ 0 → (x : ℂ⊙)/↑(y : ℂ) = ↑(x/y) :=
  begin
  intro h,
  apply quotient.sound,
  unfold fraction_wheel.pre_inv fraction_wheel.pre_mul,
  dsimp, repeat {rw mul_one}, rw one_mul,
  use [1, y, one_ne_zero, h]; dsimp,
  rw one_mul, exact (mul_div_cancel' x h).symm,
  apply mul_comm,
  end

lemma reimann_wheel.cases (P : ℂ⊙ → Prop)
  : P (0/0) → P (1/0) -> (∀ c : ℂ, P c) -> (∀ z, P z)
  | P_bot P_inf P_c z :=
  quotient.induction_on' z $ λ z,
    match z with
    | ⟨z₁, z₂⟩ :=
      if z₂_0 : z₂ = 0
        then if z₁_0 : z₁ = 0
          then begin rw [z₂_0, z₁_0, ← of_div_of], exact P_bot end
          else begin rw [z₂_0, ← of_div_of], rw inf_eq z₁_0, exact P_inf end
        else begin rw ← of_div_of, rw finite_eq, refine P_c _, exact z₂_0, end
    end

abbreviation M_2x2 := matrix (fin 2) (fin 2) ℂ

notation `M₂` := M_2x2

namespace M_2x2

variables m n : M₂

abbreviation det : ℂ := m.det

lemma det_2x2 : m.det = m 0 0 * m 1 1 - m 1 0 * m 0 1 :=
calc m.det = ((1 : units ℤ) * (_ * (_ * 1))) + (((-1 : units ℤ) * (_ * (_ * 1))) + 0) : refl m.det
... = m 0 0 * m 1 1 - m 1 0 * m 0 1 : by { simp, ring }

lemma ext_2x2 : m 0 0 = n 0 0 → m 0 1 = n 0 1 → m 1 0 = n 1 0 → m 1 1 = n 1 1 → m = n :=
  begin intros h₀₀ h₀₁ h₁₀ h₁₁,
  apply matrix.ext,
  intros i,
  apply fin.cases; revert i,
  apply fin.cases, exact h₀₀,
  apply fin.cases, exact h₁₀,
  intro void, apply fin.elim0 void,
  intros i,
  apply fin.cases; revert i,
  apply fin.cases, exact h₀₁,
  apply fin.cases, exact h₁₁,
  intro void, apply fin.elim0 void,
  intros _ void, apply fin.elim0 void,
  end

lemma dot_2  (w v : fin 2 → ℂ) : matrix.dot_product w v = w 0 * v 0 + w 1 * v 1 :=
  calc matrix.dot_product w v = (_ + _) : refl (matrix.dot_product w v)
  ... = w 0 * v 0 + w 1 * v 1 : by { simp, ring }

lemma mul_2x2 : m * n =
  ![  ![m 0 0 * n 0 0 + m 0 1 * n 1 0, m 0 0 * n 0 1 + m 0 1 * n 1 1],
      ![m 1 0 * n 0 0 + m 1 1 * n 1 0, m 1 0 * n 0 1 + m 1 1 * n 1 1]
  ] :=
begin
apply ext_2x2; simp; unfold matrix.mul; apply dot_2,
end

end M_2x2

noncomputable def as_mobius (m : M₂) (z : ℂ⊙) := (z * m 0 0 + m 1 0 )/(z * m 1 0 + m 1 1)

noncomputable instance mobius_as_scalar : has_scalar M₂ ℂ⊙ := ⟨as_mobius⟩

notation `G₂` := units M₂

namespace M_2x2
variables m n : M₂

def unit_inv : M₂ := ![ ![ m 1 1, - m 0 1], ![ -m 1 0, m 0 0] ]

lemma unit_inv_unit_inv : unit_inv (unit_inv m) = m :=
  begin
  unfold unit_inv; apply ext_2x2; simp,
  end

lemma det_unit_inv : det m.unit_inv = det m :=
  begin
  unfold unit_inv, repeat {rw det_2x2}, simp,
  apply mul_comm,
  end

lemma mul_unit_inv : m * m.unit_inv = m.det • (1 : M₂) :=
  begin unfold unit_inv,
  rw mul_2x2, simp,
  apply ext_2x2; rw det_2x2; simp; ring; rw ← matrix.diagonal_one; rw matrix.diagonal_val_ne,
  repeat {rw [zero_mul]}, symmetry, apply sub_zero,
  intro h, rw fin.ext_iff at h, simp at h, exact h,
  ring,
  intro h, rw fin.ext_iff at h, simp at h, exact h,
  end

lemma unit_inv_mul : m.unit_inv * m = m.det • (1 : M₂) :=
  begin
  rw ← det_unit_inv,
  rw ← mul_unit_inv m.unit_inv,
  symmetry,
  rw unit_inv_unit_inv,
  end

lemma mul_add_assoc {T} [ring T] (x a b c d : T)
  : x * (a * b + c * d) = x * a * b + x * c * d:=
  calc x * (a * b + c * d)
      = x * (a * b) + x * (c * d) : mul_add x _ _
  ... = x * a * b + x * c * d : by repeat {rw mul_assoc}

lemma smul_mul (s : ℂ) : s • m * n = s • (m * n) :=
  begin rw [mul_2x2, mul_2x2], unfold has_scalar.smul,
  apply ext_2x2; simp; symmetry; apply mul_add_assoc,
  end

noncomputable def inv : M₂ := (det m)⁻¹ • unit_inv m

lemma inv_val (h : m.det ≠ 0) : inv m * m = 1 :=
  begin
  unfold inv,
  rw smul_mul,
  rw unit_inv_mul,
  rw smul_smul,
  field_simp,
  rw (div_self h),
  apply one_smul,
  end

lemma inv_inv : inv (inv m) = m :=
  begin
  unfold inv,
  end



lemma val_inv (h : m.det ≠ 0) : m * inv m = 1 :=
  begin

  end

noncomputable def mk_G₂ (h : det m ≠ 0) : G₂ :=
{ val := m,
  inv := inv m,
  val_inv := ,
  inv_val := inv_val m h }

end M₂
