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

lemma inf_eq {x : ℂ} : x ≠ 0 → (0 : ℂ⊙)⁻¹ = quotient.mk' ⟨x, 0⟩ :=
  begin
  intro h,
  apply quotient.sound,
  unfold fraction_wheel.pre_inv fraction_wheel.pre_mul,
  dsimp,
  use [x, 1, h, one_ne_zero]; dsimp,
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
  : P ⊥ → P 0⁻¹ -> (∀ c : ℂ, P (of_finite c)) -> (∀ z, P z)
  | P_bot P_inf P_c z :=
  quotient.induction_on' z $ λ z,
    match z with
    | ⟨z₁, z₂⟩ :=
      if z₂_0 : z₂ = 0
        then if z₁_0 : z₁ = 0
          then begin rw [z₂_0, z₁_0], exact P_bot end
          else begin rw [z₂_0, ← inf_eq z₁_0], exact P_inf end
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

def pre_mobius (m : M₂) : ℂ×ℂ → ℂ×ℂ :=
λ z, ⟨m 0 0 * z.1 + m 0 1 * z.2, m 1 0 * z.1 + m 1 1 * z.2⟩

noncomputable def as_mobius (m : M₂) : ℂ⊙ → ℂ⊙:=
  quotient.map' (pre_mobius m)
    begin
    intros x₀ x₁ x, cases x,
    use [x_sl, x_sr, x_sl_in_s, x_sr_in_s];
    unfold pre_mobius; simp; repeat {rw left_distrib};
    repeat {rw ← mul_assoc};
    repeat {rw mul_comm x_sl, rw mul_comm x_sr};
    repeat {rw mul_assoc};
    repeat {rw [x_fst_eq, x_snd_eq]},
    end

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


lemma smul_unit_inv (s : ℂ) : s • m.unit_inv = (s • m).unit_inv :=
  begin
  unfold unit_inv,
  unfold has_scalar.smul,
  apply ext_2x2; simp,
  end

lemma smul_det (s : ℂ) : (s • m).det = s * s * m.det :=
  begin
  rw [det_2x2, det_2x2],
  unfold has_scalar.smul,
  simp_rw fraction_wheel.mul_rearange,
  rw mul_sub,
  end

lemma inv_det_nonzero (h : m.det ≠ 0) : det m.inv ≠ 0 :=
  begin
  unfold inv,
  rw smul_det,
  rw det_unit_inv,
  rw mul_assoc,
  rw (inv_mul_cancel h),
  rw mul_one,
  rw ← inv_zero,
  intro h',
  apply h,
  revert h',
  exact (inv_inj'' (det m) 0).mp,
  end

lemma inv_inv_helper (d : ℂ) (d_ne_0 : d ≠ 0) : d⁻¹ * d⁻¹ * d * d = 1 :=
  calc d⁻¹ * d⁻¹ * d * d = d⁻¹ * d⁻¹ * (d * d) : by ring
    ... = d⁻¹ * d * (d⁻¹ * d) : fraction_wheel.mul_rearange d⁻¹ d⁻¹ d d
    ... = 1 * 1 : by simp_rw inv_mul_cancel d_ne_0
    ... = 1 : mul_one 1

lemma inv_inv (d_neq_0 : m.det ≠ 0) : inv (inv m) = m :=
  begin
  unfold inv,
  rw ← smul_unit_inv,
  rw unit_inv_unit_inv,
  rw smul_smul,
  have h : ((((m.det)⁻¹ • m.unit_inv).det)⁻¹ * (m.det)⁻¹) = (1 : ℂ),
    { rw ← mul_inv'',
      rw ← inv_one,
      congr,
      rw smul_det,
      rw det_unit_inv,
      apply inv_inv_helper m.det d_neq_0
    },
  rw h,
  apply one_smul,
  end

lemma val_inv (h : m.det ≠ 0) : m * inv m = 1 :=
  begin
  symmetry,
  have h' : det m.inv ≠ 0, by exact inv_det_nonzero _ h,
  calc 1 = inv (inv m) * inv m : (inv_val (inv m) h').symm
    ... = m * inv m : by rw (inv_inv m h)
  end

noncomputable def mk_G₂ (h : det m ≠ 0) : G₂ :=
{ val := m,
  inv := inv m,
  val_inv := val_inv m h,
  inv_val := inv_val m h }

end M_2x2

instance : nonzero (fin 2) :=
  begin constructor,
  unfold has_zero.zero has_one.one fin.of_nat,
  norm_num,
  end

lemma id_1_0 : (1 : M₂) 1 0 = 0 :=
  begin
  rw ← matrix.diagonal_one,
  rw (matrix.diagonal_val_ne one_ne_zero),
  exact fin.nonzero,
  end

lemma id_0_1 : (1 : M₂) 0 1 = 0 :=
  begin
  rw ← matrix.diagonal_one,
  rw (matrix.diagonal_val_ne' one_ne_zero),
  exact fin.nonzero,
  end

lemma id_0_0 : (1 : M₂) 0 0 = 1 :=
  begin
  rw ← matrix.diagonal_one,
  rw (matrix.diagonal_val_eq),
  end

lemma id_1_1 : (1 : M₂) 1 1 = 1 :=
  begin
  rw ← matrix.diagonal_one,
  rw (matrix.diagonal_val_eq),
  end

noncomputable def G₂.smul (g : G₂) := as_mobius g.val
local infix ` •' `:60 := G₂.smul

notation `z` := (has_zero.zero : ℂ⊙)

lemma unfold_zero_inv : (0 : ℂ⊙)⁻¹ = quotient.mk' (1,0) :=
  congr_arg quotient.mk' rfl

lemma G₂.one_smul (b) : 1 •' b = b :=
  begin
  revert b,
  unfold G₂.smul has_one.one,
  unfold1 monoid.one,
  unfold1 group.one, simp,
  rw ← matrix.diagonal_one,
  unfold as_mobius, simp,
  apply reimann_wheel.cases;
  try {unfold has_bot.bot};
  try {rw unfold_zero_inv};
  try {intro c, unfold of_finite fraction_wheel.of};
  { rw quotient.map'_mk',
    unfold pre_mobius,
    congr,
    { rw [id_0_0, id_0_1],
      rw [one_mul, zero_mul],
      simp,
    },
    { rw [id_1_0, id_1_1],
      rw [one_mul, zero_mul],
      simp,
    },
  },
  end

lemma G₂.mul_smul (x y : G₂) (b : ℂ⊙) : (x * y) •' b = x •' (y •' b) :=
  begin
  change as_mobius (x.val * y.val) b = as_mobius x.val (as_mobius y.val b),
  apply quotient.induction_on' b, clear b, intro b,
  unfold as_mobius,
  repeat {rw quotient.map'_mk'},
  apply congr_arg,
  cases b,
  unfold pre_mobius,
  rw M_2x2.mul_2x2, simp, split; ring,
  end

noncomputable instance : mul_action G₂ ℂ⊙ :=
{ smul := G₂.smul,
  one_smul := G₂.one_smul,
  mul_smul := G₂.mul_smul }
