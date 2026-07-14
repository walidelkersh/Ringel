import Mathlib

open Complex BigOperators Real

variable (n : ℕ)

lemma exp_sum_zmod (ξ : ZMod (2 * n + 1)) :
    ∑ x : ZMod (2 * n + 1), (AddChar.zmod (2 * n + 1) ξ x : ℂ) =
      if ξ = 0 then (2 * n + 1 : ℂ) else 0 := by
  let ψ : AddChar (ZMod (2 * n + 1)) ℂ := AddChar.circleEquivComplex (AddChar.zmod (2 * n + 1) ξ)
  have H : ∑ x : ZMod (2 * n + 1), ψ x = if ψ = 0 then (2 * n + 1 : ℂ) else 0 := by
    have h1 := AddChar.sum_eq_ite ψ
    have h2 : (Fintype.card (ZMod (2 * n + 1)) : ℂ) = 2 * n + 1 := by simp
    rw [h2] at h1
    exact h1
  have h_iff : ψ = 0 ↔ ξ = 0 := by
    dsimp [ψ]
    have h_ne : NeZero (2 * n + 1) := ⟨by linarith⟩
    have h_zero : (0 : AddChar (ZMod (2 * n + 1)) ℂ) = AddChar.circleEquivComplex (AddChar.zmod (2 * n + 1) 0) := by
      ext x
      have : (0 : AddChar (ZMod (2 * n + 1)) ℂ) x = 1 := AddChar.zero_apply x
      rw [this]
      change (1 : ℂ) = ↑(AddChar.zmod (2 * n + 1) 0 x)
      have h_eval : AddChar.zmod (2 * n + 1) 0 = 1 := AddChar.zmod_zero (2 * n + 1)
      rw [h_eval]
      rfl
    rw [h_zero]
    rw [AddEquiv.apply_eq_iff_eq]
    exact AddChar.zmod_inj
  have H_change : ∑ x : ZMod (2 * n + 1), (AddChar.zmod (2 * n + 1) ξ x : ℂ) = ∑ x : ZMod (2 * n + 1), ψ x := rfl
  rw [H_change, H]
  by_cases h : ξ = 0
  · rw [if_pos h, if_pos (h_iff.mpr h)]
  · rw [if_neg h, if_neg (h_iff.not.mpr h)]

lemma char_symm (x y : ZMod (2 * n + 1)) :
    (AddChar.zmod (2 * n + 1) x y : ℂ) = (AddChar.zmod (2 * n + 1) y x : ℂ) := by
  have h_ne : NeZero (2 * n + 1) := ⟨by linarith⟩
  obtain ⟨x', rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨y', rfl⟩ := ZMod.intCast_surjective y
  congr 1
  -- Both are equal in Circle
  have h1 : AddChar.zmod (2 * n + 1) (x' : ZMod (2 * n + 1)) (y' : ZMod (2 * n + 1)) =
    Circle.exp (2 * Real.pi * (x' * y' / ↑(2 * n + 1))) := AddChar.zmod_intCast (2 * n + 1) x' y'
  have h2 : AddChar.zmod (2 * n + 1) (y' : ZMod (2 * n + 1)) (x' : ZMod (2 * n + 1)) =
    Circle.exp (2 * Real.pi * (y' * x' / ↑(2 * n + 1))) := AddChar.zmod_intCast (2 * n + 1) y' x'
  rw [h1, h2]
  congr 2
  ring

lemma char_sub (x y z : ZMod (2 * n + 1)) :
    (AddChar.zmod (2 * n + 1) x z : ℂ) * star (AddChar.zmod (2 * n + 1) x y : ℂ) =
    (AddChar.zmod (2 * n + 1) x (z - y) : ℂ) := by
  have h1 : star (AddChar.zmod (2 * n + 1) x y : ℂ) = ((AddChar.zmod (2 * n + 1) x y)⁻¹ : ℂ) := by
    exact (Circle.coe_inv_eq_conj _).symm
  rw [h1]
  -- Now we just need to use AddChar properties
  have h2 : (AddChar.zmod (2 * n + 1) x z : ℂ) * ((AddChar.zmod (2 * n + 1) x y)⁻¹ : ℂ) =
    (((AddChar.zmod (2 * n + 1) x z) * (AddChar.zmod (2 * n + 1) x y)⁻¹ : Circle) : ℂ) := by
    push_cast
    rfl
  rw [h2]
  congr 1
  rw [← div_eq_mul_inv, ← AddChar.map_sub_eq_div]

noncomputable def fourier_transform (f : ZMod (2 * n + 1) → ℂ) (ξ : ZMod (2 * n + 1)) : ℂ :=
  ∑ x : ZMod (2 * n + 1), f x * star (AddChar.zmod (2 * n + 1) ξ x : ℂ)

noncomputable def inner_product (f g : ZMod (2 * n + 1) → ℂ) : ℂ :=
  ∑ x : ZMod (2 * n + 1), f x * star (g x)

theorem parseval (f : ZMod (2 * n + 1) → ℂ) :
    inner_product n (fourier_transform n f) (fourier_transform n f) =
    (2 * n + 1 : ℂ) * inner_product n f f := by
  dsimp [inner_product, fourier_transform]
  calc
    ∑ x, (∑ x_1, f x_1 * star (AddChar.zmod (2 * n + 1) x x_1 : ℂ)) * star (∑ x_1, f x_1 * star (AddChar.zmod (2 * n + 1) x x_1 : ℂ))
      = ∑ x, (∑ y, f y * star (AddChar.zmod (2 * n + 1) x y : ℂ)) * (∑ z, star (f z) * (AddChar.zmod (2 * n + 1) x z : ℂ)) := by
        congr 1; ext x; congr 1
        rw [star_sum]
        congr 1; ext y
        rw [star_mul, star_star, mul_comm]
    _ = ∑ x, ∑ y, ∑ z, f y * star (f z) * ((AddChar.zmod (2 * n + 1) x z : ℂ) * star (AddChar.zmod (2 * n + 1) x y : ℂ)) := by
      congr 1; ext x
      rw [Finset.sum_mul]
      congr 1; ext y
      rw [Finset.mul_sum]
      congr 1; ext z
      ring
    _ = ∑ x, ∑ y, ∑ z, f y * star (f z) * (AddChar.zmod (2 * n + 1) x (z - y) : ℂ) := by
      congr 1; ext x; congr 1; ext y; congr 1; ext z
      rw [char_sub]
    _ = ∑ y, ∑ z, ∑ x, f y * star (f z) * (AddChar.zmod (2 * n + 1) x (z - y) : ℂ) := by
      rw [Finset.sum_comm]
      congr 1; ext y
      rw [Finset.sum_comm]
    _ = ∑ y, ∑ z, f y * star (f z) * ∑ x, (AddChar.zmod (2 * n + 1) x (z - y) : ℂ) := by
      congr 1; ext y; congr 1; ext z
      rw [Finset.mul_sum]
    _ = ∑ y, ∑ z, f y * star (f z) * if z - y = 0 then (2 * n + 1 : ℂ) else 0 := by
      congr 1; ext y; congr 1; ext z
      have h : ∑ x, (AddChar.zmod (2 * n + 1) x (z - y) : ℂ) = ∑ x, (AddChar.zmod (2 * n + 1) (z - y) x : ℂ) := by
        congr 1; ext x; exact char_symm n x (z - y)
      rw [h, exp_sum_zmod]
    _ = ∑ y, ∑ z, if z = y then f y * star (f y) * (2 * n + 1 : ℂ) else 0 := by
      congr 1; ext y; congr 1; ext z
      have h_iff : z - y = 0 ↔ z = y := sub_eq_zero
      by_cases h : z = y
      · rw [if_pos h, if_pos (h_iff.mpr h), h]
      · rw [if_neg h, if_neg (h_iff.not.mpr h)]
        ring
    _ = ∑ y, f y * star (f y) * (2 * n + 1 : ℂ) := by
      congr 1; ext y
      simp
    _ = (2 * n + 1 : ℂ) * inner_product n f f := by
      dsimp [inner_product]
      rw [Finset.mul_sum]
      congr 1; ext y
      ring
