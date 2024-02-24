-- This module serves as the root of the `Bitblast` library.
-- Import modules here that should be built as part of the library.
import «Bitblast».Basic
import Lean.Meta.Tactic.NormBv
-- import Lean.Elab.Tactic.NormBv

@[bv_concat]
theorem BitVec.concat_eq_concat_iff (x y : BitVec w) (a b : Bool) :
    concat x a = concat y b ↔ a = b ∧ x = y := by
  constructor
  · intro h
    replace h : (concat x a).toNat = (concat y b).toNat := by rw [h]
    simp at h
    obtain rfl : a = b := by
      cases a <;> cases b <;> (try rfl)
      · replace h : x.toNat * 2 % 2 = (y.toNat * 2 + 1) % 2 := by simp_all [h]
        simp [Nat.add_mod] at h
      · replace h : y.toNat * 2 % 2 = (x.toNat * 2 + 1) % 2 := by simp_all [h]
        simp [Nat.add_mod] at h
    replace h := Nat.add_right_cancel h
    replace h := Nat.mul_right_cancel Nat.zero_lt_two h
    obtain rfl := BitVec.eq_of_toNat_eq h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

attribute [bv_concat] and_true true_and BitVec.of_length_zero BitVec.concat_or_concat
  BitVec.add_eq_adc
  Bool.xor_false Bool.false_xor
  Bool.atLeastTwo_false_left Bool.atLeastTwo_false_mid Bool.atLeastTwo_false_right
  Bool.atLeastTwo_true_left Bool.atLeastTwo_true_mid Bool.atLeastTwo_true_right

@[bv_concat]
theorem BitVec.concat_adc_concat_snd (x y : BitVec w) (a b c : Bool) :
    (adc (concat x a) (concat y b) c).2
    = concat (adc x y (Bool.atLeastTwo a b c)).2 (xor (xor a b) c) := by
  sorry

example (x y : BitVec 4) : x + y = y + x := by
  bitblast
  /-
  b✝⁷ b✝⁶ b✝⁵ b✝⁴ b✝³ b✝² b✝¹ b✝: Bool
  ⊢ xor b✝⁷ b✝⁶ = xor b✝⁶ b✝⁷ ∧
    xor (xor b✝⁵ b✝⁴) (b✝⁷ && b✝⁶) = xor (xor b✝⁴ b✝⁵) (b✝⁶ && b✝⁷) ∧
      xor (xor b✝³ b✝²) (Bool.atLeastTwo b✝⁵ b✝⁴ (b✝⁷ && b✝⁶)) =
          xor (xor b✝² b✝³) (Bool.atLeastTwo b✝⁴ b✝⁵ (b✝⁶ && b✝⁷)) ∧
        xor (xor b✝¹ b✝) (Bool.atLeastTwo b✝³ b✝² (Bool.atLeastTwo b✝⁵ b✝⁴ (b✝⁷ && b✝⁶))) =
          xor (xor b✝ b✝¹) (Bool.atLeastTwo b✝² b✝³ (Bool.atLeastTwo b✝⁴ b✝⁵ (b✝⁶ && b✝⁷)))
  -/
  sorry
