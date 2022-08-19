prelude
import Leanbin.Init.Meta.Default
import Leanbin.Init.Logic
import Leanbin.Init.Data.Nat.Lemmas
import Leanbin.Init.Data.Char.Basic

namespace Char

theorem val_of_nat_eq_of_is_valid {n : Nat} : Nat.isValidChar n → (ofNat n).toNat = n := by
  intro h <;> unfold ofNat <;> rw [dif_pos h] <;> rfl

theorem val_of_nat_eq_of_not_is_valid {n : Nat} : ¬Nat.isValidChar n → (ofNat n).toNat = 0 := by
  intro h <;> unfold ofNat <;> rw [dif_neg h] <;> rfl

theorem of_nat_eq_of_not_is_valid {n : Nat} : ¬Nat.isValidChar n → ofNat n = ofNat 0 := by
  intro h <;> apply eq_of_veq <;> rw [val_of_nat_eq_of_not_is_valid h] <;> rfl

theorem of_nat_ne_of_ne {n₁ n₂ : Nat} (h₁ : n₁ ≠ n₂) (h₂ : Nat.isValidChar n₁) (h₃ : Nat.isValidChar n₂) :
    ofNat n₁ ≠ ofNat n₂ := by
  apply ne_of_vne
  rw [val_of_nat_eq_of_is_valid h₂, val_of_nat_eq_of_is_valid h₃]
  assumption

end Char

