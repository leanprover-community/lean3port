prelude
import Leanbin.Init.Data.Nat.Basic

namespace Nat

protected def div_core (y : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x => if h : 0 < y ∧ y ≤ x then div_core fuel (x - y) + 1 else 0

protected def div (x y : ℕ) : ℕ :=
  Nat.divCore y x x

instance : Div Nat :=
  ⟨Nat.divₓ⟩

protected def mod_core (y : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x => if h : 0 < y ∧ y ≤ x then mod_core fuel (x - y) else x

protected def mod (x y : ℕ) : ℕ :=
  Nat.modCore y x x

instance : Mod Nat :=
  ⟨Nat.modₓ⟩

end Nat

