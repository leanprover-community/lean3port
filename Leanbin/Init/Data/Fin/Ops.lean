prelude 
import Leanbin.Init.Data.Nat.Default 
import Leanbin.Init.Data.Fin.Basic

namespace Finₓ

open Nat

variable {n : Nat}

protected def succ : Finₓ n → Finₓ (succ n)
| ⟨a, h⟩ => ⟨Nat.succ a, succ_lt_succ h⟩

def of_nat {n : Nat} (a : Nat) : Finₓ (succ n) :=
  ⟨a % succ n, Nat.mod_ltₓ _ (Nat.zero_lt_succₓ _)⟩

private theorem mlt {n b : Nat} : ∀ {a}, n > a → b % n < n
| 0, h => Nat.mod_ltₓ _ h
| a+1, h =>
  have  : n > 0 := lt_transₓ (Nat.zero_lt_succₓ _) h 
  Nat.mod_ltₓ _ this

protected def add : Finₓ n → Finₓ n → Finₓ n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a+b) % n, mlt h⟩

protected def mul : Finₓ n → Finₓ n → Finₓ n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a*b) % n, mlt h⟩

private theorem sublt {a b n : Nat} (h : a < n) : a - b < n :=
  lt_of_le_of_ltₓ (Nat.sub_leₓ a b) h

protected def sub : Finₓ n → Finₓ n → Finₓ n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨(a+n - b) % n, mlt h⟩

-- error in Init.Data.Fin.Ops: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private theorem modlt {a b n : nat} (h₁ : «expr < »(a, n)) (h₂ : «expr < »(b, n)) : «expr < »(«expr % »(a, b), n) :=
begin
  cases [expr b] ["with", ident b],
  { simp [] [] [] ["[", expr mod_zero, "]"] [] [],
    assumption },
  { have [ident h] [":", expr «expr < »(«expr % »(a, succ b), succ b)] [],
    apply [expr nat.mod_lt _ (nat.zero_lt_succ _)],
    exact [expr lt_trans h h₂] }
end

protected def mod : Finₓ n → Finₓ n → Finₓ n
| ⟨a, h₁⟩, ⟨b, h₂⟩ => ⟨a % b, modlt h₁ h₂⟩

private theorem divlt {a b n : Nat} (h : a < n) : a / b < n :=
  lt_of_le_of_ltₓ (Nat.div_le_selfₓ a b) h

protected def div : Finₓ n → Finₓ n → Finₓ n
| ⟨a, h⟩, ⟨b, _⟩ => ⟨a / b, divlt h⟩

instance : HasZero (Finₓ (succ n)) :=
  ⟨⟨0, succ_pos n⟩⟩

instance : HasOne (Finₓ (succ n)) :=
  ⟨of_nat 1⟩

instance : Add (Finₓ n) :=
  ⟨Finₓ.add⟩

instance : Sub (Finₓ n) :=
  ⟨Finₓ.sub⟩

instance : Mul (Finₓ n) :=
  ⟨Finₓ.mul⟩

instance : Mod (Finₓ n) :=
  ⟨Finₓ.mod⟩

instance : Div (Finₓ n) :=
  ⟨Finₓ.div⟩

theorem of_nat_zero : @of_nat n 0 = 0 :=
  rfl

theorem add_def (a b : Finₓ n) : (a+b).val = (a.val+b.val) % n :=
  show (Finₓ.add a b).val = (a.val+b.val) % n from
    by 
      cases a <;> cases b <;> simp [Finₓ.add]

theorem mul_def (a b : Finₓ n) : (a*b).val = (a.val*b.val) % n :=
  show (Finₓ.mul a b).val = (a.val*b.val) % n from
    by 
      cases a <;> cases b <;> simp [Finₓ.mul]

theorem sub_def (a b : Finₓ n) : (a - b).val = (a.val+n - b.val) % n :=
  by 
    cases a <;> cases b <;> rfl

theorem mod_def (a b : Finₓ n) : (a % b).val = a.val % b.val :=
  show (Finₓ.mod a b).val = a.val % b.val from
    by 
      cases a <;> cases b <;> simp [Finₓ.mod]

theorem div_def (a b : Finₓ n) : (a / b).val = a.val / b.val :=
  show (Finₓ.div a b).val = a.val / b.val from
    by 
      cases a <;> cases b <;> simp [Finₓ.div]

theorem lt_def (a b : Finₓ n) : (a < b) = (a.val < b.val) :=
  show Finₓ.Lt a b = (a.val < b.val) from
    by 
      cases a <;> cases b <;> simp [Finₓ.Lt]

theorem le_def (a b : Finₓ n) : (a ≤ b) = (a.val ≤ b.val) :=
  show Finₓ.Le a b = (a.val ≤ b.val) from
    by 
      cases a <;> cases b <;> simp [Finₓ.Le]

theorem val_zero : (0 : Finₓ (succ n)).val = 0 :=
  rfl

-- error in Init.Data.Fin.Ops: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
def pred {n : nat} : ∀ i : fin (succ n), «expr ≠ »(i, 0) → fin n
| ⟨a, h₁⟩, h₂ := ⟨a.pred, begin
   have [ident this] [":", expr «expr ≠ »(a, 0)] [],
   { have [ident aux₁] [] [":=", expr vne_of_ne h₂],
     dsimp [] [] [] ["at", ident aux₁],
     rw [expr val_zero] ["at", ident aux₁],
     exact [expr aux₁] },
   exact [expr nat.pred_lt_pred this h₁]
 end⟩

end Finₓ

