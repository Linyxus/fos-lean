import LeanInfer

namespace Fos

inductive Nat : Type where
| zero : Nat
| succ : Nat → Nat

open Nat

def add : Nat → Nat → Nat
| zero, n => n
| succ m, n => succ (add m n)

theorem add_n_zero : ∀ {n},
  add n zero = n := by
  intros n
  induction n
  case zero =>
    rw [add]
  case succ n ih =>
    rw [add, ih]

theorem add_n_succ_m : ∀ {n m},
  add n (succ m) = succ (add n m) := by
  intro n m
  induction n generalizing m
  case zero => simp [add]
  case succ n ih => simp [add, ih]

end Fos
