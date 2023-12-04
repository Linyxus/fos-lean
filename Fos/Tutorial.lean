namespace Fos

inductive Nat : Type
  | zero
  | succ (n0 : Nat)

#check Nat
#check Nat.zero
#check Nat.succ

end Fos
