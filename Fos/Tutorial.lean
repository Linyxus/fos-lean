namespace Fos

/-!
Adapted from [the Coq version of this tutorial](https://github.com/lampepfl/fos-coq/blob/master/advanced.md), which itself is based on [a POPL 2008 workshop](https://www.cis.upenn.edu/~plclub/popl08-tutorial/).

# Before we begin

The point of this workshop is to give you a feel for what is it like to do proofs in Lean, and also to illustrate what the Curry-Howard isomorphism really is and what are its applications. This workshop is not graded, and you will not see Lean during the exam (though there's a big chance you'll see Curry-Howard, and you may see a fragment of CoC).

However, we cannot actually properly teach you how to do proofs in Lean or to explain everything we will do in details due to time constraints. In case you are interested in knowing more, check the following resources:
- [Coq version of this tutorial](https://github.com/lampepfl/fos-coq/blob/master/advanced.md). The content will be more or less the same, but it uses Coq instead of Lean. It also points to some other resources in Coq.
- [Natural number game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4). A game-like tutorial for Lean 4.
- [Glimpse of Lean](https://github.com/PatrickMassot/GlimpseOfLean). A introduction to Lean 4 for the impatient. It covers fundamental aspects of theorem proving in Lean 4, but also includes some independent topics about elementary analysis, abstract topology and mathematical logic.

# Coq vs CoC

During the lecture, you have already seen how we can formulate CoC on paper. In this notebook, we will be working with Coq, an interactive theorem assistant with a type system based on an extension of CoC. The differences are slight, but they are there, so let's start by inspecting them.

First things first: you can use the `#check` command to inspect types of terms.
!-/

#check 0

/-!
Naturally, we type `0` as `Nat`.
!-/

#check Nat

/-!
`Type` is like `*` in CoC. More to the point, `Type` in Lean is a kind of types that represent data (more on this in a second).
!-/

namespace MyNat

/-!
We can define our own types with the `inductive` construct:
!-/

inductive MyNat : Type where
| zero
| succ (n0 : MyNat)

/-!
The `inductive` form introduces an inductive data type, inductive in this case meaning being defined inductively. The above definition is basically the same as the following Scala definition:
```scala
sealed trait Nat
final case object Zero extends Nat
final case class Succ(n: Nat) extends Nat
```
We say that `zero` and `succ` are constructors for the `MyNat` type, since they are the fundamental/primitive way of constructing values of type `MyNat`. They are themselves values or functions:
!-/

#check MyNat.zero
#check MyNat.succ

open MyNat

/-!
`open` opens a namespace and introduces its definitions into the current scope. Previously, we had to write `MyNat.zero` and `MyNat.succ` to refer to the constructors, but now we can just write `zero` and `succ`.
!-/

#check zero
#check succ

/-!
The constructors can also be used to destruct/pattern match on values of type `MyNat`:
!-/

def add (n m : MyNat) : MyNat :=
  match n with
  | zero => m
  | succ n0 => succ (add n0 m)

/-!
Lean is an interactive theorem assistant, so we'd like to use it to do some proofs. Recall that by the Curry-Howard isomorphism, types are propositions and terms that inhabit them are proofs that those propositions are true. Then, if we want to do proofs about whether a number is even or not, we first thing need to define a type for this proposition. Specifically, if `n` is even, we would like to be able to construct a value of type `IsEven n` (note that `IsEven` will need to be a type operator). We can define `IsEven` as follows:
!-/

inductive IsEven : MyNat -> Prop where
| zeroIsEven : IsEven zero
| doubleSuccIsEven
  (n : MyNat)
  (p : IsEven n) :
  --------------------------------------
  IsEven (succ (succ n))

open IsEven

/-!
As expected, we needed to annotate `IsEven` with `MyNat -> Prop` as its type, meaning it's a type operator from nat's to a propositions (more on `Prop` in a second). We have two constructors for this proposition, and both of them now have annotations for their result types.

The first one, `zeroIsEven`, is a proof that 0 is even, and accordingly its type is `IsEven zero`.

The other one is more complicated. We can understand it as follows: if we want to prove that `n+2` is even, we need to have n (naturally) and we need a proof that `n` is even -- a value of type `IsEven n`.
!-/

#check fun (n : MyNat) =>
       fun (p : IsEven n) =>
       doubleSuccIsEven _ (doubleSuccIsEven _ p)

/-!
## Sets and Props
!-/

#check Type
#check Prop

/-!
## Alternative form of Inductive
!-/

namespace MyNatAlt

#check zero
#check succ

inductive MyNat' : Type where
  | zero : MyNat'
  | succ : MyNat' -> MyNat'

#check MyNat'.zero
#check MyNat'.succ

end MyNatAlt

end MyNat

namespace NB

inductive Term : Type where
  | yes : Term
  | no : Term
  | cond : Term -> Term -> Term -> Term
  | zero : Term
  | succ : Term -> Term
  | pred : Term -> Term
  | iszero : Term -> Term

open Term

#check cond (iszero zero) no yes

inductive BValue : Term -> Prop where
  | yes : BValue yes
  | no : BValue no

inductive NValue : Term -> Prop where
  | zero : NValue zero
  | succ : forall {t : Term},
    NValue t ->
    --------------------------------------
    NValue (succ t)

inductive Eval : Term -> Term -> Prop where
  | iftrue : forall {t1 t2 : Term},
    Eval (cond yes t1 t2) t1
  | iffalse : forall {t1 t2 : Term},
    Eval (cond no t1 t2) t2
  | ifcond : forall {t0 t1 t2 t0' : Term},
    Eval t0 t0' ->
    Eval (cond t0 t1 t2) (cond t0' t1 t2)
  | succ : forall {t t' : Term},
    Eval t t' ->
    Eval (succ t) (succ t')
  | predzero :
    Eval (pred zero) zero
  | predsucc : forall {t : Term},
    NValue t ->
    Eval (pred (succ t)) t
  | pred : forall {t t' : Term},
    Eval t t' ->
    Eval (pred t) (pred t')
  | iszerozero :
    Eval (iszero zero) yes
  | iszerosucc : forall {t : Term},
    NValue t ->
    Eval (iszero (succ t)) no
  | iszero : forall {t t' : Term},
    Eval t t' ->
    Eval (iszero t) (iszero t')

inductive EvalMany : Term -> Term -> Prop where
| refl : forall {t : Term},
  EvalMany t t
| step : forall {t1 t2 t3 : Term},
  Eval t1 t2 ->
  EvalMany t2 t3 ->
  EvalMany t1 t3

theorem e_succ_pred_succ : forall {t : Term},
  NValue t ->
  Eval (succ (pred (succ t))) (succ t) := by
  intros t
  intros Hn
  apply Eval.succ
  apply Eval.predsucc
  apply Hn

end NB

end Fos
