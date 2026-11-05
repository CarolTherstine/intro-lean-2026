/-
Copyright (c) 2026 Guilherme Lima. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Guilherme Lima
-/
module

/- A deductive system for minimal propositional implication logic -/

@[expose] public section

namespace Hello.Logic

/-! ## Formula -/

/-- A formula is either an atom `n` or an implication of `A` to `B`. -/
inductive Formula where
| atom (n : Nat)
| imp (A B : Formula)
deriving BEq, ReflBEq, LawfulBEq, DecidableEq

namespace Formula

instance {n : Nat} : OfNat Formula n where
  ofNat := Formula.atom n

def toString : Formula → String
| .atom n => n.repr
| .imp A B => "(" ++ A.toString ++ "⊃" ++ B.toString ++ ")"

instance : ToString Formula where
  toString := Formula.toString

instance : Repr Formula where
  reprPrec f _ := f.toString

prefix:max "#" => Formula.atom
infixr:66 "⊃" => Formula.imp

end Formula

/- Some example formulas -/
#check (#0 : Formula)           -- (atom 0)
#check (0⊃1 : Formula)          -- (imp (atom 0) (atom 1))
#eval (0⊃1⊃2 : Formula)         -- (0⊃(1⊃2))
#eval ((0⊃1)⊃2 : Formula)       -- ((0⊃1)⊃2)

/-! ## Context -/

/-- A context is a list of formulas. -/
abbrev Context := List Formula

end Hello.Logic

namespace List

universe u
variable {α : Type u}

@[simp]
def delete [BEq α] [ReflBEq α] (a : α) :
    (l : List α) → List α
  | [] => []
  | x :: xs => match x == a with
    | true => List.delete a xs
    | false => x :: List.delete a xs

abbrev delete' [BEq α] [ReflBEq α] (l : List α) (a : α) := delete a l

infixl:68 " / " => List.delete'

theorem delete_filter [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    l.delete a = l.filter (λ b ↦ !(b == a)) := by
  induction l with
  | nil => rfl
  | cons b _ => simp!; if h : b = a then rw [h]; simp; trivial else
    rw [beq_false_of_ne h]; simp; trivial

theorem delete_nil [BEq α] [ReflBEq α] (a : α) : []/a = [] := rfl

theorem delete_head [BEq α] [ReflBEq α] (a : α) (l : List α) :
    (a :: l)/a = l/a := by simp

theorem subset_delete [BEq α] [LawfulBEq α] (a : α) (l : List α) :
    l/a ⊆ l := by
  induction l with
  | nil => simp
  | cons a' l' ih =>
    simp;
    if h : a' = a then
      rw [h]; simp; apply Subset.trans ih;
      apply List.subset_cons_of_subset; apply Subset.refl
    else
      rw [beq_false_of_ne h]; simp; apply Subset.trans ih;
      apply List.subset_cons_of_subset; apply Subset.refl

end List

namespace Hello.Logic

/-! ## Derivation -/

inductive Derivation : Context → Formula → Prop where

/-- Hypothesis introduction -/
| hypo (A : Formula) : Derivation [A] A

/-- Implication introduction -/
| impI {A B : Formula} {G H : Context} (d : Derivation G B) :
    A ∈ G → H = G/A → Derivation H (A⊃B)

/-- Implication elimination -/
| impE {A B : Formula} {G₁ G₂ H : Context}
    (d₁ : Derivation G₁ A) (d₂ : Derivation G₂ (A⊃B)) :
    H = G₁ ++ G₂ → Derivation H B

export Derivation (hypo impI impE)

infix:21 " ⊢ " => Derivation

macro "app " e:term : tactic =>
  `(tactic| apply ($e : _) <;> try simp +decide)

namespace Derivation

variable {A B C : Formula} {G G₁ G₂ : Context}

example : [] ⊢ A⊃A := by
  app impI (hypo A)

example : [] ⊢ (0⊃1)⊃(1⊃2)⊃(0⊃2) := by
  app impI (_ : [0⊃1] ⊢ (1⊃2)⊃(0⊃2))
  app impI (_ : [0⊃1, 1⊃2] ⊢ (0⊃2))
  app impI (_ : [0, 0⊃1, 1⊃2] ⊢ 2)
  app impE (_ : [0, 0⊃1] ⊢ 1) (_ : [1⊃2] ⊢ 1⊃2)
  · app impE (hypo 0) (hypo (0⊃1))
  · app hypo

theorem MP (d₁ : G₁ ⊢ A) (d₂ : G₂ ⊢ A⊃B) : G₁ ++ G₂ ⊢ B := by
  app impE d₁ d₂

theorem imp_trans (d₁ : G₁ ⊢ A⊃B) (d₂ : G₂ ⊢ B⊃C) : (G₁ ++ G₂)/A ⊢ A⊃C := by
  app impI (MP (MP (hypo A) d₁) d₂)

theorem deduct (d : G ⊢ B) : A ∈ G → (G/A ⊢ A⊃B) := by
  intro _; app impI d; trivial

theorem deduct_head (d : A :: G ⊢ B) : G/A ⊢ A⊃B := by
  suffices (A :: G)/A ⊢ A⊃B by rw [←List.delete_head]; trivial
  app deduct (A := A) d

end Derivation
