def compose {α β γ : Type} (f : β -> γ) (g : α -> β) := λ x => f (g x)

def cons {α : Type} (a : α) (as : List α) : List α :=
  List.cons a as

#check cons
#check cons 2
#check @cons Nat

