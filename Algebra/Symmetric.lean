import Mathlib.Algebra.Group.Defs
import Mathlib.Init.Function
--------------------------------------------------------------------------------

namespace Symmetric

def endocomp (f : α -> α) (g : α -> α) := λ a => g (f a)

def id : α -> α := λ a => a

theorem endocomp_assoc
        (f : α -> α) (g : α -> α) (h : α -> α)
        : endocomp (endocomp f g) h = endocomp f (endocomp g h)
        := by
  rfl

theorem comp_id (f : α -> α) : endocomp f id = f := by
  rfl

theorem id_comp (f : α -> α) : endocomp id f = f := by
  rfl

theorem bij_inv
        (f : α -> α)
        : Function.Bijective f -> ∃ f', endocomp f f' = id
        := by
  intro ⟨ha, hb⟩ 

instance symmetric : Group (A -> A) where
  mul := endocomp
  mul_assoc := endocomp_assoc
  one := id
  one_mul := id_comp
  mul_one := comp_id
  inv := sorry
  mul_left_inv := sorry

