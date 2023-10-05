import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Use
import Std.Tactic.Basic
import Algebra.MyGroup
--------------------------------------------------------------------------------
open MyGroup
namespace Iso
--------------------------------------------------------------------------------

def Homomorphic [MyGroup G] [MyGroup G'] (f : G -> G')
                := ∀ (g h : G), f (g * h) = f g * f h

def Isomorphic [MyGroup G] [MyGroup G'] (f : G -> G')
               := Homomorphic f ∧ Function.Bijective f

