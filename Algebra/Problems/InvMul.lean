import Mathlib.Algebra.Group.Defs
import Mathlib.Data.List.Basic
--------------------------------------------------------------------------------
namespace InvMul
open List

variable {G : Type*} [Group G]

def Product {α : Type*} [Monoid α] : List α -> α
| nil       => 1
| cons a as => a * Product as

@[simp]
theorem product_nil [Monoid α] : Product ([] : List α) = 1 := by
  rfl

theorem product_cons
        [Monoid α] (a : α) (as : List α)
        : Product (a :: as) = a * Product as
        := by rfl

theorem product_append
        [Monoid α] (as bs : List α)
        : Product (as ++ bs) = Product as * Product bs
        := by
  induction as with
  | nil =>
    simp
  | cons k ks ih =>
    conv =>
      lhs
      rw [cons_append, product_cons, ih]
    rw [product_cons]
    rw [mul_assoc]

theorem product_singleton [Monoid α] (a : α) : Product [a] = a := by
  rw [product_cons]
  simp

theorem one_inv : 1⁻¹ = (1 : G) := by
  rw [<- one_mul 1⁻¹, mul_right_inv]

theorem inv_product (a b : G) : (a*b)⁻¹ = b⁻¹ * a⁻¹ := by
  simp

theorem concat_nil (as : List α) : as ++ [] = as := by
  simp

-- (a₁a₂...aₙ)⁻¹ = aₙ⁻¹aₙ₋₁⁻¹...a₁⁻¹
example (as : List G) : (Product as)⁻¹ = Product (map Inv.inv (reverse as)) := by
  induction as with
  | nil =>
    rw [product_nil, one_inv]
    have h : @reverse G [] = [] := by rfl
    have i : @map G _ Inv.inv [] = [] := by rfl
    rw [h, i, product_nil]
  | cons k ks ih =>
    rw [product_cons, inv_product, ih]
    rw [reverse_cons, map_append, product_append]
    conv =>
      rhs
      rw [map_cons, map_nil]
      rw [product_singleton]

