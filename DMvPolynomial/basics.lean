import Mathlib.Data.Dfinsupp.Basic
import Mathlib.Data.Finset.sort
import Mathlib.Data.Dfinsupp.Interval



section DMvPolynomial_Basics

variable {σ : Type}{R : Type}[CommSemiring R][DecidableEq σ][DecidableEq R]
{u : R → R → Prop}[DecidableRel u]
namespace DMvPolynomial

def DMvPolynomial (σ : Type) (R : Type) [CommSemiring R] [DecidableEq σ] :=
  Π₀ t : Π₀ x : σ, ℕ, R

protected instance DecidableEq : DecidableEq (DMvPolynomial σ R) :=
  Dfinsupp.instDecidableEqDfinsupp

instance Addcommmonoid : AddCommMonoid (DMvPolynomial σ R) :=
  Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid

instance Inhabited : Inhabited (DMvPolynomial σ R) :={
  default:=0
}

def Monomial (t : Π₀ x : σ, ℕ)(c : R) : DMvPolynomial σ R:=
  Dfinsupp.single t c

theorem zero (t : Π₀ x : σ, ℕ) : Monomial t 0 = 0:= by
  rw [Monomial, Dfinsupp.single_zero]

def Mul (p1 p2 : DMvPolynomial σ R) :DMvPolynomial σ R :=
  Dfinsupp.sum p1 (fun (t1 : Π₀ x : σ, ℕ)(c1 : R) ↦ 
  Dfinsupp.sum p2 (fun (t2 : Π₀ x : σ, ℕ)(c2 : R) ↦ 
  Monomial (t1+t2) (c1*c2)))

lemma monomialmul (t1 t2 : Π₀ x : σ, ℕ)(c1 c2 : R): 
Mul (Monomial t1 c1) (Monomial t2 c2) = 
Monomial (t1+t2) (c1*c2):=by
  rw [Mul, Monomial, 
  Dfinsupp.sum_single_index, Monomial,
  Dfinsupp.sum_single_index]
  simp only [mul_zero]
  apply Dfinsupp.single_zero
  rw [Monomial, Dfinsupp.sum_single_index]
  simp only [zero_mul]
  apply Dfinsupp.single_zero
  rw [Monomial]
  simp only [zero_mul]
  apply Dfinsupp.single_zero

theorem LeftDistrib (p q r : DMvPolynomial σ R) : Mul p (q+r) = Mul p q +Mul p r:=by
  rw [Mul, Mul, Mul, ←Dfinsupp.sum_add, Dfinsupp.sum, Dfinsupp.sum]
  apply congr_arg
  apply funext
  intro t1
  apply Dfinsupp.sum_add_index
  intro t11
  rw [mul_zero, Monomial]
  apply Dfinsupp.single_zero
  intro t0 c11 c22
  rw [mul_add, Monomial, Monomial, Monomial]
  apply Dfinsupp.single_add

instance RightDistrib (p q r : DMvPolynomial σ R) : Mul (p+q) r = Mul p r +Mul q r:=by
  rw [Mul, Mul, Mul, ←Dfinsupp.sum_add_index]
  simp only [zero_mul, Monomial, Dfinsupp.single_zero, Dfinsupp.sum_zero,
    forall_const]
  intros t0 c11 c22
  rw [←Dfinsupp.sum_add]
  simp only [Monomial, right_distrib, Dfinsupp.single_add]

instance MulComm (p q: DMvPolynomial σ R) : Mul p q = Mul q p:=by
  rw [Mul, Mul, Dfinsupp.sum_comm]
  simp only [add_comm, mul_comm]

instance ZeroMul (p : DMvPolynomial σ R) : Mul 0 p = 0:=by
  rw [Mul]
  apply Dfinsupp.sum_eq_zero
  intro x1
  apply Dfinsupp.sum_eq_zero
  intro x2
  rw [Monomial, Dfinsupp.single_eq_zero, Dfinsupp.zero_apply, zero_mul]

instance MulZero (p : DMvPolynomial σ R) : Mul p 0 = 0:=by
  rw [MulComm, ZeroMul]


-- A polynomial is a sum of its distinct monomials.
theorem Polynomial_sum_monomial (p : DMvPolynomial σ R) : 
Dfinsupp.sum p (fun (t : Π₀ x : σ, ℕ)(c : R) ↦ 
Monomial t c) = p:= by
  simp only [Monomial]
  rw [Dfinsupp.sum_single]

theorem Polynomial_linear_right (p q : DMvPolynomial σ R) : 
Dfinsupp.sum p (fun (t : Π₀ x : σ, ℕ)(c : R) ↦ 
Mul (Monomial t c) q) = 
Mul (Dfinsupp.sum p (fun (t : Π₀ x : σ, ℕ)(c : R) ↦ 
Monomial t c)) q:= by
  simp only [Mul, Monomial]
  rw [Dfinsupp.sum_single]
  apply congr_arg
  apply funext
  intro t1
  apply funext
  intro r1
  rw [Dfinsupp.sum_single_index]
  simp only [zero_mul, Dfinsupp.single_zero]
  rw [Dfinsupp.sum_zero]

theorem Polynomial_linear_left (p q : DMvPolynomial σ R) : 
Dfinsupp.sum p (fun (t : Π₀ x : σ, ℕ)(c : R) ↦ 
Mul q (Monomial t c)) = 
Mul q (Dfinsupp.sum p (fun (t : Π₀ x : σ, ℕ)(c : R) ↦ 
Monomial t c)):= by
  rw [MulComm, ←Polynomial_linear_right]
  apply congr_arg
  apply funext
  intro t1
  apply funext
  intro r1
  rw [MulComm]
  
theorem MulAssoc (p q r : DMvPolynomial σ R) : Mul (Mul p q) r = Mul p (Mul q r) := by
  have temp1 (p q r : DMvPolynomial σ R) :
  Mul p (Mul q r) =
  Dfinsupp.sum p (fun (t1 : Π₀ x : σ, ℕ)(c1 : R) ↦ 
  Dfinsupp.sum q (fun (t2 : Π₀ x : σ, ℕ)(c2 : R) ↦ 
  Dfinsupp.sum r (fun (t3 : Π₀ x : σ, ℕ)(c3 : R) ↦ 
  Monomial (t1+t2+t3) (c1*c2*c3))))
  simp only [←monomialmul, Polynomial_linear_left]
  rw [Mul]
  apply congr_arg
  apply funext
  intro t11
  apply funext
  intro r11
  rw [Mul, Dfinsupp.sum_sum_index]
  apply congr_arg
  apply funext
  intro t22
  apply funext
  intro r22
  rw [Dfinsupp.sum_sum_index, MulComm, Mul, Dfinsupp.sum_sum_index]
  apply congr_arg
  apply funext
  intro t33
  apply funext
  intro r33
  rw [Monomial, Dfinsupp.sum_single_index, eq_comm, Monomial,
    Dfinsupp.sum_single_index, monomialmul, Monomial, 
    Dfinsupp.sum_single_index, add_comm, add_assoc, mul_comm, mul_assoc]
  rw [Monomial, mul_zero, Dfinsupp.single_zero]
  simp only [Monomial, zero_mul, Dfinsupp.single_zero, Dfinsupp.sum_zero]
  rw [Monomial, mul_zero, Dfinsupp.single_zero]
  simp only [Monomial, zero_mul, Dfinsupp.single_zero, Dfinsupp.sum_zero,
  forall_const]
  simp only [←Dfinsupp.sum_add, Monomial, right_distrib, Dfinsupp.single_add,
  forall_const]
  simp only [Monomial, mul_zero, Dfinsupp.single_zero, forall_const]
  simp only [Monomial, left_distrib, Dfinsupp.single_add, forall_const]
  simp only [Monomial, mul_zero, Dfinsupp.single_zero, forall_const]
  simp only [Monomial, left_distrib, Dfinsupp.single_add, forall_const]
  simp [←Dfinsupp.sum_apply]
  have temp2 (p q r : DMvPolynomial σ R) :
  Mul (Mul p q) r =
  Dfinsupp.sum p (fun (t1 : Π₀ x : σ, ℕ)(c1 : R) ↦ 
  Dfinsupp.sum q (fun (t2 : Π₀ x : σ, ℕ)(c2 : R) ↦ 
  Dfinsupp.sum r (fun (t3 : Π₀ x : σ, ℕ)(c3 : R) ↦ 
  Monomial (t1+t2+t3) (c1*c2*c3))))
  rw [MulComm]
  simp only [Dfinsupp.sum_comm q]
  rw [Dfinsupp.sum_comm, temp1]
  apply congr_arg
  apply funext
  intro t33
  apply funext
  intro r33
  apply congr_arg
  apply funext
  intro t11
  apply funext
  intro r11
  apply congr_arg
  apply funext
  intro t22
  apply funext
  intro r22
  rw [add_comm _ t33, add_assoc, mul_comm _ r33, mul_assoc]
  rw [temp1, temp2]

theorem OneMul (p : DMvPolynomial σ R) : Mul (Monomial 0 1) p = p:=by
  rw [Mul, Monomial, Dfinsupp.sum_single_index]
  simp only [zero_add, one_mul, Monomial]
  rw [Dfinsupp.sum_single]
  apply Dfinsupp.sum_eq_zero
  intro x1
  rw [Monomial, zero_mul, Dfinsupp.single_zero]

instance MulOne (p : DMvPolynomial σ R) : Mul p (Monomial 0 1) = p:=by
  rw [MulComm, OneMul]

instance CommSemiring : CommSemiring (DMvPolynomial σ R) :=
{
  mul := Mul
  left_distrib := LeftDistrib
  right_distrib := RightDistrib
  zero_mul := ZeroMul
  mul_zero := MulZero
  mul_assoc := MulAssoc
  one := Monomial 0 1
  one_mul := OneMul
  mul_one := MulOne
  mul_comm := MulComm
}
end DMvPolynomial
