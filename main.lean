import Mathlib.Data.Dfinsupp.Basic
import Mathlib.Data.Finset.sort
import Mathlib.Data.Dfinsupp.Interval



section DMvPolynomial_Basics

variable {σ : Type}{R : Type}[CommSemiring R][DecidableEq σ][DecidableEq R]

namespace DMvPolynomial

def DMvPolynomial (σ : Type) (R : Type) [CommSemiring R] [DecidableEq σ] :=
  Π₀ (t : (Π₀ (x : σ), ℕ)), R
instance Addcommmonoid : AddCommMonoid (DMvPolynomial σ R) :=
  Dfinsupp.instAddCommMonoidDfinsuppToZeroToAddMonoid


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
def natcast (n : ℕ): DMvPolynomial σ R :=
  Monomial 0 n

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
  simp only [<-monomialmul, Polynomial_linear_left]
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
  simp only [<-Dfinsupp.sum_add, Monomial, right_distrib, Dfinsupp.single_add,
  forall_const]
  simp only [Monomial, mul_zero, Dfinsupp.single_zero, forall_const]
  simp only [Monomial, left_distrib, Dfinsupp.single_add, forall_const]
  simp only [Monomial, mul_zero, Dfinsupp.single_zero, forall_const]
  simp only [Monomial, left_distrib, Dfinsupp.single_add, forall_const]
  simp [<-Dfinsupp.sum_apply]
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

section CommDMvpolynomial

open DMvPolynomial

variable {σ : Type}{R : Type}[CommRing R][DecidableEq σ][DecidableEq R]

def neg (p : DMvPolynomial σ R) : 
DMvPolynomial σ R:=
  Dfinsupp.sum p fun (t : Π₀ x : σ, ℕ)(r : R) ↦ 
  Monomial t (-r)
  
lemma addLeft_neg (p : DMvPolynomial σ R) : neg p + p = 0:= by
  rw [neg]
  conv=>
    lhs
    congr
    {}
    {rw [←Polynomial_sum_monomial p]}
  rw [←Dfinsupp.sum_add]
  simp only [Monomial]
  apply Dfinsupp.sum_eq_zero
  intro t
  rw [←Dfinsupp.single_add, add_left_neg, Dfinsupp.single_zero]

instance commring [CommRing R] : CommRing (DMvPolynomial σ R) :=
{
  neg := neg
  add_left_neg := addLeft_neg
  mul_comm := MulComm
}

def lex (r : σ → σ → Prop) (s : ℕ → ℕ → Prop) (x y : Π₀ x : σ, ℕ) : Prop :=
  ∃ i, (∀ (j : σ), r j i → x j = y j) ∧ s (x i) (y i)

def colex (r : σ → σ → Prop) (s : ℕ → ℕ → Prop) (x y : Π₀ x : σ, ℕ) : Prop :=
  ∃ i, (∀ (j : σ), r i j → x j = y j) ∧ s (x i) (y i)

inductive grlex (fin1 fin2 : Π₀ x : ℕ, ℕ) : Prop where
  | degree : fin1.support.card < fin2.support.card → grlex fin1 fin2
  | lex    : fin1.support.card = fin2.support.card → lex ( · < · ) ( · < · ) fin1 fin2 → grlex fin1 fin2

inductive grevlex (fin1 fin2 : Π₀ x : ℕ, ℕ) : Prop where
  | degree : fin1.support.card < fin2.support.card → grevlex fin1 fin2
  | lex    : fin1.support.card = fin2.support.card → colex ( · < · ) ( · < · ) fin2 fin1 → grevlex fin1 fin2

lemma nonzero_polynomial_support_nonempty
 (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop) 
(p: DMvPolynomial σ R)[inst : DecidableRel r]
[inst : IsTrans (Π₀ x : σ, ℕ) r] [inst : IsAntisymm (Π₀ x : σ, ℕ) r] 
[inst : IsTotal (Π₀ x : σ, ℕ) r]
[nonzero : NeZero p] : Finset.sort r p.support ≠ []:= by
  rw [ne_eq, ←List.toFinset_eq_empty_iff, Finset.sort_toFinset,
  Dfinsupp.support_eq_empty]
  apply nonzero.out

def LeadingTerm (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop) [DecidableRel r] 
[IsTrans (Π₀ x : σ, ℕ) r] [IsAntisymm (Π₀ x : σ, ℕ) r] 
[IsTotal (Π₀ x : σ, ℕ) r](p : DMvPolynomial σ R)[NeZero p] : Π₀ x : σ, ℕ:=
  List.getLast (Finset.sort r p.support) 
  (nonzero_polynomial_support_nonempty r p)

def LeadingCoeff (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop) [DecidableRel r] 
[IsTrans (Π₀ x : σ, ℕ) r] [IsAntisymm (Π₀ x : σ, ℕ) r] 
[IsTotal (Π₀ x : σ, ℕ) r](p : DMvPolynomial σ R)[NeZero p] : R:=
  p.toFun (LeadingTerm r p)

def LeadingMon (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop) [DecidableRel r] 
[IsTrans (Π₀ x : σ, ℕ) r] [IsAntisymm (Π₀ x : σ, ℕ) r] 
[IsTotal (Π₀ x : σ, ℕ) r](p : DMvPolynomial σ R)[NeZero p] : DMvPolynomial σ R:=
  Monomial (LeadingTerm r p) (LeadingCoeff r p)

def TermDivPolyVersion (t : Π₀ x : σ, ℕ)(p1 : DMvPolynomial σ R){le : (x : σ)→  
(t1 : p1.support)→  t x ≤ ((t1 : p1.support) : Π₀ x : σ, ℕ) x} : 
DMvPolynomial σ R :=
  (Dfinsupp.sum p1 (fun (t1 : Π₀ x : σ, ℕ)(r1 : R) ↦
  Monomial (t1-t) (r1)))

def TermDiv (t1 t : Π₀ x : σ, ℕ)(le : (x : σ) → t x ≤ t1 x) : Π₀ x : σ, ℕ :=
  t1-t

def Lcm (t1 t2 : Π₀ x : σ, ℕ) :  Π₀ x : σ, ℕ:=
  { toFun := fun (i : σ) ↦ max (t1.toFun i) (t2.toFun i),
    support' := Trunc.mk {
      val := (t1.support ∪ t2.support).val
      property := by
        intro x
        by_cases h : (x ∈ t1.support) ∨ (x ∈ t2.support)
        apply Or.intro_left
        rw [Finset.union_val, Multiset.mem_union, Finset.mem_val, 
        Finset.mem_val]
        exact h
        apply Or.intro_right
        rw [Dfinsupp.toFun_eq_coe, Dfinsupp.toFun_eq_coe]
        simp only [ge_iff_le]
        rw [Nat.max_eq_zero_iff, ←Dfinsupp.not_mem_support_iff, 
        ←Dfinsupp.not_mem_support_iff, ←not_or]
        exact h
    }
    : Π₀ x : σ, ℕ }

instance LcmDivisibleLeft (t1 t2 : Π₀ x : σ, ℕ) : (x : σ) → t1 x ≤ Lcm t1 t2 x := by
  rw [_root_.Lcm]
  simp only [Dfinsupp.toFun_eq_coe, Finset.union_val, Dfinsupp.coe_mk',
  ge_iff_le, le_max_iff, le_refl, true_or, or_true, and_self, implies_true]

instance LcmDivisibleRight (t1 t2 : Π₀ x : σ, ℕ) : (x : σ) → t2 x ≤ Lcm t1 t2 x := by
  rw [_root_.Lcm]
  simp only [Dfinsupp.toFun_eq_coe, Finset.union_val, Dfinsupp.coe_mk',
  ge_iff_le, le_max_iff, le_refl, true_or, or_true, and_self, implies_true]

def SPolynomial (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop)
[DecidableRel r] [IsTrans (Π₀ x : σ, ℕ) r] [IsAntisymm (Π₀ x : σ, ℕ) r]
[IsTotal (Π₀ x : σ, ℕ) r](f g: DMvPolynomial σ R) 
[nonzero : NeZero f] [nonzero2 : NeZero g]: DMvPolynomial σ R :=
  Monomial (TermDiv (Lcm (LeadingTerm r f) (LeadingTerm r g))
  (LeadingTerm r f) (LcmDivisibleLeft (LeadingTerm r f) (LeadingTerm r g))) (LeadingCoeff r g) * f
  - Monomial (TermDiv (Lcm (LeadingTerm r f) (LeadingTerm r g))
  (LeadingTerm r g) (LcmDivisibleRight (LeadingTerm r f) (LeadingTerm r g))) (LeadingCoeff r f) * g
