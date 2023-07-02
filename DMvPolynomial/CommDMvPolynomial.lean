import DMvPolynomial.basics

section CommDMvpolynomial

open DMvPolynomial

namespace CommDMvpolynomial

variable {σ : Type}{R : Type}[CommRing R][DecidableEq σ][DecidableEq R]
--{rel : σ → σ → Prop}[DecidableRel rel]

--[IsTrans σ rel][IsAntisymm σ rel][IsAntisymm R s]

def neg (p : DMvPolynomial σ R) : 
DMvPolynomial σ R:=
  Dfinsupp.sum p (fun (t : Π₀ x : σ, ℕ)(r : R) ↦ 
  Monomial t (-r))
  
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