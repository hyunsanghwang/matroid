import DMvPolynomial.basics
import DMvPolynomial.CommDMvPolynomial
import DMvPolynomial.order

open DMvPolynomial CommDMvpolynomial order

variable {σ : Type}{R : Type}[DecidableEq σ][DecidableEq R][CommRing R]

namespace DMvPolynomial

def Term (var : List ℕ) : Π₀ x : ℕ, ℕ := 
  { toFun := fun x : ℕ ↦ List.getD var x 0,
      support' := Trunc.mk {
        val := Multiset.range (List.length var)
        property := by
          intro i
          by_cases h : List.length var ≤ i
          apply Or.intro_right
          apply List.getD_eq_default
          exact h
          apply Or.intro_left
          rw [not_le] at h
          rw [Multiset.mem_range]
          exact h
          }
      : Π₀ x : ℕ, ℕ }

def Monomial' (coeff : ℚ) (var : List ℕ) : DMvPolynomial ℕ ℚ:= 
  Monomial (Term var) coeff

def Term.toList (t : (Π₀ x : ℕ, ℕ)) : List ℕ := 
  if h : t=0 then [] 
  else List.map t (List.range ((Finset.max' t.support (NonzeroDfinsuppNonemptysupport t  h))+1))

def Pol.toList (p : DMvPolynomial ℕ ℚ) : List (Π₀ x : ℕ, ℕ):=
  p.support.sort (lex' Nat.lt (· < ·))

def evaluation (p : DMvPolynomial ℕ ℚ) (vals : List ℚ) : DMvPolynomial ℕ ℚ:=
  let rec evalterm : (Π₀ x : ℕ, ℕ) → Nat → Π₀ x : ℕ, ℕ
    | a, 0   => a
    | a, i+1 => evalterm (a.update i 0) i
  let rec evalcoeff : ℚ → (Π₀ x : ℕ, ℕ) → Nat → ℚ
    | c, _, 0   => c
    | c, term, i+1 => (evalcoeff c term i) * (vals[i]! ^ term.toFun i)
  let rec main : Nat → DMvPolynomial ℕ ℚ
    | 0   => 0
    | i+1 => (main i) + (Monomial (evalterm (Pol.toList p)[i]! vals.length) 
    (evalcoeff (p.toFun (Pol.toList p)[i]!) (Pol.toList p)[i]! vals.length))
  main p.support.card

def permutation (p : DMvPolynomial ℕ ℚ) (perm : List ℕ) : DMvPolynomial ℕ ℚ:=
  let rec permterm : (Π₀ x : ℕ, ℕ) → (Π₀ x : ℕ, ℕ) → Nat → Π₀ x : ℕ, ℕ
    | _, a, 0 => a
    | term, a, 1 => a.update perm[0]! (term.toFun perm[perm.length-1]!)
    | term, a, i+1 => permterm term (a.update perm[i]! (a.toFun perm[i-1]!)) i
  let rec main : Nat → DMvPolynomial ℕ ℚ
    | 0   => 0
    | i+1 => (main i) + (Monomial (permterm (Pol.toList p)[i]! (Pol.toList p)[i]! perm.length)
     (p.toFun (Pol.toList p)[i]!))
  main p.support.card

def PolynomialViewer (p : DMvPolynomial ℕ ℚ) : List String := 
  List.map (fun i : List ℕ ↦ 
  ite (Term i ∈ p.support) (toString (p.toFun (Term i)) ++ " " ++ List.toString i) "") 
  (List.map Term.toList (p.support.sort (lex' Nat.lt (· < ·))))

#eval PolynomialViewer (evaluation (Monomial' (-2.5) ([1,0,3,1]) + Monomial' (3.5) ([1,3,3,1]) + Monomial' (2.5) ([])) ([4,2]))

def a: Finset (DMvPolynomial ℕ ℚ) :={(Monomial' (-2.5) ([1,0,3,1]) + Monomial' (3.5) ([1,3,3,1]) + Monomial' (2.5) ([])),
(Monomial' (-2.5) ([2,0,3,1]) + Monomial' (3.5) ([1,3,0,1]) + Monomial' (2.5) ([]))}

#check a.sort (lex'' (lex' Nat.lt (· < ·)) (· < ·))
#eval List.map PolynomialViewer (a.sort (lex'' (lex' Nat.lt (· < ·)) (· < ·)))