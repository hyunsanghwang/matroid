import DMvPolynomial.basics
import DMvPolynomial.CommDMvPolynomial

section order

open DMvPolynomial CommDMvpolynomial

namespace order

variable {σ : Type}{R : Type}[DecidableEq σ][DecidableEq R][CommSemiring R]
--{r: σ → σ → Prop}[DecidableRel r][IsTrans σ r][IsAntisymm σ r][IsTotal σ r]
--{s : N → N → Prop}[DecidableRel s][IsTrans N s][IsAntisymm N s][IsTotal N s]


def lex' (r : σ → σ → Prop) (s : ℕ → ℕ → Prop) (x y : Π₀ x : σ, ℕ)
: Prop :=
  x = y ∨ ∃ i, (∀ (j : σ), r j i → x j = y j) ∧ s (x i) (y i)

def colex (r : σ → σ → Prop) (s : ℕ → ℕ → Prop) (x y : Π₀ x : σ, ℕ) : Prop :=
  ∃ i, (∀ (j : σ), r i j → x j = y j) ∧ s (x i) (y i)

inductive grlex (fin1 fin2 : Π₀ x : ℕ, ℕ) : Prop where
  | degree : fin1.support.card < fin2.support.card → grlex fin1 fin2
  | lex    : fin1.support.card = fin2.support.card → lex' Nat.lt ( · < · ) fin1 fin2 → grlex fin1 fin2

inductive grevlex (fin1 fin2 : Π₀ x : ℕ, ℕ) : Prop where
  | degree : fin1.support.card < fin2.support.card → grevlex fin1 fin2
  | lex    : fin1.support.card = fin2.support.card → colex ( · < · ) ( · < · ) fin2 fin1 → grevlex fin1 fin2

lemma tool1 (a b : Π₀ x : ℕ, ℕ) (sub1 : a-b=0) : a=b ∨ (∃ i, (∀ (j : ℕ), Nat.lt j i → a j = b j) ∧ a i < b i):=by
  rw [FunLike.ext_iff] at sub1
  simp only [ge_iff_le, Dfinsupp.coe_tsub, Pi.sub_apply, Dfinsupp.coe_zero, Pi.zero_apply,
  tsub_eq_zero_iff_le] at sub1
  by_contra h
  rw [not_or, not_exists, ←ne_eq] at h
  simp only [not_and, not_lt] at h
  rw [←iff_false_intro h.left, FunLike.ext_iff]
  intro x
  apply Nat.strong_rec_on x
  intro
  rw [le_antisymm_iff, imp_and]
  apply And.intro
  intro 
  apply sub1
  apply h.right

lemma tool2 (a b : Π₀ x : ℕ, ℕ) (sub1 : ¬a-b=0)(sub2 : b-a=0) : ¬(a=b ∨ (∃ i, (∀ (j : ℕ), Nat.lt j i → a j = b j) ∧ a i < b i)):=by
  rw [FunLike.ext_iff, not_forall] at sub1
  simp only [ge_iff_le, Dfinsupp.coe_tsub, Pi.sub_apply, Dfinsupp.coe_zero, Pi.zero_apply, tsub_eq_zero_iff_le,
  not_le] at sub1
  rw [FunLike.ext_iff] at sub2
  simp only [ge_iff_le, Dfinsupp.coe_tsub, Pi.sub_apply, Dfinsupp.coe_zero, Pi.zero_apply,
  tsub_eq_zero_iff_le] at sub2
  rw [not_or]
  apply And.intro
  rw [←ne_eq, FunLike.ne_iff]
  simp only [ne_iff_lt_or_gt]
  rw [exists_or]
  apply Or.intro_right
  apply sub1
  rw [not_exists]
  intro
  rw [not_and]
  apply imp_intro
  rw [not_lt]
  apply sub2

lemma NonzeroDfinsuppNonemptysupport (t : (Π₀ x : σ, ℕ))(nonzero : ¬t = 0) : Finset.Nonempty t.support:= by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty, Dfinsupp.support_eq_empty] at h
  rw [←not_iff_false_intro h]
  exact nonzero

lemma tool3 (a b : Π₀ x : ℕ, ℕ) (sub1 : ¬a-b=0)(sub2 : ¬b-a=0)
(sub3 : List.map (b-a) (List.range ((Finset.max' (b-a).support (NonzeroDfinsuppNonemptysupport (b-a) sub2))+1)) >
List.map (a-b) (List.range ((Finset.max' (a-b).support (NonzeroDfinsuppNonemptysupport (a-b) sub1))+1)))
 : a=b ∨ (∃ i, (∀ (j : ℕ), Nat.lt j i → a j = b j) ∧ a i < b i):=by
  sorry

lemma tool4 (a b : Π₀ x : ℕ, ℕ) (sub1 : ¬a-b=0)(sub2 : ¬b-a=0)
(sub3 : ¬(List.map (b-a) (List.range ((Finset.max' (b-a).support (NonzeroDfinsuppNonemptysupport (b-a) sub2))+1)) >
List.map (a-b) (List.range ((Finset.max' (a-b).support (NonzeroDfinsuppNonemptysupport (a-b) sub1))+1))))
 : ¬(a=b ∨ (∃ i, (∀ (j : ℕ), Nat.lt j i → a j = b j) ∧ a i < b i)):=by
  sorry

instance lex'.decidable (a b : Π₀ x : ℕ, ℕ) : Decidable (a=b ∨ (∃ i, (∀ (j : ℕ), Nat.lt j i → a j = b j) ∧ a i < b i)):=
  if sub1 : a-b=0 then isTrue (tool1 a b sub1) else
    if sub2 : b-a=0 then isFalse (tool2 a b sub1 sub2) else
      if lt : List.map (b-a) (List.range ((Finset.max' (b-a).support (NonzeroDfinsuppNonemptysupport (b-a) sub2))+1)) >
      List.map (a-b) (List.range ((Finset.max' (a-b).support (NonzeroDfinsuppNonemptysupport (a-b) sub1))+1)) then 
      isTrue (tool3 a b sub1 sub2 lt) else isFalse (tool4 a b sub1 sub2 lt)

instance lex'.DecidableRel : DecidableRel (lex' Nat.lt (· < ·)):= lex'.decidable

instance lex'.Trans : IsTrans (Π₀ x : ℕ, ℕ) (lex' Nat.lt ( · < · )) where
  trans:=by
    intro a b c h1 h2
    by_cases first : a=b
    rw [first]
    exact h2
    by_cases second : b=c
    rw [←second]
    exact h1
    rw [lex', or_iff_right] at h1
    rw [lex', or_iff_right] at h2
    let ⟨i1, h11⟩ := h1
    let ⟨i2, h22⟩ := h2
    rw [lex']
    apply Or.intro_right
    by_cases h : i1<i2
    use i1
    apply And.intro
    intro j
    intro h3
    rw [h11.left, h22.left]
    apply lt_trans h3 h
    exact h3
    rw [←h22.left]
    apply h11.right
    exact h
    rw [not_lt] at h
    use i2
    apply And.intro
    intro j
    intro h3
    rw [h11.left, h22.left]
    exact h3
    apply lt_of_lt_of_le h3 h
    by_cases h4 : i2=i1
    rw [h4] at h22
    rw [h4]
    apply lt_trans h11.right h22.right
    rw [←Ne.def] at h4
    rw [h11.left]
    exact h22.right
    rw [Nat.lt_eq, lt_iff_le_and_ne]
    apply And.intro
    exact h
    exact h4
    exact second
    exact first

instance lex'.Antisymm : IsAntisymm (Π₀ x : ℕ, ℕ) (lex' Nat.lt (· < ·)) where
  antisymm:= by
    intro a b h1 h2
    by_cases first : a=b
    exact first
    rw [lex', or_iff_right] at h1
    rw [lex', or_iff_right] at h2
    let ⟨i1, h11⟩ := h1
    let ⟨i2, h22⟩ := h2
    rw [FunLike.ext_iff]
    by_contra h
    by_cases h001 : i1 < i2
    have ht : a i1 = b i1
    rw [h22.left]
    rw [Nat.lt_eq]
    exact h001
    rw [←not_iff_false_intro h11.right]
    apply Eq.not_lt ht
    by_cases h002 : i1 = i2
    rw [←and_not_self_iff (a i1 < b i1)]
    apply And.intro
    exact h11.right
    rw [h002, not_lt]
    apply le_of_lt h22.right
    have ht : a i2 = b i2
    rw [h11.left]
    rw [Nat.lt_eq]
    rw [not_lt] at h001
    rw [←ne_eq] at h002
    apply lt_of_le_of_ne h001
    apply Ne.symm
    exact h002
    rw [←not_iff_false_intro h22.right, not_lt]
    apply Eq.le ht
    rw [←ne_eq] at first
    rw [←ne_eq]
    apply Ne.symm
    exact first
    exact first

instance lex'.Total : IsTotal (Π₀ x : ℕ, ℕ) (lex' Nat.lt (· < ·)) where
  total := by
    intro a b
    rw [lex', lex']
    by_cases h : a = b
    apply Or.intro_left
    apply Or.intro_left
    exact h
    rw [eq_comm]
    rw [←or_or_distrib_left]
    apply Or.intro_right
    rw [FunLike.ext_iff, not_forall] at h
    by_contra h02
    rw [not_or, not_exists, not_exists, ←forall_and] at h02
    simp only [not_and, eq_comm, ←imp_and, not_lt, ←le_antisymm_iff,
    Nat.lt_eq] at h02
    rw [←not_iff_false_intro h, not_exists_not]
    simp at h02
    intro n
    apply Nat.strong_rec_on n h02

def Pol.toList (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop)[DecidableRel r]
[IsTrans (Π₀ x : σ, ℕ) r][IsAntisymm (Π₀ x : σ, ℕ) r][IsTotal (Π₀ x : σ, ℕ) r]
(p : DMvPolynomial σ R) : List (Π₀ x : σ, ℕ):=
  p.support.sort r

def lex'' (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop) (s : R → R → Prop) (p1 p2 : DMvPolynomial σ R)
: Prop :=
  p1 = p2 ∨ ∃ i, (∀ (j : Π₀ x : σ, ℕ), r j i → p1.toFun j = p2.toFun j) ∧ s (p1.toFun i) (p2.toFun i)

lemma tool1' (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop)[DecidableRel r]
[IsTrans (Π₀ x : σ, ℕ) r][IsAntisymm (Π₀ x : σ, ℕ) r][IsTotal (Π₀ x : σ, ℕ) r]
(s : R → R → Prop)(p1 p2 : DMvPolynomial σ R)(sub1 : Pol.toList r p1 = Pol.toList r p2) : 
p1=p2 ∨ (∃ i, (∀ (j : Π₀ x : σ, ℕ), r j i → p1.toFun j = p2.toFun j) ∧ s (p1.toFun i) (p2.toFun i)):=by sorry

lemma tool2' (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop)[DecidableRel r]
[IsTrans (Π₀ x : σ, ℕ) r][IsAntisymm (Π₀ x : σ, ℕ) r][IsTotal (Π₀ x : σ, ℕ) r]
(s : R → R → Prop)(p1 p2 : DMvPolynomial σ R)
(sub1 : ¬Pol.toList r p1 = Pol.toList r p2)(lex1: List.Lex r (Pol.toList r p1) (Pol.toList r p2)) : 
p1=p2 ∨ (∃ i, (∀ (j : Π₀ x : σ, ℕ), r j i → p1.toFun j = p2.toFun j) ∧ s (p1.toFun i) (p2.toFun i)):= by sorry

lemma tool3' (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop)[DecidableRel r]
[IsTrans (Π₀ x : σ, ℕ) r][IsAntisymm (Π₀ x : σ, ℕ) r][IsTotal (Π₀ x : σ, ℕ) r]
(s : R → R → Prop)(p1 p2 : DMvPolynomial σ R)
(sub1 : ¬Pol.toList r p1 = Pol.toList r p2)(lex1: ¬List.Lex r (Pol.toList r p1) (Pol.toList r p2)) : 
¬(p1=p2 ∨ (∃ i, (∀ (j : Π₀ x : σ, ℕ), r j i → p1.toFun j = p2.toFun j) ∧ s (p1.toFun i) (p2.toFun i))):= by sorry

instance lex''.decidable (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop)[DecidableRel r]
[IsTrans (Π₀ x : σ, ℕ) r][IsAntisymm (Π₀ x : σ, ℕ) r][IsTotal (Π₀ x : σ, ℕ) r]
(s : R → R → Prop)(p1 p2 : DMvPolynomial σ R) : 
Decidable (p1=p2 ∨ (∃ i, (∀ (j : Π₀ x : σ, ℕ), r j i → p1.toFun j = p2.toFun j) ∧ s (p1.toFun i) (p2.toFun i))):=
  if eq : (Pol.toList r p1 = Pol.toList r p2) then isTrue (tool1' r s p1 p2 eq) else
    if lex1: List.Lex r (Pol.toList r p1) (Pol.toList r p2) then isTrue (tool2' r s p1 p2 eq lex1) else
      isFalse (tool3' r s p1 p2 eq lex1)

instance lex''.DecidableRel (r : (Π₀ x : σ, ℕ) → (Π₀ x : σ, ℕ) → Prop)[DecidableRel r]
[IsTrans (Π₀ x : σ, ℕ) r][IsAntisymm (Π₀ x : σ, ℕ) r][IsTotal (Π₀ x : σ, ℕ) r]
(s : R → R → Prop): DecidableRel (lex'' r s):= lex''.decidable r s

instance lex''.Trans : IsTrans (DMvPolynomial σ R) (lex'' r s) where
  trans:=by sorry

instance lex''.Antisymm : IsAntisymm (DMvPolynomial σ R) (lex'' r s) where
  antisymm:=by sorry

instance lex''.Total : IsTotal (DMvPolynomial σ R) (lex'' r s) where
  total:=by sorry