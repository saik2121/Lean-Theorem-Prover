--Propositions as Types
namespace mine
constant and : Prop -> Prop -> Prop 
constant Proof : Prop -> Type
constant implies : Prop → Prop → Prop
constant and_comm : Π p q : Prop, Proof (implies (and p q ) (and q p))
variables p q : Prop 
#check and_comm p q 
end mine

--Introducing Theorems
constants p q :Prop
theorem t1 (hp :p) (hq :q) : p :=hp
#check t1

-- using lemma/theorem and show and assume and from

theorem t5 : p->q->p:=
assume hp :p,
assume hq:q,
show p ,from hp


axiom hp : p
theorem t2 : q -> p:= t1 hp

#check t2

--Declaring types within theorem

theorem t3 (p q :Prop)(hp:p)(hq:q):p:=hp
#check t3

--The above holds true for any propositions p and q 
variables p q r s :Prop 
#check t3 (r->s)(s->r)

--Propositional Logic

--and

example (hp :p )(hq : q) : p∧q := and.intro hp hq 
#check λ (hp :p )(hq : q),and.intro hp hq

-- and.elim_left and and.elim_right

example (hp : p∧q) : p := and.left hp
#check λ(hp : p∧q),and.left hp

example (hp : p∧q) : q := and.right hp
#check λ(hp : p∧q),and.right hp

--proving q and p from p and q

example (hp : p ∧ q) : q ∧ p := and.intro (and.right hp) (and.left hp)


--angular brackets for and.intro

example (hp : p ∧ q):q ∧ p := ⟨ hp.right , hp.left ⟩ 
 
--Disjunction

--or intro rules : proving (p ∨ q ) from p or q

example (h:p):p ∨ q := or.intro_left q h
example (h:q):p ∨ q := or.intro_right p h

--or elimination rules : proving q ∨ p from p ∨ q , takes 3 arguments h : p∨q , either p true or q true

example (h: p∨q) : q ∨ p := 
or.elim h
(assume (h : p), show q ∨ p ,from or.intro_right q h)
(assume (h:q), show q∨p , from or.intro_left p h)


--Negation

--The proof ¬ p is derived from p->false. To show a contradiction we do hp:p hnp :¬ p
--thus proving false

--Proving (p->q)-> ¬q -> ¬p

example (hpq : p -> q)(hnq : ¬ q) : ¬ p :=
(assume hp :p , show false, from hnq (hpq hp))

--Proving anything follows from a contradiction using absurd 
-- Proving p -> ¬ p -> q

example (hp : p)( hnp : ¬ p):q := absurd hp hnp

--Proof of ¬p → q → (q → p) → r using absurd 

example (hnp : ¬ p)(hq : q)(hqp : q->p ):r:=
absurd (hqp hq) hnp

--Equivalence
--iff.intro h1 h2  proves p ↔ q from h1:p->q and h2: q->p

--Proving p∧q ↔ q∧p

theorem and_iff : p∧q ↔ q∧p:= iff.intro 
(assume h:p∧q,show q∧p , from and.intro (and.right h ) (and.left h))
(assume h:q∧ p,show p∧ q,from and.intro (and.right h) (and.left h))

#check and_iff p q 


