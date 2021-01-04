-- definitions
--first way of defining 
def succesor : ℕ -> ℕ := λ (x: ℕ) , x+5
#reduce  succesor 5
def succesor1 (x: ℕ ): ℕ :=x+5
#check succesor1 5

--lamda abstractions

#check λ x:nat,x+5
#check λ (x: ℕ )(y: ℕ ),x+y
 
--Applying lambda abstarctions as functions

--constants α β : Type
--constant p : α 
--constant q : β 
--#check λ (x: α)( y: β ),x
--#check (λ (x: α)( y: β ),x) p q

--Using let functions

#reduce let y:= 2+2 in y*y

def t (x: ℕ ): ℕ := let y:= x+x in y*y
#eval t 2

--Variables and sections

--def compose (α β γ : Type) (g : α -> β ) ( f : γ -> α ) ( x: γ ):β := g (f x) 
variables (α β γ : Type*)
variable x : α 
def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)

--Namespaces 
namespace foo
def f (x: ℕ ) : ℕ := x+7
#check f
end foo
#check foo.f

--Nested namespaces

namespace f1 
def b (a : bool)( c: bool) := tt && (a && c)
#check b
namespace f2
def b (a : nat)( c: nat) := tt 
#check b
end f2
#check b
#check f2.b
end f1



