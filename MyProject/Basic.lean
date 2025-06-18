import Mathlib
open Finset BigOperators
open Std





inductive AExp where
  | const : ℕ → AExp
  | var   : String → AExp
  | add   : AExp → AExp → AExp
  | sub   : AExp → AExp → AExp
  | mul   : AExp → AExp → AExp
deriving Repr, DecidableEq

inductive BExp where
  | True  : BExp
  | False : BExp
  | eq    : AExp → AExp → BExp
  | le    : AExp → AExp → BExp
  | not   : BExp → BExp
  | and   : BExp → BExp → BExp
deriving Repr, DecidableEq




abbrev Store := HashMap String ℕ

def emptyStore : Store := {}

def update (σ : Store) (x : String) (v : ℕ) : Store :=
  σ.insert x v

def lookup (σ : Store) (x : String) : ℕ :=
  σ.getD x 0


def aeval (a : AExp) (σ : Store) : ℕ :=
  match a with
  | AExp.const n   => n
  | AExp.var x     => lookup σ x
  | AExp.add b c   => aeval b σ + aeval c σ
  | AExp.sub b c   => aeval b σ - aeval c σ
  | AExp.mul b c   => aeval b σ * aeval c σ

def beval (b : BExp) (σ : Store) : Bool :=
  match b with
  | BExp.True      => true
  | BExp.False     => false
  | BExp.eq h g    => aeval h σ == aeval g σ
  | BExp.le h g    => aeval h σ ≤ aeval g σ
  | BExp.not c     => ¬ beval c σ
  | BExp.and a c   => beval a σ ∧ beval c σ


inductive Com where
  | skip     : Com
  | assign   : String → AExp → Com
  | seq      : Com → Com → Com
  | ite      : BExp → Com → Com → Com
  | while    : BExp → Com → Com
  | randbit  : String → Com
deriving Repr, DecidableEq



def oneStep : (Com × Store) × ℚ → List ((Com × Store) × ℚ)
  | ((Com.skip, _), _) => []
  | ((Com.assign x n, σ), r) =>
      [((Com.skip, update σ x (aeval n σ)), r)]
  | ((Com.seq Com.skip c2, σ), r) =>
      [((c2, σ), r)]
  | ((Com.seq c1 c2, σ), r) =>
      oneStep ((c1, σ), r) |>.map (fun ((c1', σ'), p) => ((Com.seq c1' c2, σ'), p))
  | ((Com.ite b ct cf, σ), r) =>
      if beval b σ then [((ct, σ), r)] else [((cf, σ), r)]
  | ((Com.while b c, σ), r) =>
      if beval b σ then [((Com.seq c (Com.while b c), σ), r)] else [((Com.skip, σ), r)]
  | ((Com.randbit x, σ), r) =>
      [((Com.skip, update σ x 0), r * (1/2)), ((Com.skip, update σ x 1), r * (1/2))]




def eval : ℕ → Com × Store → List ((Com × Store) × ℚ)
  | 0, cfg => [ (cfg, 1.0) ]
  | (Nat.succ n), cfg => List.flatten (List.map oneStep (eval n cfg))




def storeEq (σ σ' : Store) : Bool :=
  σ.toList == σ'.toList




def terminates_in_n (n : ℕ) (cfg : Com × Store) (σ' : Store) : ℚ :=
  let configs := eval n cfg
  List.sum (List.map (Aux σ') configs)
where
  Aux (σ' : Store): (Com × Store) × ℚ → ℚ :=
    fun ((c, σ), r) => if c = Com.skip ∧ storeEq σ σ' then r else 0




theorem HashLem: HashMap.insert ∅ "x" 1 = Std.HashMap.ofList [("x", 1)] := by
  rw [Std.HashMap.ofList_singleton]


noncomputable def terminates_in (cfg : Com × Store) (σ' : Store) : ℝ :=
  ∑' i : ℕ , terminates_in_n i cfg σ'

def prog : Com :=
  Com.while
    (BExp.and (BExp.eq (AExp.var "x") (AExp.const 1))
              (BExp.eq (AExp.var "y") (AExp.const 1)))
    (Com.seq (Com.randbit "x") (Com.randbit "y"))







def startstate : Store := update (update emptyStore "x" 1) "y" 1
def termstate1 : Store := update (update emptyStore "x" 0) "y" 0
def termstate2 : Store := update (update emptyStore "x" 1) "y" 0
def termstate3 : Store := update (update emptyStore "x" 0) "y" 1


#eval (eval 0 (prog, startstate))
#eval (eval 1 (prog, startstate))
#eval (eval 2 (prog, startstate))
#eval (eval 3 (prog, startstate))
#eval (eval 4 (prog, startstate))
#eval (eval 5 (prog, startstate))
#eval (eval 6 (prog, startstate))
#eval (eval 7 (prog, startstate))


#eval (eval 11 (prog, startstate))



#eval terminates_in_n 0 (prog, startstate) termstate1
#eval terminates_in_n 1 (prog, startstate) termstate1
#eval terminates_in_n 2 (prog, startstate) termstate1
#eval terminates_in_n 3 (prog, startstate) termstate1
#eval terminates_in_n 4 (prog, startstate) termstate1
#eval terminates_in_n 5 (prog, startstate) termstate1
#eval terminates_in_n 6 (prog, startstate) termstate1



#eval terminates_in_n 11 (prog, startstate) termstate1
#eval terminates_in_n 16 (prog, startstate) termstate1
#eval terminates_in_n 21 (prog, startstate) termstate1














theorem main : terminates_in (prog, startstate) termstate1 = 1/3 := by sorry




lemma firstlemma (n : ℕ) : terminates_in_n (6 + 5*n) (prog, startstate) termstate1 = (1/4)^(n + 1) := by
  induction n with
  | zero =>
      simp
      unfold terminates_in_n


      have helper1 : (List.map oneStep [((prog, startstate), 1.0)]).flatten = oneStep ((prog, startstate), 1.0) := by sorry


      have helper2 : beval ((BExp.eq (AExp.var "x") (AExp.const 1)).and (BExp.eq (AExp.var "y") (AExp.const 1))) (update (update emptyStore "x" 1) "y" 1) = true := by sorry


      have helper3 : beval (BExp.eq (AExp.var "x") (AExp.const 1)) (update (update emptyStore "x" 1) "y" 1) = true := by sorry



      have helper2 : eval 6 (prog, startstate) = [] := by sorry
      sorry


lemma secondlemma (n : ℕ) : ¬ (∃ (k : ℕ ), 6 + 5*k = n) → terminates_in_n n (prog, startstate) termstate1 = 0 := by sorry


lemma thirdlemma (N : ℕ): ∑ i ∈ range (N), terminates_in_n (i + 1) (prog, startstate) termstate1 =
                        (1-(1/4)^(N))/3 := by sorry
