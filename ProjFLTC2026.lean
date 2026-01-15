import ProjFLTC2026.Basic
import Mathlib.ModelTheory.Semantics

-- from here on we shall work on model theory
-- signatures will be encoded with LEAN Languages
-- Interpretation Structures will be encoded with LEAN Structures

-- This is a how the key concepts are represented in Lean

/-
variable (Signature : FirstOrder.Language) -- signature Σ
variable (Interpretion_Structure : Type)[Signature.Structure Interpretion_Structure]
Interpretation Structure I
variable (Assignment : α → Interpretion_Structure) Assignment ρ over I

def Term.interpret (t : Signature.Term α) : (Interpretion_Structure):= Interpretation of terms with Iρ
t.realize Assignment

satistfaction
def Formula.sat (φ : Signature.Formula α) :=
    φ.Realize Assignment
def BoundedFormula.sat (φ : Signature.BoundedFormula α n) :=
    φ.Realize Assignment
def Sentence.sat (φ : Signature.Sentence) :=
    φ.Realize Interpretion_Structure


entailment i.e. every model of a theory Θ satisfies φ
def Formula.entail (φ : Signature.Formula α) :=
    Thery.Model Interpretion_Structure → φ.Realize Assignment
def Bounded.entail (φ : Signature.BoundedFormula α n) :=
    Theory.Model Interpretion_Structure →  φ.Realize Assignment
def Sentence.entail (φ : Signature.Sentence) :=
    Theory.Model Interpretion_Structure → φ.Realize Interpretion_Structure
-/


open FirstOrder

theorem and_def (S : FirstOrder.Language)
                (M : Type) [S.Structure M]
                (ρ : α → M)
                (ψ φ : S.Formula α) :
    ((φ ⊓ ψ).Realize ρ) ↔ (φ.Realize ρ ∧ ψ.Realize ρ) :=
by
    simp
--

def S_pow (S : α → α) : ℕ → α → α
    | 0,     x => x
    | k + 1, x => S (S_pow S k x)

structure SModel where
    elem : Type
    zero : elem
    S :  elem → elem
    Ax1 : ∀ {x}, ¬ S x = zero
    Ax2 : ∀ {x y}, S x = S y → x = y
    Ax3 : ∀ {x}, (¬ x = zero) → ∃ y, S y = x
    Ax4 : ∀ {k : ℕ} {x : elem}, S_pow S k x = x


theorem Ssquared (M : SModel) :
    ∀ x y, S_pow M.S 2 x = S_pow M.S 2 y → x = y :=
by
intro x y h
have h1 : M.S x = M.S y := M.Ax2 h
have h2 : x = y := M.Ax2 h1
exact h2

theorem Sn (M : SModel) (k : ℕ) :
    ∀ x y, S_pow M.S k x = S_pow M.S k y → x = y :=
by
    induction k with


    | zero =>
        intro x y h
        simp [S_pow] at h
        exact h
    | succ d hd =>
        intro x y h
        have h1 : S_pow M.S d x = S_pow M.S d y :=
            M.Ax2 h
        apply hd at h1
        exact h1









universe u v

inductive SFunc : α → Type
| zero : SFunc 0
| succ : SFunc 1

inductive SRel : α → Type
|eq : SRel 2

def SSig : FirstOrder.Language := ⟨SFunc, SRel⟩ -- Simple signature with 0, S() and ≃

--abbrev eq : SSig.Relations 2 := .eq

-- Defining the notation
notation:50 t " ≅  " s =>
  FirstOrder.Language.BoundedFormula.rel SRel.eq ![t, s]

notation:50  "S("t")" =>
  FirstOrder.Language.Term.func SFunc.succ ![t]

notation:50 "zero" =>
  FirstOrder.Language.Term.func SFunc.zero ![]

--Auxiliary recursive function to represent applying S() k times
def succPow (n : ℕ) (t : SSig.Term α) :(SSig.Term α) :=
    match n with
    |0 => t
    |k + 1 => S(succPow k t)

notation:50  "S^["k"]("t")" =>
  succPow k t

def S1 : SSig.Sentence := -- First Axiom
    ∀' (S(&(0)) ≅  zero).not

def S2 : SSig.Sentence := -- Second Axiom
    ∀' ∀' ((S(&(0)) ≅ S(&(1))).imp (&(0) ≅ &(1)))

def S3 : SSig.Sentence := -- Third Axiom
    ∀' ∃' ((&(1) ≅ zero).not.imp (S(&(0)) ≅ &(1)))

def S4 (k : ℕ) : SSig.Sentence := -- Fourth Axiom, actually ℵ₀ sentences
    ∀' ((S^[k](&(0))) ≅ &(0)).not


def STheory : SSig.Theory :=
    {S1, S2, S3} ∪ {S4 (k + 1) | k : ℕ}
-- S4 actually represents one sentence for every natural number
-- We use k+1 to skip over ¬ x ≅ x, which is obviously false

def double_cycle : SSig.Sentence :=
    ∀' ∀' ((S^[2](&(0)) ≅ S^[2](&(1))).imp (&(0) ≅ &(1)))



theorem doubleS2 (M : Type)[SSig.Structure M]
                 (ρ : α ⊕ ℕ → M):
                 STheory.Model M → double_cycle.Realize M :=
by

    simp
    intro h
    intro x
    intro y
    intro hSS
    have hS2 : S2.Realize M :=
        by
        apply h S2
        simp [STheory]

    have hS2_xy := hS2 x y
    let env : Fin 2 → M
    | ⟨0, _⟩ => x
    | ⟨1, _⟩ => y
    apply hS2_xy
    simp [succPow] at hSS
    def env_Sxy : Fin 2 → M
    |⟨0, _⟩ => S(x).realize default env
    | ⟨1, _⟩ => S(y).realize default env
