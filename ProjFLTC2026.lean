import ProjFLTC2026.Basic
import Mathlib.ModelTheory.Semantics

theorem fa_to_ex (α : Type) (P Q : α → Prop):
    (∀ x, P x → Q x) → (∃ x, P x) → ∃ x, Q x :=
by
    intro h hP
    rcases hP with ⟨ x, hx⟩
    exact ⟨ x, h x hx⟩

theorem nf_r_exnot (α : Type) (P : α → Prop) :
  (¬∀ x, P x) →  ∃ x, ¬ P x :=
by
  contrapose!
  intro h
  exact h

theorem e_comm (P Q : Prop) :
    P ∧ Q ↔ Q ∧ P :=
by
    constructor
    intro h
    exact ⟨h.right, h.left⟩
    intro h
    exact ⟨h.right, h.left⟩

theorem ant_switch (P Q R : Prop) :
    (P ↔ Q) → (Q → R) → (P → R) :=
by
    intro h hQR hP
    apply hQR
    apply h.mp
    exact hP

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

open FirstOrder
-/
theorem and_def (S : FirstOrder.Language)
                (M : Type) [S.Structure M]
                (ρ : α → M)
                (ψ φ : S.Formula α) :
    ((φ ⊓ ψ).Realize ρ) ↔ (φ.Realize ρ ∧ ψ.Realize ρ) :=
by
    simp
--

universe u v

inductive SFunc : ℕ → Type
| zero : SFunc 0
| succ : SFunc 1

inductive SRel : ℕ → Type
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
    ∀' (S(&(0)) ≅ zero).not

def S2 : SSig.Sentence := -- Second Axiom
    ∀' ∀' ((S(&(0)) ≅ S(&(1))).imp (&(0) ≅ &(1)))

def S3 : SSig.Sentence := -- Third Axiom
    ∀' ∃' ((&(1) ≅ zero).not.imp (S(&(0)) ≅ &(1)))

def S4 (k : ℕ) : SSig.Sentence := -- Fourth Axiom, actually ℵ₀ sentences
    ∀' ((S^[k](&(0))) ≅ &(0)).not


def STheory : SSig.Theory :=
    {S1, S2, S3} ∪ {S4 (k + 1) | k : ℕ}
-- S4 actually represents one sentence for every natural number
-- We use k+1 to skip the trivial case x=y → x=y

def double_cycle : SSig.Sentence :=
    ∀' ∀' ((S^[2](&(0)) ≅ S^[2](&(1))).imp (&(0) ≅ &(1)))

theorem doubleS2 (M : Type)[SSig.Structure M]
                 (ρ : α → M):
                 STheory.Model M → double_cycle.Realize M :=
by
    simp
    intro h
