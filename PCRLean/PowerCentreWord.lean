import Mathlib
import PCRLean.PowerTransformFunctoriality

/-!
# Power lift of a finite controlled centre word

A finite controlled-transform word is represented as a chain of chart
endomorphisms in one ambient algebra.  Each step removes an exceptional factor
of mark `b`.  Power functoriality lifts the whole word, step by step, to the
`q`-th-power packet with mark `b*q`.

Scheme-level blowup words vary their coordinate rings from stage to stage; the
present fixed-ring chain is the algebraic recursion kernel.  A dependent
scheme-level implementation can reuse the same induction once the blowup chart
API is available.
-/

namespace PCRLean
namespace PowerCentreWord

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Finite chain of controlled transform steps at one common mark. -/
inductive Word (b : Nat) : R → R → Type u
  | nil (f : R) : Word b f f
  | cons {f g h : R}
      (φ : R →+* R) (E : R)
      (factor : φ f = E ^ b * g)
      (tail : Word b g h) : Word b f h

namespace Word

variable {b : Nat} {f h : R}

/-- Number of controlled steps. -/
def length : Word b f h → Nat
  | nil _ => 0
  | cons _ _ _ tail => tail.length + 1

/-- Concatenate two controlled words. -/
def append {f g h : R} :
    Word b f g → Word b g h → Word b f h
  | nil _, second => second
  | cons φ E factor tail, second =>
      cons φ E factor (tail.append second)

@[simp] theorem length_append {f g h : R}
    (first : Word b f g) (second : Word b g h) :
    (first.append second).length = first.length + second.length := by
  induction first with
  | nil f => simp [append, length]
  | cons φ E factor tail ih =>
      simp [append, length, ih, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Lift an entire controlled word to `q`-th powers. -/
def pow (q : Nat) : Word b f h → Word (b * q) (f ^ q) (h ^ q)
  | nil f => nil (f ^ q)
  | cons φ E factor tail =>
      cons φ E
        (PowerTransformFunctoriality.pow_factorization_target
          φ E factor)
        (tail.pow q)

@[simp] theorem length_pow (word : Word b f h) (q : Nat) :
    (word.pow q).length = word.length := by
  induction word with
  | nil f => rfl
  | cons φ E factor tail ih =>
      simp [pow, length, ih]

/-- Power lift commutes with concatenation. -/
theorem pow_append {f g h : R}
    (first : Word b f g) (second : Word b g h) (q : Nat) :
    (first.append second).pow q =
      (first.pow q).append (second.pow q) := by
  induction first with
  | nil f => rfl
  | cons φ E factor tail ih =>
      simp [append, pow, ih]

/-- Iterated power lifts multiply their scaling factors. -/
theorem pow_pow (word : Word b f h) (q r : Nat) :
    (word.pow q).pow r = word.pow (q * r) := by
  induction word with
  | nil f => simp [pow, pow_mul]
  | cons φ E factor tail ih =>
      simp [pow, ih, mul_assoc, pow_mul]

/-- Existence form: every lower-mark controlled word yields a word of exactly
the same length for the powered packet. -/
theorem exists_power_word (word : Word b f h) (q : Nat) :
    ∃ powered : Word (b * q) (f ^ q) (h ^ q),
      powered.length = word.length :=
  ⟨word.pow q, word.length_pow q⟩

end Word

end

end PowerCentreWord
end PCRLean
