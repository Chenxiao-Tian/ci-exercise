import Mathlib
import PCRLean.Experimental.OrderIdealMarkedClosureCompiler

/-!
# The space of cardinal-minimal marked closures

X031 proves existence of a cardinal-minimal acceptable correction subfamily.
Existence alone does not make the selected subfamily canonical.  This file
makes the entire minimizer space a first-class object, proves essentiality of
every chosen component, isolates the unique-minimizer chamber, and proves an
abstract symmetry no-go theorem for a two-point orbit of minimizers.

The missing next edge is deliberately explicit: in the nonunique chamber the
finite minimizer space must be serialized as an ordinary centre word with
proved legality, critical-pair compatibility, and strict macro descent.
-/

namespace PCRLean
namespace Experimental
namespace CanonicalMarkedMinimizerSpace

noncomputable section

universe u v w

/-- Cardinal-minimal solutions of an arbitrary finite acceptance predicate. -/
def IsMinimizer {α : Type u} [Fintype α]
    (Acceptable : Finset α → Prop) (selected : Finset α) : Prop :=
  Acceptable selected ∧
    ∀ other : Finset α, Acceptable other → selected.card ≤ other.card

/-- The whole minimizer space, rather than one arbitrary chosen point. -/
def minimizerSpace {α : Type u} [Fintype α]
    (Acceptable : Finset α → Prop) : Set (Finset α) :=
  {selected | IsMinimizer Acceptable selected}

/-- Every element of a cardinal-minimal acceptable family is essential. -/
theorem erase_not_acceptable
    {α : Type u} [Fintype α] [DecidableEq α]
    {Acceptable : Finset α → Prop} {selected : Finset α}
    (hmin : IsMinimizer Acceptable selected)
    {a : α} (ha : a ∈ selected) :
    ¬ Acceptable (selected.erase a) := by
  intro herase
  have hle := hmin.2 (selected.erase a) herase
  have hlt : (selected.erase a).card < selected.card :=
    Finset.card_erase_lt_of_mem ha
  exact (Nat.not_lt_of_ge hle) hlt

/-- Uniqueness of the minimizer space. -/
def HasUniqueMinimizer {α : Type u} [Fintype α]
    (Acceptable : Finset α → Prop) : Prop :=
  ∃! selected : Finset α, IsMinimizer Acceptable selected

/-- General involutive-symmetry obstruction: if all minimizers are two distinct
points exchanged by a symmetry, there is no symmetry-fixed minimizer. -/
theorem no_fixed_minimizer_of_two_point_swap
    {α : Type u} [Fintype α] [DecidableEq α]
    {Acceptable : Finset α → Prop}
    {U V : Finset α}
    (hUV : U ≠ V)
    (σ : α ≃ α)
    (hσU : U.map σ.toEmbedding = V)
    (hσV : V.map σ.toEmbedding = U)
    (honly : ∀ W, IsMinimizer Acceptable W → W = U ∨ W = V) :
    ¬ ∃ W, IsMinimizer Acceptable W ∧ W.map σ.toEmbedding = W := by
  rintro ⟨W, hW, hfixed⟩
  rcases honly W hW with rfl | rfl
  · apply hUV
    calc
      U = U.map σ.toEmbedding := hfixed.symm
      _ = V := hσU
  · apply hUV
    calc
      U = V.map σ.toEmbedding := hσV.symm
      _ = V := hfixed

section MarkedIdeals

open OrderIdealMarkedClosureCompiler

variable {R : Type u} [CommRing R]
variable {Component : Type v} [Fintype Component] [DecidableEq Component]
variable {Owner : Type w} [Fintype Owner]

/-- The ideal-valued minimizer predicate for the X031 marked-closure compiler. -/
def MarkedMinimizer
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    (selected : Finset Component) : Prop :=
  IsMinimizer (OrderIdealMarkedClosureCompiler.Acceptable J component Q)
    selected

/-- Existence of at least one marked minimizer under full-family
acceptability. -/
theorem exists_markedMinimizer
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    (hfull : OrderIdealMarkedClosureCompiler.Acceptable
      J component Q Finset.univ) :
    ∃ selected, MarkedMinimizer J component Q selected := by
  rcases OrderIdealMarkedClosureCompiler.exists_cardinalMinimal
      J component Q hfull with
    ⟨selected, hacceptable, hminimal⟩
  exact ⟨selected, hacceptable, hminimal⟩

/-- A first-class uniqueness certificate.  Unlike an arbitrary use of choice,
this object records the exact theorem making a single closure canonical. -/
structure UniqueMarkedClosureCertificate
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner)) where
  selected : Finset Component
  isMinimizer : MarkedMinimizer J component Q selected
  unique : ∀ other : Finset Component,
    MarkedMinimizer J component Q other → other = selected

/-- Construct the first-class certificate from an existence-and-uniqueness
proof. -/
noncomputable def UniqueMarkedClosureCertificate.ofExistsUnique
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    (hunique : ∃! selected : Finset Component,
      MarkedMinimizer J component Q selected) :
    UniqueMarkedClosureCertificate J component Q where
  selected := Classical.choose hunique.exists
  isMinimizer := Classical.choose_spec hunique.exists
  unique other hother :=
    hunique.unique hother (Classical.choose_spec hunique.exists)

namespace UniqueMarkedClosureCertificate

variable {J : Ideal R} {component : Component → Ideal R}
variable {Q : Requirements (R := R) (Owner := Owner)}
variable (C : UniqueMarkedClosureCertificate J component Q)

/-- Canonical marked closure ideal. -/
def ideal : Ideal R :=
  OrderIdealMarkedClosureCompiler.closure J component C.selected

/-- The canonical selected family is acceptable. -/
theorem acceptable :
    OrderIdealMarkedClosureCompiler.Acceptable
      J component Q C.selected :=
  C.isMinimizer.1

/-- The canonical ideal satisfies every marked owner. -/
theorem owner_le_power (o : Owner) :
    Q.ownerIdeal o ≤ C.ideal ^ Q.mark o :=
  C.acceptable o

/-- Every selected correction component is essential. -/
theorem selected_essential
    {a : Component} (ha : a ∈ C.selected) :
    ¬ OrderIdealMarkedClosureCompiler.Acceptable
      J component Q (C.selected.erase a) :=
  erase_not_acceptable C.isMinimizer ha

/-- Every other minimizer is the same selected family. -/
theorem other_eq_selected
    {other : Finset Component}
    (hother : MarkedMinimizer J component Q other) :
    other = C.selected :=
  C.unique other hother

end UniqueMarkedClosureCertificate
end MarkedIdeals

end

end CanonicalMarkedMinimizerSpace
end Experimental
end PCRLean
