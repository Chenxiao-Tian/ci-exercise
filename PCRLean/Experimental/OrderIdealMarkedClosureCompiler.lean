import Mathlib

/-!
# Finite marked closure compiler around an order ideal

The raw cokernel order ideal is a mark-one defect component.  General active
owners may require a larger ideal satisfying several marked-power containments.
This file separates candidate generation from finite selection.

Input:

* one intrinsic base defect ideal `J`;
* a finite family of actual candidate correction ideals `C_a`;
* a finite family of owner ideals `D_o` with positive marks `m_o`; and
* a proof that the closure using all candidate components satisfies every
  `D_o ≤ K^(m_o)`.

Output:

* a finite selected family of components;
* an actual closure `K = J ⊔ ⋁ C_a` satisfying every owner; and
* cardinal minimality, hence every selected component is essential.

The compiler does not construct the candidate components and does not infer
regularity, properness, passive safety or SNC.  These remain independent gates.
-/

namespace PCRLean
namespace Experimental
namespace OrderIdealMarkedClosureCompiler

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {Component : Type v} [Fintype Component] [DecidableEq Component]
variable {Owner : Type w} [Fintype Owner]

/-- Join of the intrinsic order ideal with a selected finite correction family. -/
def closure
    (J : Ideal R) (component : Component → Ideal R)
    (selected : Finset Component) : Ideal R :=
  J ⊔ selected.sup component

/-- Finite marked requirements. -/
structure Requirements where
  ownerIdeal : Owner → Ideal R
  mark : Owner → Nat
  mark_pos : ∀ o, 0 < mark o

/-- All owners are permissible for one selected closure. -/
def Acceptable
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    (selected : Finset Component) : Prop :=
  ∀ o : Owner,
    Q.ownerIdeal o ≤ (closure J component selected) ^ (Q.mark o)

/-- The intrinsic base defect is always contained in every closure. -/
theorem base_le_closure
    (J : Ideal R) (component : Component → Ideal R)
    (selected : Finset Component) :
    J ≤ closure J component selected :=
  le_sup_left

/-- Every selected component is contained in the closure. -/
theorem component_le_closure
    (J : Ideal R) (component : Component → Ideal R)
    (selected : Finset Component)
    {a : Component} (ha : a ∈ selected) :
    component a ≤ closure J component selected := by
  exact le_sup_of_le_right (Finset.le_sup ha)

/-- Existence of a cardinal-minimal acceptable selected family. -/
theorem exists_cardinalMinimal
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    (hfull : Acceptable J component Q Finset.univ) :
    ∃ selected : Finset Component,
      Acceptable J component Q selected ∧
        ∀ other : Finset Component,
          Acceptable J component Q other →
            selected.card ≤ other.card := by
  classical
  let P : Nat → Prop := fun n =>
    ∃ selected : Finset Component,
      Acceptable J component Q selected ∧ selected.card = n
  have hex : ∃ n, P n := by
    exact ⟨Finset.univ.card, Finset.univ, hfull, rfl⟩
  let n := Nat.find hex
  rcases Nat.find_spec hex with ⟨selected, hselected, hcard⟩
  refine ⟨selected, hselected, ?_⟩
  intro other hother
  have hmin : n ≤ other.card := by
    apply Nat.find_min'
    exact ⟨other, hother, rfl⟩
  simpa [n, hcard] using hmin

/-- Typed output of the finite marked closure compiler. -/
structure Certificate
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner)) where
  selected : Finset Component
  acceptable : Acceptable J component Q selected
  cardinalMinimal : ∀ other : Finset Component,
    Acceptable J component Q other → selected.card ≤ other.card

/-- Compile the minimal selected closure. -/
noncomputable def certificate
    (J : Ideal R) (component : Component → Ideal R)
    (Q : Requirements (R := R) (Owner := Owner))
    (hfull : Acceptable J component Q Finset.univ) :
    Certificate J component Q := by
  classical
  rcases exists_cardinalMinimal J component Q hfull with
    ⟨selected, hselected, hminimal⟩
  exact ⟨selected, hselected, hminimal⟩

namespace Certificate

variable {J : Ideal R} {component : Component → Ideal R}
variable {Q : Requirements (R := R) (Owner := Owner)}
variable (C : Certificate J component Q)

/-- Actual marked closure selected by the compiler. -/
def ideal : Ideal R := closure J component C.selected

/-- Every owner marked ideal is contained in the required power. -/
theorem owner_le_power (o : Owner) :
    Q.ownerIdeal o ≤ C.ideal ^ (Q.mark o) :=
  C.acceptable o

/-- The raw order ideal is retained. -/
theorem base_le : J ≤ C.ideal :=
  base_le_closure J component C.selected

/-- Every selected component is retained. -/
theorem selected_component_le
    {a : Component} (ha : a ∈ C.selected) :
    component a ≤ C.ideal :=
  component_le_closure J component C.selected ha

/-- Every selected component is essential: deleting it destroys at least one
marked requirement. -/
theorem erase_not_acceptable
    {a : Component} (ha : a ∈ C.selected) :
    ¬ Acceptable J component Q (C.selected.erase a) := by
  intro herase
  have hle := C.cardinalMinimal (C.selected.erase a) herase
  have hlt : (C.selected.erase a).card < C.selected.card :=
    Finset.card_erase_lt_of_mem ha
  exact (Nat.not_lt_of_ge hle) hlt

/-- Over a Noetherian base the selected marked closure is finite type. -/
theorem ideal_fg [IsNoetherianRing R] : C.ideal.FG :=
  IsNoetherian.noetherian _

end Certificate

end

end OrderIdealMarkedClosureCompiler
end Experimental
end PCRLean
