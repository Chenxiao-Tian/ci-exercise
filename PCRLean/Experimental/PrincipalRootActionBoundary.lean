import Mathlib
import Mathlib.RingTheory.Ideal.IsPrincipal
import PCRLean.MarkedIdeal

/-!
# Experimental principal-root action boundary

A pure marked power `r^m` is automatically permissible for the root ideal
`(r)`.  That root ideal is principal.  Geometrically, if `(r)` defines an
effective Cartier divisor, blowing it up is an isomorphism; hence this algebraic
certificate belongs to a terminal/boundary-enrollment branch, not automatically
to a nonidentity blowup branch.

This file proves the algebraic half only: marked permissibility, properness
under a nonunit hypothesis, and principality.  The scheme-level statement that
the blowup of an effective Cartier divisor is the identity remains a separate
geometric bridge.
-/

namespace PCRLean
namespace Experimental
namespace PrincipalRootActionBoundary

noncomputable section

universe u

variable {R : Type u} [CommRing R]

/-- Actual principal root ideal. -/
def rootIdeal (r : R) : Ideal R :=
  Ideal.span {r}

/-- Every root ideal is principal. -/
theorem rootIdeal_isPrincipal (r : R) :
    Submodule.IsPrincipal (rootIdeal r) := by
  unfold rootIdeal
  infer_instance

/-- A pure marked power lies in the corresponding power of its root ideal. -/
theorem pow_mem_rootIdeal_pow (r : R) (m : Nat) :
    r ^ m ∈ (rootIdeal r) ^ m := by
  exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self r) m

/-- The pure-power marked packet is permissible for the root ideal. -/
theorem purePower_permissible
    (r : R) (m : Nat) (hm : 0 < m) :
    MarkedIdeal.Permissible
      (R := R) ⟨Ideal.span {r ^ m}, m, hm⟩ (rootIdeal r) := by
  exact MarkedIdeal.permissible_span_singleton hm
    (pow_mem_rootIdeal_pow r m)

/-- A nonunit root ideal is proper. -/
theorem rootIdeal_ne_top_of_not_isUnit
    (r : R) (hr : ¬ IsUnit r) :
    rootIdeal r ≠ ⊤ := by
  intro htop
  have hone : (1 : R) ∈ rootIdeal r := by
    rw [htop]
    trivial
  rw [rootIdeal, Ideal.mem_span_singleton] at hone
  exact hr (isUnit_iff_dvd_one.mpr hone)

/-- A nonzero root has a non-bottom principal ideal in a domain. -/
theorem rootIdeal_ne_bot_of_ne_zero
    [IsDomain R] (r : R) (hr : r ≠ 0) :
    rootIdeal r ≠ ⊥ := by
  intro hbot
  have hrmem : r ∈ rootIdeal r := Ideal.mem_span_singleton_self r
  rw [hbot] at hrmem
  exact hr (by simpa using hrmem)

/-- Algebraic certificate exposing why a pure root needs an additional
nonidentity/Cartier gate before it can be used as a blowup action. -/
structure PureRootCertificate (r : R) (m : Nat) (hm : 0 < m) where
  permissible : MarkedIdeal.Permissible
    (R := R) ⟨Ideal.span {r ^ m}, m, hm⟩ (rootIdeal r)
  principal : Submodule.IsPrincipal (rootIdeal r)

/-- Assemble the pure-root certificate. -/
noncomputable def pureRootCertificate
    (r : R) (m : Nat) (hm : 0 < m) :
    PureRootCertificate r m hm where
  permissible := purePower_permissible r m hm
  principal := rootIdeal_isPrincipal r

end

end PrincipalRootActionBoundary
end Experimental
end PCRLean
