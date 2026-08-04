import Mathlib
import PCRLean.Experimental.FlatExceptionalTorsionKill

/-!
# Exceptional no-recharge

After the purified associated-graded portfolio is flat over a regular carrier,
every exceptional Cartier monomial acts regularly.  Consequently no later
Cartier trace, chart restriction, or boundary monomial can create a new
exceptional-power-torsion layer.

The geometric program must construct the monomial and prove that it is a base
nonzerodivisor on every relevant chart.  This file proves only the exact module
compiler from that certificate to vanishing of any alleged recharged torsion
submodule.
-/

namespace PCRLean
namespace Experimental
namespace ExceptionalNoRecharge

noncomputable section

open scoped nonZeroDivisors

universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A source-labelled exceptional monomial together with its regularity
certificate on the carrier. -/
structure MonomialCertificate where
  monomial : R
  regular : monomial ∈ R⁰

/-- Flatness forbids any exceptional-power-torsion recharge. -/
theorem noRecharge
    [Module.Flat R M]
    (c : MonomialCertificate (R := R))
    (E : Submodule R M)
    (hE : ∀ x, x ∈ E → ∃ n : ℕ, c.monomial ^ n • x = 0) :
    E = ⊥ :=
  FlatExceptionalTorsionKill.submodule_eq_bot_of_power_torsion
    c.regular E hE

/-- Once a prior torsion layer is zero, every successor layer satisfying the
same monomial-torsion specification is also zero. -/
theorem successor_eq_bot
    [Module.Flat R M]
    (c : MonomialCertificate (R := R))
    (oldLayer newLayer : Submodule R M)
    (_hOld : oldLayer = ⊥)
    (hNew : ∀ x, x ∈ newLayer →
      ∃ n : ℕ, c.monomial ^ n • x = 0) :
    newLayer = ⊥ :=
  noRecharge c newLayer hNew

/-- Simultaneous no-recharge for a finite owner portfolio. -/
theorem finitePortfolio
    {Owner : Type w} [Fintype Owner]
    (Piece : Owner → Type v)
    [∀ o, AddCommGroup (Piece o)]
    [∀ o, Module R (Piece o)]
    [∀ o, Module.Flat R (Piece o)]
    (c : MonomialCertificate (R := R))
    (E : ∀ o, Submodule R (Piece o))
    (hE : ∀ o x, x ∈ E o →
      ∃ n : ℕ, c.monomial ^ n • x = 0) :
    ∀ o, E o = ⊥ := by
  intro o
  exact noRecharge c (E o) (hE o)

end

end ExceptionalNoRecharge
end Experimental
end PCRLean
