import PCRLean.Experimental.FittingCentreLegalityCompiler
import PCRLean.Experimental.FlatPassiveTorSafety

/-!
# Joint active/passive legality for flat passive owners

Combine the finite Fitting-atlas compiler with the flat passive-module Tor gate.
The resulting certificate contains, for one actual centre ideal:

* global Frobenius-normality;
* marked permissibility for every active owner; and
* first-Tor safety for every flat passive owner.

This is a genuine restricted joint-legality theorem: active and passive data are
certified simultaneously for the same centre.  It does not cover nonflat
passive modules, normal-flat associated graded data, boundary SNC, regularity of
the centre, or hereditary transforms.
-/

namespace PCRLean
namespace Experimental
namespace FittingFlatJointLegalityCompiler

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R]
variable {Chart : Type v} [Fintype Chart]
variable {Active : Type w}
variable {Passive : Type x}

/-- Joint output for active and flat passive owners. -/
structure Certificate
    (p : Nat) (centre : Ideal R)
    (active : Active → MarkedIdeal.Packet R)
    (passive : Passive → Type u)
    [∀ o, AddCommGroup (passive o)]
    [∀ o, Module R (passive o)] where
  frobeniusNormal :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p centre
  activePermissible : ∀ o : Active,
    MarkedIdeal.Permissible (active o) centre
  passiveTorSafe : ∀ o : Passive,
    FlatPassiveTorSafety.TorSafe centre (passive o)

/-- Compile a finite Fitting atlas together with a flat passive family. -/
noncomputable def compile
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (p : Nat) (centre : Ideal R)
    (active : Active → MarkedIdeal.Packet R)
    (L : FittingCentreLegalityCompiler.LocalCertificates
      A p centre active)
    (passive : Passive → Type u)
    [∀ o, AddCommGroup (passive o)]
    [∀ o, Module R (passive o)]
    [∀ o, Module.Flat R (passive o)] :
    Certificate p centre active passive where
  frobeniusNormal :=
    (FittingCentreLegalityCompiler.compile
      A p centre active L).frobeniusNormal
  activePermissible :=
    (FittingCentreLegalityCompiler.compile
      A p centre active L).ownerPermissible
  passiveTorSafe :=
    FlatPassiveTorSafety.owners_torSafe_of_flat passive centre

end

end FittingFlatJointLegalityCompiler
end Experimental
end PCRLean
