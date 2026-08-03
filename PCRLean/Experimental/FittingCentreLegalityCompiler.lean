import Mathlib.RingTheory.Localization.Away.Basic
import PCRLean.Experimental.FittingFrobeniusNormalCompiler
import PCRLean.Experimental.MarkedPermissibilityBasicOpenDescent

/-!
# Fitting-atlas compiler for active legality and Frobenius heredity

A finite determinant atlas can now be used as one typed local-to-global
certificate.  On each canonical away chart one supplies:

* Frobenius-normality of the extended centre; and
* marked-power containment for every active owner.

The compiler returns the corresponding global statements on the original
ring.  It uses no preferred chart and no hidden choice of an invertible minor.

The output deliberately omits passive Tor safety, normal flatness, boundary
SNC, actual regularity of the centre, controlled transforms and hereditary
packet reconstruction.  Those gates must be proved independently before this
certificate can feed the global resolution compiler.
-/

namespace PCRLean
namespace Experimental
namespace FittingCentreLegalityCompiler

noncomputable section

universe u v w

variable {R : Type u} [CommRing R]
variable {Chart : Type v} [Fintype Chart]
variable {Owner : Type w}

open FittingMinorAtlas
open FittingFrobeniusNormalCompiler
open FrobeniusNormalBasicOpenDescent

/-- Complete local active/Frobenius data on the determinant atlas. -/
structure LocalCertificates
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (p : Nat) (centre : Ideal R)
    (owners : Owner → MarkedIdeal.Packet R) where
  frobenius : ∀ c : Chart,
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p
      (awayIdeal A centre c)
  active : ∀ c : Chart, ∀ o : Owner,
    awayIdeal A (owners o).ideal c ≤
      (awayIdeal A centre c) ^ (owners o).mark

/-- Global output of the finite atlas compiler. -/
structure Certificate
    (p : Nat) (centre : Ideal R)
    (owners : Owner → MarkedIdeal.Packet R) where
  frobeniusNormal :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p centre
  ownerPermissible : ∀ o : Owner,
    MarkedIdeal.Permissible (owners o) centre

/-- Compile all local certificates to the original ring. -/
noncomputable def compile
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (p : Nat) (centre : Ideal R)
    (owners : Owner → MarkedIdeal.Packet R)
    (L : LocalCertificates A p centre owners) :
    Certificate p centre owners where
  frobeniusNormal :=
    FittingFrobeniusNormalCompiler.reflectsFrobeniusPowers
      A p centre ⟨L.frobenius⟩
  ownerPermissible := by
    intro o
    exact MarkedPermissibilityBasicOpenDescent
      .permissible_of_basicOpenCover
        A.determinant
        (fun c => Localization.Away (A.determinant c))
        (owners o) centre A.cover
        (fun c => L.active c o)

/-- Exact marked root reflection supplied by the compiled centre. -/
theorem power_mem_scaled_iff
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (p : Nat) (centre : Ideal R)
    (owners : Owner → MarkedIdeal.Packet R)
    (L : LocalCertificates A p centre owners)
    (e mark : Nat) (x : R) :
    x ^ (p ^ e) ∈ centre ^ ((p ^ e) * mark) ↔
      x ∈ centre ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p centre
    (compile A p centre owners L).frobeniusNormal
    e mark x

end

end FittingCentreLegalityCompiler
end Experimental
end PCRLean
