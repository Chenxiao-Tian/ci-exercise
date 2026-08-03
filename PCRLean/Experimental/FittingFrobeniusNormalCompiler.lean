import Mathlib.RingTheory.Localization.Away.Basic
import PCRLean.Experimental.FittingMinorAtlas
import PCRLean.Experimental.FrobeniusNormalBasicOpenDescent

/-!
# Compile a finite Fitting atlas into global Frobenius-normality

A finite Fitting atlas supplies elements `d_c` generating the unit ideal.  Its
canonical charts are the away localizations `A[d_c⁻¹]`.  If the extension of a
centre ideal is Frobenius-normal on every such chart, the finite basic-open
descent theorem patches these local reflection laws into a global one.

This removes the phrase "choose an invertible minor near each point" from the
proof interface.  The input is one finite atlas and one local certificate per
listed chart.  The still-open geometric task is to derive those local
certificates from the conormal/Fitting packet and to transport the whole packet,
not merely its centre filtration, through blowup and reentry.
-/

namespace PCRLean
namespace Experimental
namespace FittingFrobeniusNormalCompiler

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {Chart : Type v} [Fintype Chart]

open FittingMinorAtlas
open FrobeniusNormalBasicOpenDescent

/-- Centre ideal extended to one canonical determinant chart. -/
def awayIdeal
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (I : Ideal R) (c : Chart) :
    Ideal (Localization.Away (A.determinant c)) :=
  Ideal.map
    (algebraMap R (Localization.Away (A.determinant c))) I

/-- A finite family of local Frobenius-normality certificates. -/
structure LocalCertificates
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (p : Nat) (I : Ideal R) where
  reflects : ∀ c : Chart,
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p
      (awayIdeal A I c)

/-- Main Fitting-atlas patching theorem. -/
theorem reflectsFrobeniusPowers
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (p : Nat) (I : Ideal R)
    (L : LocalCertificates A p I) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  exact FrobeniusNormalBasicOpenDescent
    .reflectsFrobeniusPowers_of_basicOpenCover
      A.determinant
      (fun c => Localization.Away (A.determinant c))
      p I A.cover L.reflects

/-- Exact marked root reflection after global Fitting-atlas patching. -/
theorem power_mem_scaled_iff
    (A : FittingMinorAtlas.Atlas (R := R) (Chart := Chart))
    (p : Nat) (I : Ideal R)
    (L : LocalCertificates A p I)
    (e mark : Nat) (x : R) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔ x ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflectsFrobeniusPowers A p I L) e mark x

end

end FittingFrobeniusNormalCompiler
end Experimental
end PCRLean
