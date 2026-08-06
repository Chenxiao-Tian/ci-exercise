import Mathlib
import PCRLean.HasseSaturationDescent
import PCRLean.CoordinateFrobeniusRootCentre

/-!
# A certified local Frobenius centre step

This file combines three independently auditable layers:

1. canonical finite Hasse saturation of a seed ideal;
2. exact descent of that saturation to its Frobenius core;
3. realization of the core's root ideal as a coordinate-kernel ideal.

Under the explicit coordinate-realization hypothesis, both the original seed
and its Hasse saturation are permissible for one proper actual centre, and the
quotient by that centre is a smaller polynomial ring.  This is a complete local
centre certificate for the split Frobenius chamber.  The unresolved geometric
task is to construct these coordinate realizations intrinsically and glue them
on overlaps for arbitrary prepared inputs.
-/

namespace PCRLean
namespace LocalFrobeniusCentreStep

noncomputable section

universe u v w x

variable {R : Type u} {K : Type v}
variable [CommRing R] [CommRing K] [Nontrivial K]
variable {σ : Type w} {τ : Type x}

abbrev A := MvPolynomial τ K

variable [Algebra R (A (K := K) (τ := τ))]

/-- The original seed is controlled by the descended Frobenius core of its
canonical Hasse saturation. -/
theorem seed_le_coreExtension
    {q : Nat} {t : R}
    (F : MonogenicFrobeniusFrame.Frame
      (R := R) (A := A (K := K) (τ := τ)) q t)
    (I : Ideal (A (K := K) (τ := τ))) :
    I ≤ (HasseSaturationDescent.frobeniusCore F I).map
      (algebraMap R (A (K := K) (τ := τ))) := by
  calc
    I ≤ HasseSaturationDescent.hasseSaturation F I :=
      HasseSaturationDescent.le_hasseSaturation F I
    _ = (HasseSaturationDescent.frobeniusCore F I).map
        (algebraMap R (A (K := K) (τ := τ))) :=
      HasseSaturationDescent.hasseSaturation_eq_map_core F I

/-- The Hasse saturation itself is permissible for the actual root ideal of
its descended core. -/
theorem saturation_permissible_for_rootIdeal
    {q : Nat} {t : R} (hq : 0 < q)
    (F : MonogenicFrobeniusFrame.Frame
      (R := R) (A := A (K := K) (τ := τ)) q t)
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := A (K := K) (τ := τ)) q)
    (I : Ideal (A (K := K) (τ := τ))) :
    MarkedIdeal.Permissible
      (R := A (K := K) (τ := τ))
      ⟨HasseSaturationDescent.hasseSaturation F I, q, hq⟩
      (S.rootIdeal (HasseSaturationDescent.frobeniusCore F I)) := by
  apply S.markedPacket_permissible hq
  exact le_of_eq
    (HasseSaturationDescent.hasseSaturation_eq_map_core F I)

/-- The original seed is also permissible for the same root ideal. -/
theorem seed_permissible_for_rootIdeal
    {q : Nat} {t : R} (hq : 0 < q)
    (F : MonogenicFrobeniusFrame.Frame
      (R := R) (A := A (K := K) (τ := τ)) q t)
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := A (K := K) (τ := τ)) q)
    (I : Ideal (A (K := K) (τ := τ))) :
    MarkedIdeal.Permissible
      (R := A (K := K) (τ := τ)) ⟨I, q, hq⟩
      (S.rootIdeal (HasseSaturationDescent.frobeniusCore F I)) := by
  exact S.markedPacket_permissible hq (seed_le_coreExtension F I)

/-- Complete local affine centre certificate in the coordinate Frobenius
chamber. -/
theorem coordinateCentre_certificate
    {q : Nat} {t : R} (hq : 0 < q)
    (F : MonogenicFrobeniusFrame.Frame
      (R := R) (A := A (K := K) (τ := τ)) q t)
    (S : FrobeniusRootCentre.RootSection
      (R := R) (A := A (K := K) (τ := τ)) q)
    (I : Ideal (A (K := K) (τ := τ)))
    (f : σ → τ) (hf : Function.Injective f)
    (hcoord :
      S.rootIdeal (HasseSaturationDescent.frobeniusCore F I) =
        CoordinateKernelIdeal.ideal (R := K) f hf) :
    ∃ C : Ideal (A (K := K) (τ := τ)),
      C ≠ ⊤ ∧
      MarkedIdeal.Permissible
        (R := A (K := K) (τ := τ)) ⟨I, q, hq⟩ C ∧
      MarkedIdeal.Permissible
        (R := A (K := K) (τ := τ))
        ⟨HasseSaturationDescent.hasseSaturation F I, q, hq⟩ C ∧
      Nonempty
        ((A (K := K) (τ := τ) ⧸ C) ≃+* MvPolynomial σ K) := by
  refine ⟨S.rootIdeal (HasseSaturationDescent.frobeniusCore F I),
    CoordinateFrobeniusRootCentre.rootIdeal_ne_top
      S (HasseSaturationDescent.frobeniusCore F I) f hf hcoord,
    seed_permissible_for_rootIdeal hq F S I,
    saturation_permissible_for_rootIdeal hq F S I,
    CoordinateFrobeniusRootCentre.quotient_is_smaller_polynomial_ring
      S (HasseSaturationDescent.frobeniusCore F I) f hf hcoord⟩

end

end LocalFrobeniusCentreStep
end PCRLean
