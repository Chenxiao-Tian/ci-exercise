import Mathlib
import Mathlib.RingTheory.Localization.Away.Basic
import PCRLean.Experimental.DeterminantMinorRegularCentre

/-!
# Experimental regular centre on a principal Fitting chart

Let `A` be a square evaluation minor over a ring `R`, and let `S` be a
localization of `R` away from `det A`.  The determinant of the coefficientwise
image of `A` in `S` is a unit: localization makes `det A` invertible and
`RingHom.map_det` identifies its image with the determinant of the mapped
matrix.

Therefore any packet and test-vector family over `S` whose evaluation matrix is
the mapped minor automatically enters the unit-determinant centre theorem.  If
`S` is a nontrivial regular ring and the ambient direction module is finite
free, this yields an intrinsic actual proper finite-type regular centre on the
principal Fitting chart.

This is the first explicit localization bridge in U2.  It assumes the
localized packet/test-vector realization and regularity of the localization;
finite covering, scalar-extension construction, overlap descent, owner legality
and hereditary blowup transport remain separate obligations.
-/

namespace PCRLean
namespace Experimental
namespace FittingAwayRegularCentre

noncomputable section

universe u u' v w

variable {R : Type u} [CommRing R]
variable {S : Type u'} [CommRing S] [Algebra R S]
variable {V : Type v} [AddCommGroup V] [Module S V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

abbrev Dual := Module.Dual S V

/-- The determinant of a minor becomes a unit on its principal open. -/
theorem mapped_det_isUnit
    (A : Matrix ι ι R)
    [IsLocalization.Away A.det S] :
    IsUnit (((algebraMap R S).mapMatrix A).det) := by
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit A.det

/-- A localized packet realizing the mapped evaluation minor has unit
 determinant. -/
theorem evaluation_det_isUnit
    (A : Matrix ι ι R)
    [IsLocalization.Away A.det S]
    (packet : ι → Dual (S := S) (V := V))
    (testVector : ι → V)
    (hmatrix :
      DeterminantMinorRegularCentre.evaluationMatrix packet testVector =
        (algebraMap R S).mapMatrix A) :
    IsUnit
      (DeterminantMinorRegularCentre.evaluationMatrix
        packet testVector).det := by
  rw [hmatrix]
  exact mapped_det_isUnit (S := S) A

/-- Principal Fitting chart certificate: mapped minor plus finite freeness gives
an actual regular centre. -/
noncomputable def finiteFreeCertificate
    [Nontrivial S] [IsRegularRing S]
    [Module.Free S V] [Module.Finite S V]
    (A : Matrix ι ι R)
    [IsLocalization.Away A.det S]
    (packet : ι → Dual (S := S) (V := V))
    (testVector : ι → V)
    (hmatrix :
      DeterminantMinorRegularCentre.evaluationMatrix packet testVector =
        (algebraMap R S).mapMatrix A) :
    SurjectiveFreeRegularCentre.Certificate
      (DeterminantMinorRegularCentre.toMinorCertificate
        packet testVector
        (evaluation_det_isUnit A packet testVector hmatrix)).toBiorthogonalFrame.eval :=
  DeterminantMinorRegularCentre.finiteFreeCertificate
    packet testVector
    (evaluation_det_isUnit A packet testVector hmatrix)

end

end FittingAwayRegularCentre
end Experimental
end PCRLean
