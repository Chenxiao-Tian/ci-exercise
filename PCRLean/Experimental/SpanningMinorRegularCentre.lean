import Mathlib
import PCRLean.Experimental.BiorthogonalRegularCentre
import PCRLean.Experimental.IntrinsicCentreGaugeInvariance
import PCRLean.Experimental.FiniteFreeSymmetricAlgebraRegular

/-!
# Experimental regular centre from a spanning invertible minor

A constant-rank Fitting chart contains more information than one invertible
minor: the selected independent rows must span every row of the full packet.
This file packages exactly that certificate.

The selected rows have biorthogonal transverse vectors, so their evaluation map
is split surjective. Explicit row-reconstruction coefficients show that the
common kernel of the selected rows equals the common kernel of the entire
packet. Therefore the intrinsic actual centre ideal of the full packet is
literally the regular centre ideal supplied by the selected minor.

For a finite free ambient direction module over a nontrivial regular base ring,
this gives an actual proper finite-type regular centre for the full packet. The
remaining geometric problem is to produce these spanning-minor certificates on
a finite Fitting cover and prove their localization and blowup compatibility.
-/

namespace PCRLean
namespace Experimental
namespace SpanningMinorRegularCentre

noncomputable section

universe u v w x

variable {R : Type u} [CommRing R] [Nontrivial R] [IsRegularRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {Row : Type w}
variable {Pivot : Type x} [Fintype Pivot] [DecidableEq Pivot]

abbrev Dual := Module.Dual R V

/-- Evaluation by an arbitrary full packet of linear rows. -/
def fullEval (packet : Row → Dual (R := R) (V := V)) :
    V →ₗ[R] (Row → R) where
  toFun x row := packet row x
  map_add' := by
    intro x y
    funext row
    simp
  map_smul' := by
    intro a x
    funext row
    simp

/-- A selected invertible minor together with explicit reconstruction of every
row in the full packet. -/
structure CertificateData where
  packet : Row → Dual (R := R) (V := V)
  selected : Pivot → Row
  transverse : Pivot → V
  biorthogonal : ∀ i j : Pivot,
    packet (selected i) (transverse j) = if i = j then 1 else 0
  coefficient : Row → Pivot → R
  reconstruct : ∀ row x,
    packet row x =
      ∑ i : Pivot, coefficient row i * packet (selected i) x

namespace CertificateData

variable (C : CertificateData
  (R := R) (V := V) (Row := Row) (Pivot := Pivot))

/-- The selected minor as a biorthogonal packet. -/
def selectedFrame :
    BiorthogonalSplitFrame.Frame (K := R) (V := V) (ι := Pivot) where
  packet i := C.packet (C.selected i)
  transverse := C.transverse
  biorthogonal := C.biorthogonal

/-- Evaluation by the selected rows. -/
abbrev selectedEval : V →ₗ[R] (Pivot → R) :=
  C.selectedFrame.eval

/-- The full packet and the selected spanning minor have the same common
kernel. -/
theorem ker_fullEval_eq_selectedEval :
    LinearMap.ker (fullEval C.packet) =
      LinearMap.ker C.selectedEval := by
  ext x
  constructor
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext i
    have hzero : fullEval C.packet x = 0 := LinearMap.mem_ker.mp hx
    have hi := congrFun hzero (C.selected i)
    simpa [fullEval, selectedEval, selectedFrame,
      BiorthogonalSplitFrame.Frame.eval] using hi
  · intro hx
    apply LinearMap.mem_ker.mpr
    funext row
    have hzero : C.selectedEval x = 0 := LinearMap.mem_ker.mp hx
    have hselected : ∀ i : Pivot,
        C.packet (C.selected i) x = 0 := by
      intro i
      have hi := congrFun hzero i
      simpa [selectedEval, selectedFrame,
        BiorthogonalSplitFrame.Frame.eval] using hi
    rw [C.reconstruct row x]
    simp [hselected]

/-- Intrinsic actual centre ideal of the entire packet. -/
def centreIdeal : Ideal (SymmetricAlgebra R V) :=
  SurjectiveLinearMapSymmetricQuotient.kernelIdeal (fullEval C.packet)

/-- The full-packet centre is exactly the selected-minor centre. -/
theorem centreIdeal_eq_selectedCentre :
    C.centreIdeal =
      BiorthogonalRegularCentre.centreIdeal C.selectedFrame := by
  exact IntrinsicCentreGaugeInvariance.kernelIdeal_eq_of_ker_eq
    (fullEval C.packet) C.selectedEval
    C.ker_fullEval_eq_selectedEval

/-- Exact quotient of the full packet centre by the finite coefficient
symmetric algebra. -/
noncomputable def quotientEquiv :
    (SymmetricAlgebra R V ⧸ C.centreIdeal) ≃+*
      SymmetricAlgebra R (Pivot → R) :=
  (Ideal.quotEquivOfEq C.centreIdeal_eq_selectedCentre).trans
    (BiorthogonalRegularCentre.quotientEquiv C.selectedFrame)

/-- The full-packet centre is proper. -/
theorem centreIdeal_ne_top : C.centreIdeal ≠ ⊤ := by
  rw [C.centreIdeal_eq_selectedCentre]
  exact BiorthogonalRegularCentre.centreIdeal_ne_top C.selectedFrame

/-- The full-packet centre is finite type whenever the ambient symmetric
algebra is Noetherian. -/
theorem centreIdeal_fg
    [IsNoetherianRing (SymmetricAlgebra R V)] :
    C.centreIdeal.FG :=
  IsNoetherian.noetherian _

/-- Its quotient is regular. -/
theorem quotient_isRegularRing :
    IsRegularRing (SymmetricAlgebra R V ⧸ C.centreIdeal) := by
  exact IsRegularRing.of_ringEquiv C.quotientEquiv.symm

/-- Full-packet actual regular-centre certificate. -/
structure RegularCertificate where
  ideal : Ideal (SymmetricAlgebra R V)
  ideal_eq : ideal = C.centreIdeal
  proper : ideal ≠ ⊤
  finiteType : ideal.FG
  quotient :
    (SymmetricAlgebra R V ⧸ ideal) ≃+*
      SymmetricAlgebra R (Pivot → R)
  quotientRegular : IsRegularRing (SymmetricAlgebra R V ⧸ ideal)

/-- Assemble the full-packet certificate once the ambient symmetric algebra is
Noetherian. -/
noncomputable def regularCertificate
    [IsNoetherianRing (SymmetricAlgebra R V)] :
    C.RegularCertificate where
  ideal := C.centreIdeal
  ideal_eq := rfl
  proper := C.centreIdeal_ne_top
  finiteType := C.centreIdeal_fg
  quotient := C.quotientEquiv
  quotientRegular := C.quotient_isRegularRing

/-- Finite freeness of the ambient module makes Noetherianity automatic. -/
noncomputable def finiteFreeRegularCertificate
    [Module.Free R V] [Module.Finite R V] :
    C.RegularCertificate := by
  letI : IsNoetherianRing (SymmetricAlgebra R V) :=
    FiniteFreeSymmetricAlgebraRegular.isNoetherianRing
      (K := R) (M := V)
  exact C.regularCertificate

end CertificateData

end

end SpanningMinorRegularCentre
end Experimental
end PCRLean
