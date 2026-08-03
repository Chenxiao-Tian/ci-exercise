import Mathlib
import PCRLean.Experimental.SplitMatrixOrderIdealHybrid
import PCRLean.Experimental.OrderIdealMarkedClosureCompiler

/-!
# Split matrix packet with a minimal marked hybrid closure

The split packet supplies a graph candidate `h` and its intrinsic raw defect
ideal `J = O(ρ)`.  A finite family of root/owner/boundary correction ideals is
then fed to the cardinal-minimal marked-closure compiler.

The output is one actual coefficient closure `K` and one actual polynomial
centre

`C = (Z_i-h_i) + K R[Z]`

such that:

* `J ≤ K`, so every residual row is absorbed;
* the complete affine packet ideal lies in `C`;
* every powered packet owner lies in the matching power of `C`;
* every separately registered coefficient owner lies in the required power of
  `C`; and
* every selected correction component is essential.

Properness, regularity, passive safety and SNC remain independent legality
gates.  The compiler closes the finite marked-selection part of the hybrid
architecture without assuming those geometric properties.
-/

namespace PCRLean
namespace Experimental
namespace SplitMatrixMarkedHybridCompiler

noncomputable section

universe u v w x y

variable {R : Type u} [CommRing R]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {Component : Type x} [Fintype Component] [DecidableEq Component]
variable {Owner : Type y} [Fintype Owner]

open SplitMatrixOrderIdealHybrid
open OrderIdealMarkedClosureCompiler
open AffinePacketHybridEffectivity

variable {M : Matrix κ ι R}
variable (S : SplitMatrixOrderIdealHybrid.SplitPacket M)
variable (b : SplitMatrixOrderIdealHybrid.Target (R := R) (κ := κ))
variable (component : Component → Ideal R)
variable (Q : Requirements (R := R) (Owner := Owner))
variable
  (hfull : Acceptable (S.defectIdeal b) component Q Finset.univ)

/-- Cardinal-minimal coefficient closure certificate. -/
noncomputable def closureCertificate :
    OrderIdealMarkedClosureCompiler.Certificate
      (S.defectIdeal b) component Q :=
  OrderIdealMarkedClosureCompiler.certificate
    (S.defectIdeal b) component Q hfull

/-- Selected coefficient defect closure. -/
def coefficientClosure : Ideal R :=
  (closureCertificate S b component Q hfull).ideal

/-- Actual polynomial graph-plus-marked-defect centre. -/
def centreIdeal : Ideal (MvPolynomial ι R) :=
  hybridIdeal (coefficientClosure S b component Q hfull) (S.graph b)

/-- The raw order ideal is retained in the marked closure. -/
theorem rawDefect_le_coefficientClosure :
    S.defectIdeal b ≤ coefficientClosure S b component Q hfull :=
  (closureCertificate S b component Q hfull).base_le

/-- Every graph residual belongs to the selected coefficient closure. -/
theorem graph_residual_mem_closure (r : κ) :
    (M.mulVec (S.graph b)) r - b r ∈
      coefficientClosure S b component Q hfull :=
  rawDefect_le_coefficientClosure S b component Q hfull
    (S.graph_residual_mem_defectIdeal b r)

/-- The complete original affine packet ideal lies in the selected actual
hybrid centre. -/
theorem equationIdeal_le_centreIdeal :
    MaximalMinorEquationIdeal.equationIdeal M b ≤
      centreIdeal S b component Q hfull :=
  AffinePacketHybridEffectivity.equationIdeal_le_hybridIdeal
    M b (S.graph b) (coefficientClosure S b component Q hfull)
    (graph_residual_mem_closure S b component Q hfull)

/-- Every powered packet owner is permissible for the same selected centre. -/
theorem poweredEquationIdeal_le_centreIdeal_pow (q : Nat) :
    AffinePacketHybridEffectivity.poweredEquationIdeal M b q ≤
      (centreIdeal S b component Q hfull) ^ q :=
  AffinePacketHybridEffectivity.poweredEquationIdeal_le_hybridIdeal_pow
    M b (S.graph b) (coefficientClosure S b component Q hfull)
    (graph_residual_mem_closure S b component Q hfull) q

/-- Each coefficient owner, extended to the polynomial ring, satisfies its
registered marked-power requirement for the selected centre. -/
theorem extended_ownerIdeal_le_centreIdeal_pow (o : Owner) :
    Ideal.map MvPolynomial.C (Q.ownerIdeal o) ≤
      (centreIdeal S b component Q hfull) ^ (Q.mark o) := by
  calc
    Ideal.map MvPolynomial.C (Q.ownerIdeal o) ≤
        Ideal.map MvPolynomial.C
          ((coefficientClosure S b component Q hfull) ^ (Q.mark o)) :=
      Ideal.map_mono
        ((closureCertificate S b component Q hfull).owner_le_power o)
    _ = (extendedIdeal
          (coefficientClosure S b component Q hfull)) ^ (Q.mark o) := by
      rw [extendedIdeal, Ideal.map_pow]
    _ ≤ (centreIdeal S b component Q hfull) ^ (Q.mark o) := by
      gcongr
      exact le_sup_right

/-- Every selected correction component is present in the coefficient closure. -/
theorem selected_component_le
    {a : Component}
    (ha : a ∈ (closureCertificate S b component Q hfull).selected) :
    component a ≤ coefficientClosure S b component Q hfull :=
  (closureCertificate S b component Q hfull).selected_component_le ha

/-- Every selected correction component is essential for the registered marked
requirements. -/
theorem selected_component_essential
    {a : Component}
    (ha : a ∈ (closureCertificate S b component Q hfull).selected) :
    ¬ Acceptable (S.defectIdeal b) component Q
      ((closureCertificate S b component Q hfull).selected.erase a) :=
  (closureCertificate S b component Q hfull).erase_not_acceptable ha

/-- The selected polynomial centre is finite type over a Noetherian ambient
polynomial ring. -/
theorem centreIdeal_fg
    [IsNoetherianRing (MvPolynomial ι R)] :
    (centreIdeal S b component Q hfull).FG :=
  IsNoetherian.noetherian _

end

end SplitMatrixMarkedHybridCompiler
end Experimental
end PCRLean
