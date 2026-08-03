import Mathlib
import PCRLean.Experimental.NoetherianOrbitDualRegularCentre
import PCRLean.Experimental.ConormalAffinePacketCoordinates

/-!
# Noetherian affine orbit packets

A represented operator orbit supplies covector rows

`pair : D → T∨`.

For graph-centre synthesis one also needs affine right-hand sides.  We therefore
add a linear trace

`value : D → K`

and interpret each orbit element `d` as the affine equation

`pair(d)(x) = value(d)`.

If a finite raw packet spans the Noetherian orbit module, satisfaction of its
finite affine equations is equivalent to satisfaction of every equation in the
entire infinite orbit.  The proof is linear span induction.  Consequently:

* the affine solution predicate is independent of the noncanonical finite
  packet chosen by Noetherianity; and
* after choosing finite coordinates on `T`, the finite packet feeds directly
  into the maximal-minor/augmented-minor compiler and yields a unique solution
  of the complete infinite orbit.

The remaining geometric bridge is to construct the covector representation and
rhs trace from an arbitrary Frobenius--Hasse state and prove the determinant
conditions.
-/

namespace PCRLean
namespace Experimental
namespace NoetherianAffineOrbitPacket

noncomputable section

universe u v w x y

variable {K : Type u} [Field K]
variable {D : Type v} {T : Type w} {Op : Type x}
variable [AddCommGroup D] [Module K D]
variable [AddCommGroup T] [Module K T]
variable [IsNoetherian K D]
variable [FiniteDimensional K T]

abbrev Cotangent := Module.Dual K T

variable {ops : Op → Module.End K D} {seed : D}
variable {pair : D →ₗ[K] Cotangent (K := K) (T := T)}
variable {value : D →ₗ[K] K}

/-- Affine equation attached to one represented orbit element. -/
def EquationAt (x : T) (d : D) : Prop :=
  pair d x = value d

/-- Satisfaction of every equation in the infinite orbit module. -/
def OrbitSolution (x : T) : Prop :=
  ∀ d : D,
    d ∈ NoetherianOperatorOrbit.orbitModule ops seed →
      EquationAt (pair := pair) (value := value) x d

/-- Finite affine conormal packet associated to one raw orbit certificate. -/
def finitePacket
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair) :
    ConormalAffinePacketCoordinates.Packet
      (K := K) (V := T) (κ := C.packet) where
  row := fun d => pair d.1
  rhs := fun d => value d.1

/-- Satisfaction of the chosen finite affine packet. -/
def FiniteSolution
    (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
    (x : T) : Prop :=
  ∀ d : C.packet, EquationAt (pair := pair) (value := value) x d.1

namespace Certificate

variable (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)

/-- A finite solution extends by linearity to the whole orbit module. -/
theorem orbitSolution_of_finiteSolution
    {x : T} (hx : FiniteSolution (value := value) C x) :
    OrbitSolution (ops := ops) (seed := seed)
      (pair := pair) (value := value) x := by
  intro d hd
  rw [C.packet_spans] at hd
  induction hd using Submodule.span_induction with
  | mem d hd =>
      exact hx ⟨d, hd⟩
  | zero =>
      simp [EquationAt]
  | add d e hd he ihd ihe =>
      simpa [EquationAt, map_add, ihd, ihe]
  | smul a d hd ih =>
      simpa [EquationAt, map_smul, ih]

/-- Restriction of an orbit solution to the finite packet. -/
theorem finiteSolution_of_orbitSolution
    {x : T}
    (hx : OrbitSolution (ops := ops) (seed := seed)
      (pair := pair) (value := value) x) :
    FiniteSolution (value := value) C x := by
  intro d
  apply hx d.1
  rw [C.packet_spans]
  exact Submodule.subset_span d.2

/-- Exact finite/infinite affine solution equivalence. -/
theorem finiteSolution_iff_orbitSolution (x : T) :
    FiniteSolution (value := value) C x ↔
      OrbitSolution (ops := ops) (seed := seed)
        (pair := pair) (value := value) x :=
  ⟨C.orbitSolution_of_finiteSolution,
    C.finiteSolution_of_orbitSolution⟩

/-- The finite affine packet evaluator is the finite solution predicate. -/
theorem finitePacket_solution_iff (x : T) :
    (finitePacket (value := value) C).evaluate x =
        (finitePacket (value := value) C).rhs ↔
      FiniteSolution (value := value) C x := by
  constructor
  · intro h d
    exact congrFun h d
  · intro h
    funext d
    exact h d

/-- Hence the finite packet evaluator is equivalent to the full orbit
solution predicate. -/
theorem finitePacket_solution_iff_orbitSolution (x : T) :
    (finitePacket (value := value) C).evaluate x =
        (finitePacket (value := value) C).rhs ↔
      OrbitSolution (ops := ops) (seed := seed)
        (pair := pair) (value := value) x := by
  rw [C.finitePacket_solution_iff (value := value) x,
    C.finiteSolution_iff_orbitSolution (value := value) x]

end Certificate

/-- Two different finite Noetherian packets define the same affine solution
predicate because both are equivalent to the complete orbit predicate. -/
theorem finitePacket_choice_independent
    (C E : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
    (x : T) :
    (finitePacket (value := value) C).evaluate x =
        (finitePacket (value := value) C).rhs ↔
      (finitePacket (value := value) E).evaluate x =
        (finitePacket (value := value) E).rhs := by
  rw [C.finitePacket_solution_iff_orbitSolution (value := value) x,
    E.finitePacket_solution_iff_orbitSolution (value := value) x]

section Coordinates

variable {σ : Type y} [Fintype σ] [DecidableEq σ] [Nonempty σ]
variable (C : NoetherianOrbitDualRegularCentre.Certificate ops seed pair)
variable (Frame : T ≃ₗ[K] (σ → K))
variable [IsNoetherianRing K] [IsRegularRing K]
variable
  (Hrank : MaximalMinorAtlas.FullRankCover
    ((finitePacket (value := value) C).matrix Frame))
variable
  (Haug : MaximalMinorAugmentedPacket.AugmentedRankCondition
    ((finitePacket (value := value) C).matrix Frame)
    (finitePacket (value := value) C).rhs)

/-- Intrinsic solution supplied by the finite determinantal packet. -/
noncomputable def intrinsicSolution : T :=
  (finitePacket (value := value) C).intrinsicSolution
    Frame Hrank Haug

/-- The determinantal solution satisfies every equation in the complete
infinite operator orbit. -/
theorem intrinsicSolution_isOrbitSolution :
    OrbitSolution (ops := ops) (seed := seed)
      (pair := pair) (value := value)
      (intrinsicSolution (value := value) C Frame Hrank Haug) := by
  apply (C.finitePacket_solution_iff_orbitSolution
    (value := value)
    (intrinsicSolution (value := value) C Frame Hrank Haug)).mp
  exact (finitePacket (value := value) C).intrinsicSolution_solves
    Frame Hrank Haug

/-- The complete infinite affine orbit has a unique intrinsic solution in the
represented finite-dimensional chamber. -/
theorem existsUnique_orbitSolution :
    ∃! x : T,
      OrbitSolution (ops := ops) (seed := seed)
        (pair := pair) (value := value) x := by
  refine ⟨intrinsicSolution (value := value) C Frame Hrank Haug,
    intrinsicSolution_isOrbitSolution
      (value := value) C Frame Hrank Haug, ?_⟩
  intro x hx
  apply (finitePacket (value := value) C).solution_eq_intrinsicSolution
    Frame Hrank Haug
  exact (C.finitePacket_solution_iff_orbitSolution
    (value := value) x).mpr hx

end Coordinates

end

end NoetherianAffineOrbitPacket
end Experimental
end PCRLean
