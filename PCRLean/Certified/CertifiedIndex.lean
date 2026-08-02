import PCRLean.Algebra.MarkedIdeal
import PCRLean.Algebra.ControlledTransform
import PCRLean.Algebra.CharacteristicTwoGauge
import PCRLean.Algebra.SquareCleaningDerivative
import PCRLean.Algebra.OddContactDerivative
import PCRLean.Algebra.QuasilinearPolar
import PCRLean.Algebra.PerfectQuasilinearRoot
import PCRLean.Algebra.FrobeniusPolynomialRoot
import PCRLean.Algebra.UnitCocycleIdeal
import PCRLean.Algebra.JointOwners
import PCRLean.Algebra.PassiveFlatness
import PCRLean.Chambers.FrobeniusContent
import PCRLean.Chambers.FrobeniusContentProgram
import PCRLean.Chambers.OddCusp
import PCRLean.Chambers.OddCuspProgram
import PCRLean.Chambers.RamifiedQuadratic
import PCRLean.Chambers.RamifiedQuadraticProgram
import PCRLean.Chambers.ArtinSchreier
import PCRLean.Chambers.ArtinSchreierProgram
import PCRLean.Chambers.PurelyInseparable
import PCRLean.Chambers.PurelyInseparableProgram
import PCRLean.Chambers.RadicialDifferential
import PCRLean.Chambers.AllChartPrograms
import PCRLean.Chambers.ClosedGrammar
import PCRLean.Termination.Generational
import PCRLean.Termination.FiniteSources
import PCRLean.Termination.GenerationSystem
import PCRLean.Termination.PacketMultiset
import PCRLean.Framework.RankedSystem
import PCRLean.Framework.FiniteChartProgram
import PCRLean.Framework.GeometricProgram
import PCRLean.Framework.UniversalCompiler
import PCRLean.NoGo.PersistentObstruction
import PCRLean.NoGo.FreshBirth
import PCRLean.NoGo.CoordinatewiseDropCycle
import PCRLean.NoGo.FiniteJetBlindness
import PCRLean.NoGo.RelativeImperfection

/-!
# Certified kernel index

Only declarations proved without `sorry`, `admit`, or project-specific axioms
are imported here.  This is deliberately not a theorem of arbitrary-dimensional
resolution.  It is the current kernel-checked algebraic, all-chart,
termination, finite-source, and obstruction-audit layer.
-/

namespace PCRLean.Certified

open PCRLean.Chambers
open PCRLean.Termination

/-- The restricted generational compiler has a genuine well-founded backend. -/
theorem generational_backend_wf :
    WellFounded Generational.GenLt :=
  Generational.genLt_wellFounded

/-- The accepted finite-source transition relation itself is well founded. -/
theorem finite_source_generation_wf :
    WellFounded GenerationSystem.Step :=
  GenerationSystem.step_wellFounded

/-- The finite packet-multiset compiler has a genuine well-founded backend. -/
theorem packet_multiset_backend_wf {α : Type*} [Preorder α] [WellFoundedLT α] :
    WellFounded (PacketMultiset.PacketLt : Multiset α → Multiset α → Prop) :=
  PacketMultiset.packetLt_wellFounded

/-- A genuinely finite ancestor carrier cannot finance infinitely many births
when the payment map is injective. -/
theorem finite_carrier_excludes_infinite_births
    {Coupon : Type*} [Finite Coupon] (pay : ℕ → Coupon) :
    ¬ Function.Injective pay :=
  FiniteSources.no_infinite_financed_births pay

end PCRLean.Certified

#print axioms PCRLean.Algebra.oddCusp_principal_permissible
#print axioms PCRLean.Algebra.ramifiedQuadratic_principal_permissible
#print axioms PCRLean.Algebra.artinSchreier_principal_permissible
#print axioms PCRLean.Algebra.ControlledTransform.Certificate.compose
#print axioms PCRLean.Algebra.ControlledTransform.ChartPackage.factorization
#print axioms PCRLean.Algebra.CharacteristicTwoGauge.purelyInseparable_cleaning
#print axioms PCRLean.Algebra.CharacteristicTwoGauge.artinSchreier_cleaning
#print axioms PCRLean.Algebra.SquareCleaningDerivative.derivative_square
#print axioms PCRLean.Algebra.SquareCleaningDerivative.jacobian_span_invariant
#print axioms PCRLean.Algebra.OddContactDerivative.derivative_odd_power
#print axioms PCRLean.Algebra.OddContactDerivative.derivative_even_power
#print axioms PCRLean.Algebra.QuasilinearPolar.frobenius_additive
#print axioms PCRLean.Algebra.QuasilinearPolar.frobenius_polar_zero
#print axioms PCRLean.Algebra.QuasilinearPolar.scalar_frobenius_polar_zero
#print axioms PCRLean.Algebra.QuasilinearPolar.diagonal_frobenius_polar_zero
#print axioms PCRLean.Algebra.PerfectQuasilinearRoot.root_pow
#print axioms PCRLean.Algebra.PerfectQuasilinearRoot.finset_sum_pow_char_pow
#print axioms PCRLean.Algebra.PerfectQuasilinearRoot.linearRoot_pow
#print axioms PCRLean.Algebra.PerfectQuasilinearRoot.cleaning_identity
#print axioms PCRLean.Algebra.FrobeniusPolynomialRoot.rootPolynomial_pow_of_derivative_eq_zero
#print axioms PCRLean.Algebra.FrobeniusPolynomialRoot.derivative_eq_zero_of_eq_pow
#print axioms PCRLean.Algebra.FrobeniusPolynomialRoot.derivative_eq_zero_iff_exists_frobenius_root
#print axioms PCRLean.Algebra.FrobeniusPolynomialRoot.frobenius_root_unique
#print axioms PCRLean.Algebra.UnitCocycleIdeal.span_singleton_unit_mul
#print axioms PCRLean.Algebra.UnitCocycleIdeal.span_singleton_eq_of_eq_unit_mul
#print axioms PCRLean.Algebra.UnitCocycleIdeal.PrincipalUnitAtlas.ideal_eq
#print axioms PCRLean.Algebra.UnitCocycleIdeal.PrincipalUnitAtlas.gluedIdeal_eq
#print axioms PCRLean.Algebra.JointOwners.combinedIdeal_le_iff
#print axioms PCRLean.Algebra.JointOwners.combined_owner_permissible
#print axioms PCRLean.Algebra.JointOwners.each_owner_permissible_of_combined
#print axioms PCRLean.Algebra.PassiveFlatness.flat_of_free
#print axioms PCRLean.Algebra.PassiveFlatness.flat_of_projective
#print axioms PCRLean.Algebra.PassiveFlatness.rTensor_injective
#print axioms PCRLean.Algebra.PassiveFlatness.rTensor_injective_of_free
#print axioms PCRLean.Chambers.FrobeniusContent.active_factorization
#print axioms PCRLean.Chambers.FrobeniusContent.sibling_factorization
#print axioms PCRLean.Chambers.FrobeniusContentProgram.step_decreases
#print axioms PCRLean.Chambers.FrobeniusContentProgram.active_reaches_exit
#print axioms PCRLean.Chambers.OddCusp.sChart_factorization
#print axioms PCRLean.Chambers.OddCusp.yChart_factorization
#print axioms PCRLean.Chambers.OddCuspProgram.step_decreases
#print axioms PCRLean.Chambers.OddCuspProgram.active_reaches_resolved
#print axioms PCRLean.Chambers.RamifiedQuadratic.collision_factorization
#print axioms PCRLean.Chambers.RamifiedQuadratic.sibling_factorization
#print axioms PCRLean.Chambers.RamifiedQuadraticProgram.step_decreases
#print axioms PCRLean.Chambers.RamifiedQuadraticProgram.active_reaches_resolved
#print axioms PCRLean.Chambers.ArtinSchreier.collision_factorization
#print axioms PCRLean.Chambers.ArtinSchreier.sibling_factorization
#print axioms PCRLean.Chambers.ArtinSchreier.collisionDepth_add_step
#print axioms PCRLean.Chambers.ArtinSchreierProgram.step_decreases
#print axioms PCRLean.Chambers.ArtinSchreierProgram.active_reaches_classified_exit
#print axioms PCRLean.Chambers.PurelyInseparable.square_gauge
#print axioms PCRLean.Chambers.PurelyInseparable.even_collision_factorization
#print axioms PCRLean.Chambers.PurelyInseparable.final_t_pivot
#print axioms PCRLean.Chambers.PurelyInseparable.final_z_pivot
#print axioms PCRLean.Chambers.PurelyInseparable.pure_collision_factorization
#print axioms PCRLean.Chambers.PurelyInseparableProgram.step_decreases
#print axioms PCRLean.Chambers.PurelyInseparableProgram.active_reaches_radicial_exit
#print axioms PCRLean.Chambers.RadicialDifferential.pderiv_sq_zero
#print axioms PCRLean.Chambers.RadicialDifferential.pderiv_add_sq
#print axioms PCRLean.Chambers.RadicialDifferential.euler_odd
#print axioms PCRLean.Chambers.RadicialDifferential.jacobianIdeal_eq_top_of_isUnit_pderiv
#print axioms PCRLean.Chambers.RadicialDifferential.odd_homogeneous_mem_jacobianIdeal
#print axioms PCRLean.Chambers.AllChartPrograms.FrobeniusContent.allChartsResolve
#print axioms PCRLean.Chambers.AllChartPrograms.OddCusp.allChartsResolve
#print axioms PCRLean.Chambers.AllChartPrograms.RamifiedQuadratic.allChartsResolve
#print axioms PCRLean.Chambers.AllChartPrograms.ArtinSchreier.allChartsClassified
#print axioms PCRLean.Chambers.ClosedGrammar.resolves_every_packet
#print axioms PCRLean.Chambers.ClosedGrammar.classifies_every_packet
#print axioms PCRLean.Termination.Generational.genLt_wellFounded
#print axioms PCRLean.Termination.FiniteSources.financed_birth_bound
#print axioms PCRLean.Termination.FiniteSources.financed_birth_finset_bound
#print axioms PCRLean.Termination.FiniteSources.active_identity_bound
#print axioms PCRLean.Termination.FiniteSources.no_infinite_financed_births
#print axioms PCRLean.Termination.FiniteSources.clone_breaks_injectivity
#print axioms PCRLean.Termination.GenerationSystem.step_rank_drop
#print axioms PCRLean.Termination.GenerationSystem.step_wellFounded
#print axioms PCRLean.Termination.PacketMultiset.packetLt_wellFounded
#print axioms PCRLean.Termination.PacketMultiset.replace_block_lt
#print axioms PCRLean.Termination.PacketMultiset.PacketSystem.step_wellFounded
#print axioms PCRLean.Framework.RankedSystem.step_wellFounded
#print axioms PCRLean.Framework.CertifiedProgram.reaches_terminal
#print axioms PCRLean.Framework.CertifiedProgram.reaches_resolved
#print axioms PCRLean.Framework.FiniteChartProgram.resolvesAll
#print axioms PCRLean.Framework.FiniteChartProgram.resolved_of_leaf
#print axioms PCRLean.Framework.GeometricProgram.resolvesAll
#print axioms PCRLean.Framework.UniversalProgramFamily.resolvesAllInputs
#print axioms PCRLean.NoGo.ObstructionSystem.preserves_path
#print axioms PCRLean.NoGo.ObstructionSystem.nonzero_persists
#print axioms PCRLean.NoGo.FreshBirth.not_wellFounded
#print axioms PCRLean.NoGo.CoordinatewiseDropCycle.not_wellFounded
#print axioms PCRLean.NoGo.FiniteJetBlindness.X_pow_coeff_zero_below
#print axioms PCRLean.NoGo.FiniteJetBlindness.zero_and_X_pow_agree_below
#print axioms PCRLean.NoGo.FiniteJetBlindness.X_pow_ne_zero
#print axioms PCRLean.NoGo.FiniteJetBlindness.fixed_cutoff_not_faithful
#print axioms PCRLean.NoGo.RelativeImperfection.cast_prime_power_eq_zero
#print axioms PCRLean.NoGo.RelativeImperfection.derivative_frobenius_power_zero
#print axioms PCRLean.NoGo.RelativeImperfection.X_not_frobenius_power
#print axioms PCRLean.NoGo.RelativeImperfection.frobenius_not_surjective
#print axioms PCRLean.Certified.generational_backend_wf
#print axioms PCRLean.Certified.finite_source_generation_wf
#print axioms PCRLean.Certified.packet_multiset_backend_wf
#print axioms PCRLean.Certified.finite_carrier_excludes_infinite_births
