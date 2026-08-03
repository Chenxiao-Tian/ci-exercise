import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Operations
import PCRLean.Experimental.FrobeniusNormalCentre

/-!
# Finite basic-open descent of Frobenius-normal filtrations

Let `s_i ∈ A` generate the unit ideal.  For each `i`, choose a localization
`B_i = A[s_i⁻¹]`.  If the extension of a centre ideal `I` to every `B_i`
reflects prime-power roots in its adic filtration, then `I` reflects them in
`A`.

The proof is a genuine finite-cover patching argument rather than a hidden
single faithfully flat chart:

1. extend `x^(p^e) ∈ I^((p^e)m)` to each localization;
2. use local Frobenius reflection to obtain `x/1 ∈ I^m B_i`;
3. clear one power of `s_i`, obtaining `s_i^n x ∈ I^m`; and
4. use that the `s_i` generate `1` to patch these memberships globally.

This is the algebraic descent mechanism needed for a finite Fitting-minor atlas.
The remaining geometric theorem is to construct such a finite cover and prove
that each localized centre has a coordinate or graph model.
-/

namespace PCRLean
namespace Experimental
namespace FrobeniusNormalBasicOpenDescent

noncomputable section

universe u v w

variable {A : Type u} [CommRing A]
variable {κ : Type v} [Fintype κ]
variable (s : κ → A)
variable (B : κ → Type w)
variable [∀ i, CommRing (B i)]
variable [∀ i, Algebra A (B i)]
variable [∀ i, IsLocalization (Submonoid.powers (s i)) (B i)]

/-- Extension of an ideal to one basic-open chart. -/
def localIdeal (I : Ideal A) (i : κ) : Ideal (B i) :=
  Ideal.map (algebraMap A (B i)) I

/-- Local ideal powers are extensions of global ideal powers. -/
theorem localIdeal_pow (I : Ideal A) (i : κ) (n : Nat) :
    localIdeal s B (I ^ n) i = (localIdeal s B I i) ^ n := by
  exact Ideal.map_pow (algebraMap A (B i)) I n

/-- Membership in a localized ideal gives membership after multiplying by one
power of the basic-open generator. -/
theorem exists_power_smul_mem_of_map_mem
    (I : Ideal A) (i : κ) (x : A)
    (hx : algebraMap A (B i) x ∈ localIdeal s B I i) :
    ∃ n : Nat, (s i) ^ n * x ∈ I := by
  have hloc :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers (s i)) (S := B i) I x).mp hx
  rcases hloc with ⟨t, ht, htx⟩
  rcases ht with ⟨n, rfl⟩
  exact ⟨n, htx⟩

/-- Frobenius-normality descends from a finite basic-open cover. -/
theorem reflectsFrobeniusPowers_of_basicOpenCover
    (p : Nat) (I : Ideal A)
    (hcover : Ideal.span (Set.range s) = ⊤)
    (hlocal : ∀ i : κ,
      FrobeniusNormalCentre.ReflectsFrobeniusPowers p
        (localIdeal s B I i)) :
    FrobeniusNormalCentre.ReflectsFrobeniusPowers p I := by
  intro e mark x hx
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (I ^ mark) (Set.range s) hcover x
  rintro ⟨r, hr⟩
  rcases hr with ⟨i, rfl⟩
  have hxmap0 :
      algebraMap A (B i) (x ^ (p ^ e)) ∈
        localIdeal s B (I ^ ((p ^ e) * mark)) i :=
    Ideal.mem_map_of_mem (algebraMap A (B i)) hx
  have hxmap :
      (algebraMap A (B i) x) ^ (p ^ e) ∈
        (localIdeal s B I i) ^ ((p ^ e) * mark) := by
    rw [map_pow] at hxmap0
    rw [localIdeal_pow] at hxmap0
    exact hxmap0
  have hroot :
      algebraMap A (B i) x ∈ (localIdeal s B I i) ^ mark :=
    hlocal i e mark (algebraMap A (B i) x) hxmap
  have hroot' :
      algebraMap A (B i) x ∈ localIdeal s B (I ^ mark) i := by
    rw [localIdeal_pow]
    exact hroot
  obtain ⟨n, hn⟩ :=
    exists_power_smul_mem_of_map_mem s B (I ^ mark) i x hroot'
  refine ⟨n, ?_⟩
  simpa [smul_eq_mul] using hn

/-- Exact scaled marked heredity on the base ring, obtained from the finite
basic-open cover. -/
theorem power_mem_scaled_iff_of_basicOpenCover
    (p : Nat) (I : Ideal A)
    (hcover : Ideal.span (Set.range s) = ⊤)
    (hlocal : ∀ i : κ,
      FrobeniusNormalCentre.ReflectsFrobeniusPowers p
        (localIdeal s B I i))
    (e mark : Nat) (x : A) :
    x ^ (p ^ e) ∈ I ^ ((p ^ e) * mark) ↔ x ∈ I ^ mark := by
  exact FrobeniusNormalCentre.power_mem_scaled_iff p I
    (reflectsFrobeniusPowers_of_basicOpenCover s B p I hcover hlocal)
    e mark x

end

end FrobeniusNormalBasicOpenDescent
end Experimental
end PCRLean
