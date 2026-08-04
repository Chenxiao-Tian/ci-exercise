import Mathlib

/-!
# Finite Artin--Rees tail compiler

Artin--Rees turns an induced filtration into a finite prefix followed by a tail
obtained recursively from one cutoff layer.  The geometric X038 packet uses
this to replace infinitely many exceptional-torsion degrees by a finite window,
a tail seed, and one propagation law.

This file proves only the logical/numerical compiler.  It does not prove the
Artin--Rees theorem, construct an induced filtration, or identify a geometric
Rees-interchange defect.
-/

namespace PCRLean
namespace Experimental
namespace ArtinReesTailCompiler

noncomputable section

/-- A finite prefix, one cutoff value, and an eventual successor law. -/
structure Packet (Good : ℕ → Prop) where
  cutoff : ℕ
  prefixCert : ∀ n, n < cutoff → Good n
  seed : Good cutoff
  tailStep : ∀ n, cutoff ≤ n → Good n → Good (n + 1)

namespace Packet

variable {Good : ℕ → Prop}

/-- Every degree is certified by the finite prefix or by induction from the
Artin--Rees cutoff. -/
theorem all_degrees (P : Packet Good) : ∀ n, Good n := by
  intro n
  induction n with
  | zero =>
      by_cases h : 0 < P.cutoff
      · exact P.prefixCert 0 h
      · have hc : P.cutoff = 0 := by omega
        simpa [hc] using P.seed
  | succ n ih =>
      by_cases hprefix : n + 1 < P.cutoff
      · exact P.prefixCert (n + 1) hprefix
      · by_cases hseed : n + 1 = P.cutoff
        · simpa [hseed] using P.seed
        · have hcut : P.cutoff ≤ n := by omega
          exact P.tailStep n hcut ih

/-- Pointwise projection of the full degree certificate. -/
theorem degree (P : Packet Good) (n : ℕ) : Good n :=
  P.all_degrees n

end Packet

/-- A direct finite-prefix/tail induction theorem without packaging. -/
theorem all_of_prefix_seed_step
    (Good : ℕ → Prop) (cutoff : ℕ)
    (hprefix : ∀ n, n < cutoff → Good n)
    (hseed : Good cutoff)
    (hstep : ∀ n, cutoff ≤ n → Good n → Good (n + 1)) :
    ∀ n, Good n := by
  exact (Packet.mk cutoff hprefix hseed hstep).all_degrees

end

end ArtinReesTailCompiler
end Experimental
end PCRLean
