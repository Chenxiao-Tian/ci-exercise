# U2 Arbitrary Base Change CI Result

- source commit: `996b2dd81e4d629e4bbd7f02f353df2da7fba0f4`
- workflow run: `30777085338`
- placeholder rejection: success
- build: failure
- axiom audit: failure

## basechange-placeholders.txt
```text
```

## basechange-build.txt
```text
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:62:7: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:64:9: Unknown identifier `S.baseChange`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:71:6: Invalid field `residualLinear`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.residualLinear`, so it is not possible to project the field `residualLinear` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:76:6: Invalid field `residualLinear`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.residualLinear`, so it is not possible to project the field `residualLinear` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:81:29: Invalid field `residualLinear`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.residualLinear`, so it is not possible to project the field `residualLinear` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:82:9: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:83:6: Failed to rewrite using equation theorems for `residualLinear`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:90:7: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:92:12: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:93:10: Invalid field `baseChange_residualLinear`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange_residualLinear`, so it is not possible to project the field `baseChange_residualLinear` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:91:30: unsolved goals
R : Type uR
A : Type uA
inst✝⁶ : CommRing R
inst✝⁵ : CommRing A
inst✝⁴ : Algebra R A
V : Type uV
W : Type uW
inst✝³ : AddCommGroup V
inst✝² : Module R V
inst✝¹ : AddCommGroup W
inst✝ : Module R W
S : SplitSurjection
a : A
x : V
⊢ sorry = a ⊗ₜ[R] S.residual x
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:100:7: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:103:9: unsolved goals
case zero
R : Type uR
A : Type uA
inst✝⁶ : CommRing R
inst✝⁵ : CommRing A
inst✝⁴ : Algebra R A
V : Type uV
W : Type uW
inst✝³ : AddCommGroup V
inst✝² : Module R V
inst✝¹ : AddCommGroup W
inst✝ : Module R W
S : SplitSurjection
⊢ sorry () ∈ Submodule.baseChange A S.project.ker
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:106:12: Invalid field `baseChange_residual_tmul`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange_residual_tmul`, so it is not possible to project the field `baseChange_residual_tmul` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:111:13: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:112:15: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:113:17: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
warning: PCRLean/Experimental/SplitSurjectionBaseChange.lean:104:12: This simp argument is unused:
  SplitSurjection.residual

Hint: Omit it from the simp argument list.
  simp ̵[̵S̵p̵l̵i̵t̵S̵u̵r̵j̵e̵c̵t̵i̵o̵n̵.̵r̵e̵s̵i̵d̵u̵a̵l̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:128:19: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:128:58: unsolved goals
R : Type uR
A : Type uA
inst✝⁶ : CommRing R
inst✝⁵ : CommRing A
inst✝⁴ : Algebra R A
V : Type uV
W : Type uW
inst✝³ : AddCommGroup V
inst✝² : Module R V
inst✝¹ : AddCommGroup W
inst✝ : Module R W
S : SplitSurjection
z : TensorProduct R A V
hz : z ∈ (LinearMap.baseChange A S.project).ker
hzero : (LinearMap.baseChange A S.project) z = 0
⊢ sorry () = z
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:131:12: Invalid field `baseChange_residual_mem`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange_residual_mem`, so it is not possible to project the field `baseChange_residual_mem` from an expression
  S
of type `SplitSurjection`
warning: PCRLean/Experimental/SplitSurjectionBaseChange.lean:129:12: This simp argument is unused:
  SplitSurjection.residual

Hint: Omit it from the simp argument list.
  simp [S̵p̵l̵i̵t̵S̵u̵r̵j̵e̵c̵t̵i̵o̵n̵.̵r̵e̵s̵i̵d̵u̵a̵l̵,̵ ̵baseChange, hzero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: PCRLean/Experimental/SplitSurjectionBaseChange.lean:129:38: This simp argument is unused:
  baseChange

Hint: Omit it from the simp argument list.
  simp [SplitSurjection.residual, b̵a̵s̵e̵C̵h̵a̵n̵g̵e̵,̵ ̵hzero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: PCRLean/Experimental/SplitSurjectionBaseChange.lean:129:50: This simp argument is unused:
  hzero

Hint: Omit it from the simp argument list.
  simp [SplitSurjection.residual, baseChange,̵ ̵h̵z̵e̵r̵o̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:142:7: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:154:9: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:156:9: Invalid `⟨...⟩` notation: The expected type of this term could not be determined
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:164:11: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: PCRLean/Experimental/SplitSurjectionBaseChange.lean:166:5: Invalid field `baseChange`: The environment does not contain `PCRLean.Experimental.SplitSurjectionSymmetricQuotient.SplitSurjection.baseChange`, so it is not possible to project the field `baseChange` from an expression
  S
of type `SplitSurjection`
error: Lean exited with code 1
Some required targets logged failures:
- PCRLean.Experimental.SplitSurjectionBaseChange
error: build failed
```

## basechange-axioms.txt
```text
PCRLean/Experimental/SplitSurjectionBaseChangeAudit.lean:1:0: error: object file '/home/runner/work/ci-exercise/ci-exercise/.lake/build/lib/lean/PCRLean/Experimental/SplitSurjectionBaseChange.olean' of module PCRLean.Experimental.SplitSurjectionBaseChange does not exist
```
