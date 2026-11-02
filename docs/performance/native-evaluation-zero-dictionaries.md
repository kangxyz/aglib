# Native evaluation: preserve the actual category and zero dictionaries

## Validated scope and basis

This case records a repaired compiler boundary, not a whole-library speedup.
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, native
source basis `54d6974`; the native build profile retained jobs 8, threads 4
and its existing 12800 MiB frontend budget. No universe equality, new functor/category, suppression,
budget increase, kernel replay or separate client certification was introduced.

The actual native evaluation view is
`SheafOfModules.evaluation R U` followed by the existing module-to-additive
forgetful functor. The generic view retains independent site-object, site-Hom,
ring and module-carrier universes. The Scheme consumer uses its original open
restriction functor and original restricted-sections natural isomorphism.

The successful generic producer has SHA256
`fa65b570040a98bc0b94a8d5835b63f6fb9e3a5eaaec954d158aa50564d647d7`;
the successful actual consumer has SHA256
`845d9046a3a7155959dca9dac63b959a678c21628899b98103c0730fcf55054f`.
The producer passed in native run `remote-3770b014d5434f3c9f69893cd0249348`
(2.7 seconds); the original failed `Modules.Restriction.Sections` call passed
in `remote-a42752a32876442d986b24ed6a786bde` (7.4 seconds). The latter's source
content identity is
`4f5f0d2fa015ea24f2ba2815cea9f4daf7b4e88ad84663a5ed7c724dfcf9a566`,
and its complete SOURCE receipt SHA256 is
`8e18573e3612950c2e0ad56bc1917be68e5d15630345db6163a3e77d1135dca8`.
Other downstream closures were not accepted merely from these leaf passes.

## Failure and unsuccessful repairs

The actual failed call was `Functor.mapHomologicalComplexCompIso` at the
original restricted-sections cochain isomorphism. It could not synthesize
`(SheafOfModules.additiveEvaluation U.ringCatSheaf (op top)).PreservesZeroMorphisms`.
A native registration passed by itself while this original caller still failed.

A single cached probe, preserved below, ran as
`remote-aaf2737e9e7543cab048edfe0a0e7e4b` (14.3 seconds, one frontend).
Its native and Scheme direct synthesis examples and explicit delegation
succeeded; only the two actual CompIso variants at lines 49 and 60 failed.
The printed goal used `Scheme.Modules.instCategory` and zero morphisms from
`Abelian.toPreadditive (Scheme.Modules.instAbelian U)`. The generic registration
had the native module-sheaf structure head. All displayed value worlds matched;
collapsing independent universes was not a justified repair. A functor type
ascription alone did not pin the preservation class's implicit category data.

Generalizing the registration to arbitrary valid zero structures was sound,
because `HasZeroMorphisms` is subsingleton. A dependent `cases` normalization
failed in `remote-5bf804b1954b452789e97c3081f4da4f`: Lean generated the equation
`nativeSourceZero = sourceZero`. The repair instead formed the explicit
preservation proposition as a function of both dictionaries, proved its
canonical native case by `rfl`, and transported the proposition with
`congrArg2` and `Eq.mp`. The producer then passed, but the old CompIso caller
still failed in `remote-d821ca1c0eb2420eb529aede926b9ecb`.

The final caller repair supplies fully explicit local preservation witnesses,
including the original Scheme category and zero arguments, and delegates to
the existing generic proof by `exact`. This uses definitional conversion at
the actual wrapper boundary instead of asking instance search to reconstruct
that conversion. It copies no map-zero proof and installs no global Scheme
instance. Category structures are not assumed unique: only valid zero-morphism
structures at the fixed actual category are normalized by uniqueness.

## Accepted generic proof

```lean
instance additiveEvaluation_preservesZeroMorphisms (U : Cᵒᵖ)
    [sourceZero : Limits.HasZeroMorphisms (SheafOfModules.{m} R)]
    [targetZero : Limits.HasZeroMorphisms AddCommGrpCat.{m}] :
    (additiveEvaluation R U :
      SheafOfModules.{m} R ⥤ AddCommGrpCat.{m}).PreservesZeroMorphisms := by
  let nativeSourceZero : Limits.HasZeroMorphisms (SheafOfModules.{m} R) :=
    @Preadditive.preadditiveHasZeroMorphisms (SheafOfModules.{m} R) inferInstance
      (SheafOfModules.instPreadditive R)
  let nativeTargetZero : Limits.HasZeroMorphisms AddCommGrpCat.{m} :=
    @Preadditive.preadditiveHasZeroMorphisms AddCommGrpCat.{m} inferInstance
      AddCommGrpCat.instPreadditive
  let preserves (s : Limits.HasZeroMorphisms (SheafOfModules.{m} R))
      (t : Limits.HasZeroMorphisms AddCommGrpCat.{m}) : Prop :=
    @Functor.PreservesZeroMorphisms (SheafOfModules.{m} R) inferInstance
      AddCommGrpCat.{m} inferInstance s t (additiveEvaluation R U)
  have native : preserves nativeSourceZero nativeTargetZero := ⟨fun _ _ => rfl⟩
  exact Eq.mp (congrArg₂ preserves (Subsingleton.elim nativeSourceZero sourceZero)
    (Subsingleton.elim nativeTargetZero targetZero)) native
```

## Accepted original caller

```lean
def restrictedSectionsComplexIso (I : CochainComplex X.Modules ℕ) :
    ((SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).mapHomologicalComplex _).obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex _).obj I) ≅
      ((SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange)).mapHomologicalComplex
        _).obj I := by
  letI : @Functor.PreservesZeroMorphisms U.Modules inferInstance
      AddCommGrpCat.{u} inferInstance inferInstance inferInstance
      (SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)) := by
    exact SheafOfModules.additiveEvaluation_preservesZeroMorphisms U.ringCatSheaf (op ⊤)
      (sourceZero := (inferInstance : HasZeroMorphisms U.Modules))
      (targetZero := (inferInstance : HasZeroMorphisms AddCommGrpCat.{u}))
  letI : @Functor.PreservesZeroMorphisms X.Modules inferInstance
      AddCommGrpCat.{u} inferInstance inferInstance inferInstance
      (SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange)) := by
    exact SheafOfModules.additiveEvaluation_preservesZeroMorphisms
      X.ringCatSheaf (op j.opensRange)
      (sourceZero := (inferInstance : HasZeroMorphisms X.Modules))
      (targetZero := (inferInstance : HasZeroMorphisms AddCommGrpCat.{u}))
  exact (Functor.mapHomologicalComplexCompIso (restrictedSectionsIso j) (.up ℕ)).app I
```

## Complete diagnostic probe

This is a recorded cached native diagnostic, not an added package test or a
new acceptance chain. Its SHA256 is
`7b5cdb4eebaffea809bf3e59a42b3f50f1f27c3871e4a212584e883d85082e64`.

```lean
import Aglib.Algebra.Category.ModuleCat.Sheaf.Evaluation
import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
import Mathlib.Algebra.Homology.Additive

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

set_option pp.universes true
set_option pp.explicit true

#check @SheafOfModules.additiveEvaluation
#check @SheafOfModules.additiveEvaluation_preservesZeroMorphisms
#check @Functor.mapHomologicalComplexCompIso

-- Native source: should use the compiled generic registration.
example (S : Scheme.{u}) (V : S.Opens) :
    (SheafOfModules.additiveEvaluation S.ringCatSheaf (op V) :
      SheafOfModules.{u} S.ringCatSheaf ⥤ AddCommGrpCat.{u}).PreservesZeroMorphisms := by
  infer_instance

-- Same view, installed Scheme.Modules source: trace the actual synthesis head.
set_option trace.Meta.synthInstance true in
example (S : Scheme.{u}) (V : S.Opens) :
    (SheafOfModules.additiveEvaluation S.ringCatSheaf (op V) :
      S.Modules ⥤ AddCommGrpCat.{u}).PreservesZeroMorphisms := by
  infer_instance

-- Explicit delegation tests definitional conversion beyond instance search.
example (S : Scheme.{u}) (V : S.Opens) :
    (SheafOfModules.additiveEvaluation S.ringCatSheaf (op V) :
      S.Modules ⥤ AddCommGrpCat.{u}).PreservesZeroMorphisms := by
  exact SheafOfModules.additiveEvaluation_preservesZeroMorphisms S.ringCatSheaf (op V)

section
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
variable (e : Scheme.Modules.restrictFunctor j ⋙
    SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤) ≅
  SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange))
variable (I : CochainComplex X.Modules ℕ)

-- Original CompIso inference, with precisely the actual intermediate category.
set_option trace.Meta.synthInstance true in
example :
    ((SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).mapHomologicalComplex _).obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex _).obj I) ≅
      ((SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange)).mapHomologicalComplex
        _).obj I :=
  (Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I

-- Candidate delegation at the actual boundary, with no Scheme-specific map proof.
example :
    ((SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤)).mapHomologicalComplex _).obj
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex _).obj I) ≅
      ((SheafOfModules.additiveEvaluation X.ringCatSheaf (op j.opensRange)).mapHomologicalComplex
        _).obj I := by
  letI : (SheafOfModules.additiveEvaluation U.ringCatSheaf (op ⊤) :
      U.Modules ⥤ AddCommGrpCat.{u}).PreservesZeroMorphisms :=
    SheafOfModules.additiveEvaluation_preservesZeroMorphisms U.ringCatSheaf (op ⊤)
  exact (Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I
end
```

## Reuse and evidence limits

When a generic witness passes but the actual constructor still cannot infer it,
print the preservation predicate's implicit category and structure arguments.
Bind or pass the same existing witness at that exact head before changing
models, universes or proving a duplicate concrete instance. Use proof-only
proposition transport when normalizing unique structure dictionaries; do not
apply a uniqueness claim to arbitrary category or algebra structures.

The timings include native frontend setup/imports and are not controlled
before/after performance measurements. A phase command's advertised admission
profile is not an independent measurement of its arbitrary subprocess caps. Failed elaborations and successful
leaves have different coverage. Full native run evidence and hash-bound source
manifests were preserved in the research workspace; this complete case retains
the reproduction, failed attempts, accepted proof, conditions and limits.
