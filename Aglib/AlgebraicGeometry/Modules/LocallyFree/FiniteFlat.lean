/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Flat
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite flat direct image of the structure module

For every finite flat locally finitely presented morphism, its actual
structure-sheaf direct image is finite locally free over the original target.
The native local-basis class, actual structure module and morphism properties
are used directly; no new morphism wrapper or rank/degree family is defined.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/FiniteFlatLocallyFree.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`d3dc4d7ca161eb1493165b50730ef4e573da5882fd475b4d4d520c066d42a7fb`. Selected original ranges: [[309,
331], [360, 396], [403, 419]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite Module TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
open BaseChange.Affine (isoRestrictPushforwardComparison)
universe u
variable {X Y : Scheme.{u}}

theorem finiteFlatSpecMap_locallyFree {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [IsFinite (Spec.map φ)] [Flat (Spec.map φ)]
    [LocallyOfFinitePresentation (Spec.map φ)] :
    IsFiniteLocallyFree _ (pushforwardStructureSheaf (Spec.map φ)) := by
  have hfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have hflat : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hfp : φ.hom.FinitePresentation :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  algebraize [φ.hom]
  letI : Module.Finite R S := hfin
  letI : Module.Flat R S := hflat
  letI : Algebra.FinitePresentation R S := hfp
  letI : Module.FinitePresentation R S :=
    Module.FinitePresentation.of_finite_of_finitePresentation R S
  let N : ModuleCat R := ModuleCat.of R S
  let L := (moduleSpecΓFunctor (R := R)).obj (tilde N)
  let e : L ≅ N := (tilde.isoTop N).symm
  letI : Module.FinitePresentation R L := Module.FinitePresentation.of_equiv e.symm.toLinearEquiv
  letI : Module.Flat R L := Module.Flat.of_linearEquiv e.toLinearEquiv
  have h : IsFiniteLocallyFree _ (tilde N) := affineFinitePresentationFlatSheaf_locallyFree _
  letI := h
  exact finiteLocallyFree_of_iso (M := tilde N)
    ((tildePushforwardIso φ).symm.app (ModuleCat.of S S) ≪≫
      (Scheme.Modules.pushforward (Spec.map φ)).mapIso tildeSelf)

/-- The direct-image structure-module comparison induced by the source scheme isomorphism. -/
def pushforwardStructureSourceIso {Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) :
    pushforwardStructureSheaf f ≅ pushforwardStructureSheaf (e.hom ≫ f) := by
  let a := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  haveI : IsIso a := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    change IsIso (((forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat AddCommGrpCat).map (e.hom.app U))
    infer_instance
  exact (Scheme.Modules.pushforward f).mapIso (asIso a) ≪≫
    ((Scheme.Modules.pushforwardComp e.hom f).app _)

theorem finiteFlatToSpec_locallyFree {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    IsFiniteLocallyFree _ (pushforwardStructureSheaf f) := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  let g := X.isoSpec.inv ≫ f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  haveI : IsFinite (Spec.map φ) := hφ.symm ▸ inferInstanceAs (IsFinite g)
  haveI : Flat (Spec.map φ) := hφ.symm ▸ inferInstanceAs (Flat g)
  haveI : LocallyOfFinitePresentation (Spec.map φ) :=
    hφ.symm ▸ inferInstanceAs (LocallyOfFinitePresentation g)
  have h : IsFiniteLocallyFree _ (pushforwardStructureSheaf g) := by
    simpa only [hφ] using finiteFlatSpecMap_locallyFree φ
  letI := h
  refine finiteLocallyFree_of_iso
    (pushforwardStructureSourceIso X.isoSpec g ≪≫ eqToIso ?_)
  congr 1
  simp [g]

theorem finiteFlatAffineTarget_locallyFree (f : X ⟶ Y) [IsAffine Y]
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    IsFiniteLocallyFree _ (pushforwardStructureSheaf f) := by
  apply finiteLocallyFree_of_openImmersionCover (pushforwardStructureSheaf f)
    (fun _ : PUnit.{u + 1} => Spec Γ(Y, ⊤)) (fun _ => Y.isoSpec.inv)
  · intro y
    exact ⟨PUnit.unit, Y.isoSpec.hom y, by simp⟩
  · intro _
    let a : (show Y.Modules from pushforwardStructureSheaf f).restrict Y.isoSpec.inv ≅
        pushforwardStructureSheaf (f ≫ Y.isoSpec.hom) :=
      isoRestrictPushforwardComparison Y.isoSpec.symm _ ≪≫
        ((Scheme.Modules.pushforwardComp f Y.isoSpec.hom).app _)
    haveI := finiteFlatToSpec_locallyFree (f ≫ Y.isoSpec.hom)
    exact finiteLocallyFree_of_iso a.symm

/-- The actual direct image of the structure module of a finite flat finitely
presented morphism has genuine finite local bases over the original target. -/
theorem finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree (f : X ⟶ Y)
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    IsFiniteLocallyFree Y (pushforwardStructureSheaf f) := by
  apply finiteLocallyFree_of_openCover (pushforwardStructureSheaf f)
    (fun U : Y.affineOpens => U.val) (iSup_affineOpens_eq_top Y)
  intro U
  haveI : IsAffine U.val.toScheme := U.property
  let e : (show Y.Modules from pushforwardStructureSheaf f).restrict U.val.ι ≅
      pushforwardStructureSheaf (f ∣_ U.val) :=
    Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardIso f U.val _ ≪≫
      (Scheme.Modules.pushforward (f ∣_ U.val)).mapIso
        (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U.val).ι)
  haveI := finiteFlatAffineTarget_locallyFree (f ∣_ U.val)
  exact finiteLocallyFree_of_iso e.symm

end AlgebraicGeometry.Scheme.Modules
