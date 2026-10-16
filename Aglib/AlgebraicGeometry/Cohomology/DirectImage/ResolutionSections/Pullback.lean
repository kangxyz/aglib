/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.ExactResolution.Ext
public import Aglib.Algebra.Homology.HomologicalComplex.Adjunction
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Homology.Forget
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Cycles

/-!
# Actual pullback maps between native resolution sections

The original geometric unit gives the section map before scalar extension.
The native scalar adjunction supplies the actual tensor map between the
supplied module-resolution section complexes. Exact geometric pullback
allows the original comparison with the target resolution. Scalar flatness
and quasicoherence are not needed to construct this map or compute its unit.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite CochainComplex HomComplex
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (σ : R →+* S)
  (hσ : p.appTop.hom.comp α = β.comp σ)

/-- The existing section map on the top open, retaining the original top-section comparisons. -/
def moduleGlobalSectionsMapAlong {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) :
    (moduleGlobalSectionsFunctorOfHom X α).obj M ⟶
      (ModuleCat.restrictScalars σ).obj ((moduleGlobalSectionsFunctorOfHom Y β).obj N) :=
  (moduleTopSectionsIso X α M).inv ≫
    (moduleSectionsMapAlong p α β σ hσ φ).app (op ⊤) ≫
      (ModuleCat.restrictScalars σ).map (moduleTopSectionsIso Y β N).hom

/-- The top-section comparison is the original coefficient arrow on the original section. -/
theorem moduleGlobalSectionsMapAlong_apply {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (x : (moduleGlobalSectionsFunctorOfHom X α).obj M) :
    moduleGlobalSectionsMapAlong p α β σ hσ φ x = φ.app ⊤ x := rfl

/-- The actual geometric unit on global sections, natural in the original module coefficient. -/
def moduleGlobalSectionsPullbackMap :
    moduleGlobalSectionsFunctorOfHom X α ⟶ Scheme.Modules.pullback p ⋙
      moduleGlobalSectionsFunctorOfHom Y β ⋙ ModuleCat.restrictScalars σ where
  app M := moduleGlobalSectionsMapAlong p α β σ hσ
    ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)
  naturality {M N} v := by
    ext x
    change (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N).app ⊤)
        (v.app ⊤ x) =
      ((Scheme.Modules.pullback p).map v).app ⊤
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) x)
    exact congrArg (fun q => q.app ⊤ x)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality v)

private theorem unitHomGlobalSectionsEquiv_pullback (P : X.Modules)
    (k : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ P) :
    Scheme.Modules.unitHomGlobalSectionsEquiv Y ((Scheme.Modules.pullback p).obj P)
        ((Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map k) =
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app P).app ⊤)
        (Scheme.Modules.unitHomGlobalSectionsEquiv X P k) := by
  have hu := Scheme.Modules.pullbackUnitIso_homEquiv p
  rw [Adjunction.homEquiv_apply] at hu
  have ht : SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
      (Scheme.Modules.pushforward p).map
        ((Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map k) =
      k ≫ (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app P := by
    rw [← hu]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.naturality k).symm
  have hv := congrArg
    (fun z : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
        (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj P) =>
      Scheme.Modules.Hom.app z ⊤ (1 : Γ(X, ⊤))) ht
  change (((Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map k).app ⊤)
        (p.appTop (1 : Γ(X, ⊤))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app P).app ⊤)
        (Scheme.Modules.unitHomGlobalSectionsEquiv X P k) at hv
  simpa only [map_one, Scheme.Modules.unitHomGlobalSectionsEquiv_apply] using hv

/-- Native standard derived categories are used for the original resolution comparison. -/
local instance resolutionPullbackStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable [Flat p] {M : X.Modules} (I : InjectiveResolution M)
  (J : InjectiveResolution ((Scheme.Modules.pullback p).obj M))

/-- The original geometric unit followed by the original resolution comparison, before
scalar extension. Only geometric pullback is required to be flat. -/
def moduleResolutionPullbackSectionsMap :
    moduleResolutionSectionComplex X α I ⟶
      ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleResolutionSectionComplex Y β J) :=
  (NatTrans.mapHomologicalComplex (moduleGlobalSectionsPullbackMap p α β σ hσ)
      (.up ℤ)).app I.cochainComplex ≫
    ((moduleGlobalSectionsFunctorOfHom Y β ⋙ ModuleCat.restrictScalars σ).mapHomologicalComplex
      (.up ℤ)).map (InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback p) I J)

/-- The actual section-complex map uses the original module unit and original chosen
resolution comparison in every degree. -/
theorem moduleResolutionPullbackSectionsMap_f_apply (i : ℤ)
    (x : (moduleResolutionSectionComplex X α I).X i) :
    (moduleResolutionPullbackSectionsMap p α β σ hσ I J).f i x =
      ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback p) I J).f i).app ⊤
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          (I.cochainComplex.X i)).app ⊤) x) := rfl

/-- The original scalar-adjunction mate is the actual tensor map on the supplied section
complexes; no scalar flatness or quasicoherence is used in its definition. -/
def moduleResolutionPullbackSectionsTensorMap :
    ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj
        (moduleResolutionSectionComplex X α I) ⟶ moduleResolutionSectionComplex Y β J :=
  (((ModuleCat.extendRestrictScalarsAdj σ).mapHomologicalComplex (.up ℤ)).homEquiv _ _).symm
    (moduleResolutionPullbackSectionsMap p α β σ hσ I J)

/-- The complex tensor mate retains the literal native scalar-adjunction unit. -/
theorem moduleResolutionPullbackSectionsTensorMap_unit :
    ((ModuleCat.extendRestrictScalarsAdj σ).mapHomologicalComplex (.up ℤ)).unit.app
        (moduleResolutionSectionComplex X α I) ≫
      ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).map
        (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J) =
      moduleResolutionPullbackSectionsMap p α β σ hσ I J := by
  have h := Equiv.apply_symm_apply
    (((ModuleCat.extendRestrictScalarsAdj σ).mapHomologicalComplex (.up ℤ)).homEquiv _ _)
    (moduleResolutionPullbackSectionsMap p α β σ hσ I J)
  simpa only [Adjunction.homEquiv_apply, moduleResolutionPullbackSectionsTensorMap] using h

/-- Every unit pure tensor has its original geometric-unit and resolution-comparison formula. -/
theorem moduleResolutionPullbackSectionsTensorMap_one_tmul (i : ℤ)
    (x : (moduleResolutionSectionComplex X α I).X i) :
    (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J).f i ((1 : S) ⊗ₜ[R,σ] x) =
      ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback p) I J).f i).app ⊤
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          (I.cochainComplex.X i)).app ⊤) x) := by
  have h := congrArg (fun z => z.f i x)
    (moduleResolutionPullbackSectionsTensorMap_unit p α β σ hσ I J)
  change (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J).f i
      ((1 : S) ⊗ₜ[R,σ] x) =
    (moduleResolutionPullbackSectionsMap p α β σ hσ I J).f i x at h
  exact h.trans (moduleResolutionPullbackSectionsMap_f_apply p α β σ hσ I J i x)

/-- Actual source section cycles map by the original geometric unit and comparison component. -/
def moduleResolutionPullbackSectionCyclesMap (n : ℕ) :
    moduleResolutionSectionCycles X α I n →+ moduleResolutionSectionCycles Y β J n where
  toFun s := ⟨(moduleResolutionPullbackSectionsMap p α β σ hσ I J).f n s.val, by
    let g := moduleResolutionPullbackSectionsMap p α β σ hσ I J
    have h := congrArg
      (fun q : (moduleResolutionSectionComplex X α I).X n ⟶
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj
            (moduleResolutionSectionComplex Y β J)).X ((n : ℤ) + 1) => q s.val)
      (g.comm n ((n : ℤ) + 1))
    change ((moduleResolutionSectionComplex Y β J).d n ((n : ℤ) + 1)) (g.f n s.val) =
      g.f ((n : ℤ) + 1)
        (((moduleResolutionSectionComplex X α I).d n ((n : ℤ) + 1)) s.val) at h
    rw [s.property, map_zero] at h
    exact h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' s t := Subtype.ext
    (((moduleResolutionPullbackSectionsMap p α β σ hσ I J).f n).hom.map_add s.val t.val)

private theorem moduleResolutionPullbackSectionCyclesMap_unitHom (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    (Scheme.Modules.unitHomGlobalSectionsAddEquiv Y (J.cochainComplex.X n)).symm
        (moduleResolutionPullbackSectionCyclesMap p α β σ hσ I J n s).val =
      ((Scheme.Modules.pullbackUnitIso p).inv ≫ (Scheme.Modules.pullback p).map
          ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)).symm s.val)) ≫
        (InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback p) I J).f n := by
  apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv Y (J.cochainComplex.X n)).injective
  rw [AddEquiv.apply_symm_apply]
  change (moduleResolutionPullbackSectionCyclesMap p α β σ hσ I J n s).val =
    Scheme.Modules.unitHomGlobalSectionsEquiv Y (J.cochainComplex.X n) (_ ≫ _)
  rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality,
    unitHomGlobalSectionsEquiv_pullback]
  change (moduleResolutionPullbackSectionsMap p α β σ hσ I J).f n s.val =
    ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback p) I J).f n).app ⊤
      ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
          (I.cochainComplex.X n)).app ⊤)
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n))
          ((Scheme.Modules.unitHomGlobalSectionsAddEquiv X (I.cochainComplex.X n)).symm s.val)))
  rw [AddEquiv.apply_symm_apply]
  exact moduleResolutionPullbackSectionsMap_f_apply p α β σ hσ I J n s.val

/-- The actual target section cocycle is the mapped original cocycle followed by the original
resolution comparison, with original unit-module precomposition. -/
theorem moduleResolutionPullbackSectionCocycle (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    moduleResolutionSectionCocycle Y β J n
        (moduleResolutionPullbackSectionCyclesMap p α β σ hσ I J n s) =
      (InjectiveResolution.mapCochainComparisonCocycle (Scheme.Modules.pullback p) I J
          (moduleResolutionSectionCocycle X α I n s)).precomp
        ((CochainComplex.singleFunctor Y.Modules 0).map
          (Scheme.Modules.pullbackUnitIso p).inv) := by
  let d := InjectiveResolution.mapCochainComparisonCocycle (Scheme.Modules.pullback p) I J
    (moduleResolutionSectionCocycle X α I n s)
  have hpre : Cochain.fromSingleEquiv (zero_add (n : ℤ))
        (d.precomp ((CochainComplex.singleFunctor Y.Modules 0).map
          (Scheme.Modules.pullbackUnitIso p).inv)).1 =
      (Scheme.Modules.pullbackUnitIso p).inv ≫
        Cochain.fromSingleEquiv (zero_add (n : ℤ)) d.1 := by
    obtain ⟨r, hr, he⟩ := Cocycle.fromSingleMk_surjective d
      (n : ℤ) (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl
    rw [← he, ← Cocycle.fromSingleMk_precomp]
    simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
  apply Cocycle.ext
  apply (Cochain.fromSingleEquiv (zero_add (n : ℤ))).injective
  change _ = Cochain.fromSingleEquiv (zero_add (n : ℤ))
    (d.precomp ((CochainComplex.singleFunctor Y.Modules 0).map
      (Scheme.Modules.pullbackUnitIso p).inv)).1
  rw [hpre]
  dsimp only [d]
  rw [InjectiveResolution.mapCochainComparisonCocycle_fromSingleEquiv]
  simp only [moduleResolutionSectionCocycle, Cocycle.fromSingleMk_coe,
    Cochain.fromSingleEquiv_fromSingleMk]
  simpa only [Category.assoc] using
    moduleResolutionPullbackSectionCyclesMap_unitHom p α β σ hσ I J n s

/-- The actual mapped section cycle represents exactly the original geometric cohomology
pullback of the original section class. Only the geometric pullback is required to be flat. -/
theorem moduleResolutionPullbackSectionClass (n : ℕ)
    (s : moduleResolutionSectionCycles X α I n) :
    moduleCohomologyMapAlong (M := M) (N := (Scheme.Modules.pullback p).obj M) p
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n
        (moduleResolutionSectionClass X α I n s) =
      moduleResolutionSectionClass Y β J n
        (moduleResolutionPullbackSectionCyclesMap p α β σ hσ I J n s) := by
  change moduleCohomologyMapAlong p _ n
      (moduleExtCohomologyMap X M n
        (I.extEquivCohomologyClass.symm (.mk (moduleResolutionSectionCocycle X α I n s)))) =
    moduleExtCohomologyMap Y ((Scheme.Modules.pullback p).obj M) n
      (J.extEquivCohomologyClass.symm (.mk (moduleResolutionSectionCocycle Y β J n
        (moduleResolutionPullbackSectionCyclesMap p α β σ hσ I J n s))))
  rw [moduleExtCohomologyMap_pullback,
    InjectiveResolution.mapCochainComparisonCocycle_extClass,
    InjectiveResolution.extEquivCohomologyClass_symm_mk_precomp,
    moduleResolutionPullbackSectionCocycle]

/-- The original canonical homology tensor comparison followed by the actual section map. -/
def moduleResolutionPullbackSectionsHomologyMap (n : ℤ) :
    (ModuleCat.extendScalars σ).obj ((moduleResolutionSectionComplex X α I).homology n) ⟶
      (moduleResolutionSectionComplex Y β J).homology n :=
  extendScalarsHomologyMap σ (moduleResolutionSectionComplex X α I) n ≫
    homologyMap (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J) n

/-- The original cycle map underlying the followed native homology mate. -/
def moduleResolutionPullbackHomologyCyclesMap (n : ℤ) :
    (moduleResolutionSectionComplex X α I).cycles n ⟶
      (ModuleCat.restrictScalars σ).obj ((moduleResolutionSectionComplex Y β J).cycles n) :=
  (ModuleCat.extendRestrictScalarsAdj σ).cyclesUnitMap
    ((moduleResolutionSectionComplex X α I).sc n)
    ((shortComplexFunctor (ModuleCat.{u} S) (.up ℤ) n).map
      (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J))

/-- The native followed homology-cycle map has exactly the original geometric section value. -/
theorem moduleResolutionPullbackHomologyCyclesMap_iCycles (n : ℤ) :
    moduleResolutionPullbackHomologyCyclesMap p α β σ hσ I J n ≫
        (ModuleCat.restrictScalars σ).map
          ((moduleResolutionSectionComplex Y β J).iCycles n) =
      (moduleResolutionSectionComplex X α I).iCycles n ≫
        (moduleResolutionPullbackSectionsMap p α β σ hσ I J).f n := by
  have h := (ModuleCat.extendRestrictScalarsAdj σ).cyclesUnitMap_iCycles
    ((moduleResolutionSectionComplex X α I).sc n)
    ((shortComplexFunctor (ModuleCat.{u} S) (.up ℤ) n).map
      (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J))
  have hu := congrArg (fun z => z.f n)
    (moduleResolutionPullbackSectionsTensorMap_unit p α β σ hσ I J)
  change (ModuleCat.extendRestrictScalarsAdj σ).unit.app
      ((moduleResolutionSectionComplex X α I).X n) ≫
    (ModuleCat.restrictScalars σ).map
      ((moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J).f n) =
    (moduleResolutionPullbackSectionsMap p α β σ hσ I J).f n at hu
  change _ = (moduleResolutionSectionComplex X α I).iCycles n ≫ _ ≫ _ at h
  exact h.trans (congrArg (fun z => (moduleResolutionSectionComplex X α I).iCycles n ≫ z) hu)

/-- The original followed homology mate maps the unit pure tensor of a cycle class to the
original target cycle projection, without scalar flatness. -/
theorem moduleResolutionPullbackSectionsHomologyMap_homologyπ (n : ℤ)
    (c : (moduleResolutionSectionComplex X α I).cycles n) :
    moduleResolutionPullbackSectionsHomologyMap p α β σ hσ I J n
        ((1 : S) ⊗ₜ[R,σ] (moduleResolutionSectionComplex X α I).homologyπ n c) =
      (moduleResolutionSectionComplex Y β J).homologyπ n
        (moduleResolutionPullbackHomologyCyclesMap p α β σ hσ I J n c) := by
  have h := congrArg (fun z => z c)
    ((ModuleCat.extendRestrictScalarsAdj σ).homologyComparison_map_homologyπ
      ((moduleResolutionSectionComplex X α I).sc n)
      ((shortComplexFunctor (ModuleCat.{u} S) (.up ℤ) n).map
        (moduleResolutionPullbackSectionsTensorMap p α β σ hσ I J)))
  exact h

/-- On the unit pure tensor, the actual resolution-section homology map is exactly the
original geometric cohomology pullback under the original resolution-section comparisons.
Neither scalar flatness nor quasicoherence is needed for this normalization. -/
theorem moduleResolutionPullbackSectionsHomologyMap_one_tmul (n : ℕ)
    (x : (moduleResolutionSectionComplex X α I).homology (n : ℤ)) :
    moduleResolutionSectionsCohomologyLinearEquiv Y β J n
        (moduleResolutionPullbackSectionsHomologyMap p α β σ hσ I J n
          ((1 : S) ⊗ₜ[R,σ] x)) =
      moduleCohomologyMapAlong (M := M) (N := (Scheme.Modules.pullback p).obj M) p
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n
        (moduleResolutionSectionsCohomologyLinearEquiv X α I n x) := by
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective
    ((moduleResolutionSectionComplex X α I).homologyπ (n : ℤ))).mp inferInstance) x
  rw [moduleResolutionPullbackSectionsHomologyMap_homologyπ p α β σ hσ I J,
    moduleResolutionSectionsCohomologyLinearEquiv_homologyπ Y β J,
    moduleResolutionSectionsCohomologyLinearEquiv_homologyπ X α I,
    moduleResolutionPullbackSectionClass p α β σ hσ I J]
  apply congrArg (moduleResolutionSectionClass Y β J n)
  apply Subtype.ext
  rw [moduleResolutionSectionCyclesIso_hom_val]
  change (moduleResolutionSectionComplex Y β J).iCycles n
      (moduleResolutionPullbackHomologyCyclesMap p α β σ hσ I J n c) =
    (moduleResolutionPullbackSectionsMap p α β σ hσ I J).f n
      ((moduleResolutionSectionCyclesIso X α I n).hom c).val
  rw [moduleResolutionSectionCyclesIso_hom_val]
  exact congrArg (fun z => z c)
    (moduleResolutionPullbackHomologyCyclesMap_iCycles p α β σ hσ I J n)

end AlgebraicGeometry.Scheme.Cohomology
