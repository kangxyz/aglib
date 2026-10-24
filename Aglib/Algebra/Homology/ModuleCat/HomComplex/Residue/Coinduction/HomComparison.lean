/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Residue.Coinduction
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.Exact
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Derived Hom with the intrinsic residue coefficient line

The original scalar restriction and coinduction adjunction, computed at the
original injective resolution of the base, gives a Hom comparison with arbitrary
derived source. Its inverse is exact restriction followed by the same original
counit in every degree. The own-degree-two reconstruction of derived residue
coinduction then gives the intrinsic line-valued comparison, with the integer
shift `r + 1` on the base side and `r - 1` on the field side.

All shifted source compositions and the original field action are retained.
The latter acts by precomposition on the restricted side. The bounded-below
adapter uses the installed exact-functor comparison, including its native unit
normalization. No coefficient orientation, projectivity of the source,
surjectivity of the base map, or separability hypothesis is used.
-/

@[expose] public noncomputable section

universe u w z

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace ModuleCat

variable (R k : Type u) [CommRing R] [Field k] [Algebra R k]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{z} (ModuleCat.{u} k)]

/-- Original exact restriction on the full derived categories. -/
abbrev residueDerivedRestriction :
    DerivedCategory (ModuleCat.{u} k) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (restrictScalars (algebraMap R k)).mapDerivedCategory

/-- The installed residue coinduction, viewed in the full derived category. -/
abbrev residueDerivedCoefficient : DerivedCategory (ModuleCat.{u} k) :=
  DerivedCategory.Plus.ι.obj (derivedResidueCoinduction R k)

/-- The original base ring in degree zero. -/
abbrev residueBaseSingle : DerivedCategory (ModuleCat.{u} R) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)

/-- The native localization source model; it cancels from the inverse counit formula. -/
def residueSourceIso (M : DerivedCategory (ModuleCat.{u} k)) :
    DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage M) ≅ M :=
  DerivedCategory.Q.objObjPreimageIso M

/-- The same source model after the original exact scalar restriction. -/
def residueRestrictedSourceIso (M : DerivedCategory (ModuleCat.{u} k)) :
    DerivedCategory.Q.obj
        (((restrictScalars (algebraMap R k)).mapHomologicalComplex (.up ℤ)).obj
          (DerivedCategory.Q.objPreimage M)) ≅ (residueDerivedRestriction R k).obj M :=
  ((restrictScalars (algebraMap R k)).mapDerivedCategoryFactors.app
      (DerivedCategory.Q.objPreimage M)).symm ≪≫
    (residueDerivedRestriction R k).mapIso (residueSourceIso k M)

/-- One original resolution counit, before applying any integer shift. -/
def residueDerivedCounit :
    (residueDerivedRestriction R k).obj (residueDerivedCoefficient R k) ⟶
      residueBaseSingle R :=
  (restrictCoextendScalarsAdj (algebraMap R k)).injectiveResolutionDerivedCounit
    (injectiveResolution (ModuleCat.of R R))

/-- The unshifted model comparison is exactly the original installed
resolution comparison, viewed through the native plus/full comparison. -/
theorem residueRightDerivedResolutionIso_eq :
    Adjunction.rightDerivedResolutionIso
        (G := coextendScalars (algebraMap R k))
        (injectiveResolution (ModuleCat.of R R)) =
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} k)).symm.app
          ((coextendScalars (algebraMap R k)).mapCochainComplexPlus.obj
            (injectiveResolution (ModuleCat.of R R)).cochainComplexPlus) ≪≫
        DerivedCategory.Plus.ι.mapIso
          (derivedResidueResolutionIso R k (injectiveResolution (ModuleCat.of R R))) := rfl

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{z} (ModuleCat.{u} k)] in
/-- The same original coinduction counit evaluates every literal functional at one. -/
theorem residueDerivedCounit_component_apply (q : ℤ)
    (φ : (residueCoinductionComplex R k
      (injectiveResolution (ModuleCat.of R R))).X q) :
    ((restrictCoextendScalarsAdj (algebraMap R k)).counit.app
        ((injectiveResolution (ModuleCat.of R R)).cochainComplex.X q)) φ =
      CoextendScalars.equiv (algebraMap R k)
        ((injectiveResolution (ModuleCat.of R R)).cochainComplex.X q) φ (1 : k) :=
  residueCoinductionComplex_counit_apply R k _ q φ

/-- Original derived Hom adjunction at the base resolution, with arbitrary
derived source and no projectivity or K-injectivity premise on that source. -/
def residueDerivedHomEquiv (M : DerivedCategory (ModuleCat.{u} k)) (s : ℤ) :
    ShiftedHom ((residueDerivedRestriction R k).obj M) (residueBaseSingle R) s ≃+
      ShiftedHom M (residueDerivedCoefficient R k) s := by
  let I := injectiveResolution (ModuleCat.of R R)
  let K := DerivedCategory.Q.objPreimage M
  let e₁ := (Linear.homCongr ℤ (residueRestrictedSourceIso R k M).symm
    (Adjunction.resolutionShiftIso I s)).toAddEquiv
  let e₂ := Adjunction.cochainDerivedHomEquivOfInjectiveResolution
    (restrictCoextendScalarsAdj (algebraMap R k)) I s K
  let e₃ := (Linear.homCongr ℤ (residueSourceIso k M)
    (Adjunction.rightDerivedResolutionShiftIso
      (G := coextendScalars (algebraMap R k)) I s)).toAddEquiv
  exact e₁.trans (e₂.trans e₃)

/-- The forward map is the original pointwise derived adjunction between the
two actual resolution comparisons and the native source-model isomorphism. -/
theorem residueDerivedHomEquiv_apply_model
    (M : DerivedCategory (ModuleCat.{u} k)) (s : ℤ)
    (f : ShiftedHom ((residueDerivedRestriction R k).obj M) (residueBaseSingle R) s) :
    residueDerivedHomEquiv R k M s f =
      ((residueSourceIso k M).inv ≫
        Adjunction.cochainDerivedHomEquivOfInjectiveResolution
            (restrictCoextendScalarsAdj (algebraMap R k))
            (injectiveResolution (ModuleCat.of R R)) s (DerivedCategory.Q.objPreimage M)
            (((residueRestrictedSourceIso R k M).hom ≫ f) ≫
              (Adjunction.resolutionShiftIso
                (injectiveResolution (ModuleCat.of R R)) s).hom)) ≫
        (Adjunction.rightDerivedResolutionShiftIso
          (G := coextendScalars (algebraMap R k))
          (injectiveResolution (ModuleCat.of R R)) s).hom := rfl

/-- The inverse retains the original source model, the actual pointwise chain
adjunction, and both native resolution comparisons. -/
theorem residueDerivedHomEquiv_symm_apply_model
    (M : DerivedCategory (ModuleCat.{u} k)) (s : ℤ)
    (g : ShiftedHom M (residueDerivedCoefficient R k) s) :
    (residueDerivedHomEquiv R k M s).symm g =
      (residueRestrictedSourceIso R k M).inv ≫
        (Adjunction.cochainDerivedHomEquivOfInjectiveResolution
            (restrictCoextendScalarsAdj (algebraMap R k))
            (injectiveResolution (ModuleCat.of R R)) s
            (DerivedCategory.Q.objPreimage M)).symm
          ((residueSourceIso k M).hom ≫ g ≫
            (Adjunction.rightDerivedResolutionShiftIso
              (G := coextendScalars (algebraMap R k))
              (injectiveResolution (ModuleCat.of R R)) s).inv) ≫
        (Adjunction.resolutionShiftIso
          (injectiveResolution (ModuleCat.of R R)) s).inv := rfl

/-- Every degree uses exact restriction and the shift of the same original
counit; the chosen source-model isomorphism cancels from this formula. -/
theorem residueDerivedHomEquiv_symm_eq_map_counit
    (M : DerivedCategory (ModuleCat.{u} k)) (s : ℤ)
    (g : ShiftedHom M (residueDerivedCoefficient R k) s) :
    (residueDerivedHomEquiv R k M s).symm g =
      g.map (residueDerivedRestriction R k) ≫ (residueDerivedCounit R k)⟦s⟧' := by
  rw [residueDerivedHomEquiv_symm_apply_model,
    Adjunction.cochainDerivedHomEquivOfInjectiveResolution_symm_eq_map_counit]
  simp only [residueRestrictedSourceIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Iso.app_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id,
    (residueDerivedRestriction R k).map_id M, Category.id_comp]
  rw [Adjunction.injectiveResolutionDerivedCounit_shift
    (restrictCoextendScalarsAdj (algebraMap R k))
    (injectiveResolution (ModuleCat.of R R)) s]
  dsimp only [ShiftedHom.map, residueDerivedRestriction, residueDerivedCoefficient,
    derivedResidueCoinduction, residueDerivedCounit, residueBaseSingle]
  exact (Category.assoc _ _ _).symm

/-- The adjunction respects arbitrary shifted derived-source composition. -/
theorem residueDerivedHomEquiv_symm_comp
    {M M' : DerivedCategory (ModuleCat.{u} k)} {a b c : ℤ}
    (α : ShiftedHom M M' a) (g : ShiftedHom M' (residueDerivedCoefficient R k) b)
    (h : b + a = c) :
    (residueDerivedHomEquiv R k M c).symm (α.comp g h) =
      (α.map (residueDerivedRestriction R k)).comp
        ((residueDerivedHomEquiv R k M' b).symm g) h := by
  simp only [residueDerivedHomEquiv_symm_eq_map_counit, ShiftedHom.map_comp]
  have hn := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) b a c h).inv.naturality
    (residueDerivedCounit R k)
  change ((residueDerivedCounit R k)⟦b⟧')⟦a⟧' ≫ _ =
    _ ≫ (residueDerivedCounit R k)⟦c⟧' at hn
  simpa only [ShiftedHom.comp, Functor.map_comp, Category.assoc] using
    congrArg (fun q => α.map (residueDerivedRestriction R k) ≫
      (g.map (residueDerivedRestriction R k))⟦a⟧' ≫ q) hn.symm

/-- Original exact restriction on bounded-below objects agrees with the native
full-derived restriction through its installed unit-normalized comparison. -/
abbrev residueDerivedRestrictionIso :
    (restrictScalars (algebraMap R k)).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ residueDerivedRestriction R k :=
  (restrictScalars (algebraMap R k)).rightDerivedFunctorPlusCompιIso

/-- The bounded-below restriction comparison retains the original derived unit. -/
theorem residueDerivedRestrictionIso_unit (K : CochainComplex.Plus (ModuleCat.{u} k)) :
    (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).inv.app
        ((restrictScalars (algebraMap R k)).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.ι.map
        ((restrictScalars (algebraMap R k)).rightDerivedFunctorPlusUnit.app K) ≫
      (residueDerivedRestrictionIso R k).hom.app (DerivedCategory.Plus.Q.obj K) =
        DerivedCategory.Q.map
          ((restrictScalars (algebraMap R k)).mapCochainComplexPlusCompι.hom.app K) ≫
        (restrictScalars (algebraMap R k)).mapDerivedCategoryFactors.inv.app K.obj ≫
        (residueDerivedRestriction R k).map
          ((DerivedCategory.Plus.QCompιIso (ModuleCat.{u} k)).inv.app K) :=
  (restrictScalars (algebraMap R k)).rightDerivedFunctorPlusCompιIso_unit K

section Surface

variable [IsRegularLocalRing R] [IsLocalHom (algebraMap R k)] [Module.Finite R k]

/-- The intrinsic line as the original degree-zero single, with its native field action. -/
abbrev residueLineSingle : DerivedCategory (ModuleCat.{u} k) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (derivedResidueCoefficientLine R k)

/-- Shifted own-homology reconstruction, using the original degree-two
normalization and the native single-functor shift. -/
def residueLineShiftIso (hd : ringKrullDim R = (2 : ℕ)) :
    (residueDerivedCoefficient R k)⟦(2 : ℤ)⟧ ≅ residueLineSingle R k :=
  (shiftFunctor (DerivedCategory (ModuleCat.{u} k)) (2 : ℤ)).mapIso
      (DerivedCategory.Plus.ι.mapIso (derivedResidueCoinductionSingleIso R k hd) ≪≫
        (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} k) 2).app
          (derivedResidueCoefficientLine R k)) ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso 2 0 2 (by omega)).app
      (derivedResidueCoefficientLine R k)

/-- The original line-valued finite trace is the adjoint of the inverse
own-homology reconstruction. Its target is the base single shifted by two. -/
def residueLineTrace (hd : ringKrullDim R = (2 : ℕ)) :
    ShiftedHom ((residueDerivedRestriction R k).obj (residueLineSingle R k))
      (residueBaseSingle R) (2 : ℤ) :=
  (residueDerivedHomEquiv R k (residueLineSingle R k) 2).symm
    (residueLineShiftIso R k hd).inv

/-- The intrinsic trace uses the same original counit and exact restriction. -/
theorem residueLineTrace_eq_map_counit (hd : ringKrullDim R = (2 : ℕ)) :
    residueLineTrace R k hd =
      ShiftedHom.map (residueLineShiftIso R k hd).inv (residueDerivedRestriction R k) ≫
        (residueDerivedCounit R k)⟦(2 : ℤ)⟧' :=
  residueDerivedHomEquiv_symm_eq_map_counit R k _ 2 _

/-- The integer ledger from the original degree-two homology to the line target. -/
def residueLineHomTargetIso (hd : ringKrullDim R = (2 : ℕ)) (r : ℤ) :
    (residueDerivedCoefficient R k)⟦r + 1⟧ ≅ (residueLineSingle R k)⟦r - 1⟧ :=
  (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} k)) 2 (r - 1) (r + 1)
      (by omega)).app (residueDerivedCoefficient R k) ≪≫
    (shiftFunctor (DerivedCategory (ModuleCat.{u} k)) (r - 1)).mapIso
      (residueLineShiftIso R k hd)

/-- Original restriction/coinduction followed by the intrinsic own-homology
reconstruction: `R[r+1]` corresponds to the actual `V[r-1]`. -/
def residueLineHomEquiv (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory (ModuleCat.{u} k)) (r : ℤ) :
    ShiftedHom ((residueDerivedRestriction R k).obj M) (residueBaseSingle R) (r + 1) ≃+
      ShiftedHom M (residueLineSingle R k) (r - 1) :=
  (residueDerivedHomEquiv R k M (r + 1)).trans
    (Linear.homCongr ℤ (Iso.refl M) (residueLineHomTargetIso R k hd r)).toAddEquiv

/-- The inverse is the original adjunction applied to the original reconstructed arrow. -/
theorem residueLineHomEquiv_symm_apply (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory (ModuleCat.{u} k)) (r : ℤ)
    (g : ShiftedHom M (residueLineSingle R k) (r - 1)) :
    (residueLineHomEquiv R k hd M r).symm g =
      (residueDerivedHomEquiv R k M (r + 1)).symm
        (g.comp (residueLineShiftIso R k hd).inv (by omega)) := by
  change (residueDerivedHomEquiv R k M (r + 1)).symm
    (𝟙 M ≫ g ≫ (residueLineHomTargetIso R k hd r).inv) = _
  simp only [residueLineHomTargetIso, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    Category.id_comp, ShiftedHom.comp]

/-- Every inverse line comparison is exact restriction followed by the same
degree-two trace, with the native shifted composition. -/
theorem residueLineHomEquiv_symm_eq_trace (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory (ModuleCat.{u} k)) (r : ℤ)
    (g : ShiftedHom M (residueLineSingle R k) (r - 1)) :
    (residueLineHomEquiv R k hd M r).symm g =
      (g.map (residueDerivedRestriction R k)).comp (residueLineTrace R k hd) (by omega) := by
  rw [residueLineHomEquiv_symm_apply]
  exact residueDerivedHomEquiv_symm_comp R k g (residueLineShiftIso R k hd).inv (by omega)

/-- The full integer-graded source law, including the native shift maps. -/
theorem residueLineHomEquiv_symm_comp (hd : ringKrullDim R = (2 : ℕ))
    {M M' : DerivedCategory (ModuleCat.{u} k)} {a r t : ℤ}
    (α : ShiftedHom M M' a) (g : ShiftedHom M' (residueLineSingle R k) (r - 1))
    (h : r + a = t) :
    (residueLineHomEquiv R k hd M t).symm (α.comp g (by omega)) =
      (α.map (residueDerivedRestriction R k)).comp
        ((residueLineHomEquiv R k hd M' r).symm g) (by omega) := by
  rw [residueLineHomEquiv_symm_eq_trace, ShiftedHom.map_comp,
    residueLineHomEquiv_symm_eq_trace]
  exact ShiftedHom.comp_assoc (α.map (residueDerivedRestriction R k))
    (g.map (residueDerivedRestriction R k)) (residueLineTrace R k hd)
    (by omega) (by omega) (by omega)

/-- Forward shifted source naturality, suitable for the original Yoneda action. -/
theorem residueLineHomEquiv_comp (hd : ringKrullDim R = (2 : ℕ))
    {M M' : DerivedCategory (ModuleCat.{u} k)} {a r t : ℤ}
    (α : ShiftedHom M M' a)
    (f : ShiftedHom ((residueDerivedRestriction R k).obj M') (residueBaseSingle R) (r + 1))
    (h : r + a = t) :
    residueLineHomEquiv R k hd M t
        ((α.map (residueDerivedRestriction R k)).comp f (by omega)) =
      α.comp (residueLineHomEquiv R k hd M' r f) (by omega) := by
  apply (residueLineHomEquiv R k hd M t).symm.injective
  rw [AddEquiv.symm_apply_apply, residueLineHomEquiv_symm_comp R k hd α _ h,
    AddEquiv.symm_apply_apply]

/-- Unshifted source naturality applies to every actual derived source arrow,
including the original structural field unit used to evaluate a trace. -/
theorem residueLineHomEquiv_symm_naturality (hd : ringKrullDim R = (2 : ℕ))
    {M M' : DerivedCategory (ModuleCat.{u} k)} (a : M' ⟶ M) (r : ℤ)
    (g : ShiftedHom M (residueLineSingle R k) (r - 1)) :
    (residueLineHomEquiv R k hd M' r).symm (a ≫ g) =
      (residueDerivedRestriction R k).map a ≫ (residueLineHomEquiv R k hd M r).symm g := by
  simp only [residueLineHomEquiv_symm_eq_trace, ShiftedHom.map,
    ShiftedHom.comp, Functor.map_comp, Category.assoc]

/-- Native target-field scalar multiplication becomes precomposition by the
original field scalar endomorphism after exact restriction. -/
theorem residueLineHomEquiv_symm_smul (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory (ModuleCat.{u} k)) (r : ℤ) (a : k)
    (g : ShiftedHom M (residueLineSingle R k) (r - 1)) :
    (residueLineHomEquiv R k hd M r).symm (a • g) =
      (residueDerivedRestriction R k).map (a • 𝟙 M) ≫
        (residueLineHomEquiv R k hd M r).symm g := by
  simpa only [Linear.smul_comp, Category.id_comp] using
    residueLineHomEquiv_symm_naturality R k hd (a • 𝟙 M) r g

/-- The forward comparison has the same intrinsic field-action law. -/
theorem residueLineHomEquiv_precomp_smul (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory (ModuleCat.{u} k)) (r : ℤ) (a : k)
    (f : ShiftedHom ((residueDerivedRestriction R k).obj M) (residueBaseSingle R) (r + 1)) :
    residueLineHomEquiv R k hd M r
        ((residueDerivedRestriction R k).map (a • 𝟙 M) ≫ f) =
      a • residueLineHomEquiv R k hd M r f := by
  apply (residueLineHomEquiv R k hd M r).symm.injective
  rw [AddEquiv.symm_apply_apply, residueLineHomEquiv_symm_smul,
    AddEquiv.symm_apply_apply]

/-- The bounded-below form uses the installed derived restriction itself,
transported through its original exact-functor comparison. -/
def residueLineHomEquivPlus (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory.Plus (ModuleCat.{u} k)) (r : ℤ) :
    ShiftedHom (DerivedCategory.Plus.ι.obj
      ((restrictScalars (algebraMap R k)).rightDerivedFunctorPlus.obj M))
        (residueBaseSingle R) (r + 1) ≃+
      ShiftedHom (DerivedCategory.Plus.ι.obj M) (residueLineSingle R k) (r - 1) :=
  (Linear.homCongr ℤ ((residueDerivedRestrictionIso R k).app M)
    (Iso.refl ((residueBaseSingle R)⟦r + 1⟧))).toAddEquiv |>.trans
      (residueLineHomEquiv R k hd (DerivedCategory.Plus.ι.obj M) r)

/-- The bounded-below inverse retains the original restriction comparison. -/
theorem residueLineHomEquivPlus_symm_apply (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory.Plus (ModuleCat.{u} k)) (r : ℤ)
    (g : ShiftedHom (DerivedCategory.Plus.ι.obj M) (residueLineSingle R k) (r - 1)) :
    (residueLineHomEquivPlus R k hd M r).symm g =
      (residueDerivedRestrictionIso R k).hom.app M ≫
        (residueLineHomEquiv R k hd (DerivedCategory.Plus.ι.obj M) r).symm g := by
  change _ ≫ (_ ≫ 𝟙 _) = _
  simp only [Category.comp_id, Iso.app_hom]
  rfl

/-- Shifted source naturality for the installed bounded-below restriction,
with its original plus/full shift and unit comparisons. -/
theorem residueLineHomEquivPlus_symm_comp (hd : ringKrullDim R = (2 : ℕ))
    {M M' : DerivedCategory.Plus (ModuleCat.{u} k)} {a r t : ℤ}
    (α : ShiftedHom M M' a)
    (g : ShiftedHom (DerivedCategory.Plus.ι.obj M') (residueLineSingle R k) (r - 1))
    (h : r + a = t) :
    (residueLineHomEquivPlus R k hd M t).symm
        ((α.map DerivedCategory.Plus.ι).comp g (by omega)) =
      ((α.map (restrictScalars (algebraMap R k)).rightDerivedFunctorPlus).map
        DerivedCategory.Plus.ι).comp
          ((residueLineHomEquivPlus R k hd M' r).symm g) (by omega) := by
  rw [residueLineHomEquivPlus_symm_apply,
    residueLineHomEquiv_symm_comp R k hd _ _ h, residueLineHomEquivPlus_symm_apply]
  have hβ := ShiftedHom.map_naturality α (residueDerivedRestrictionIso R k).hom
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hβ
  simpa only [ShiftedHom.comp, Functor.map_comp, Category.assoc] using
    congrArg (fun q => q ≫
      ((residueLineHomEquiv R k hd (DerivedCategory.Plus.ι.obj M') r).symm g)⟦a⟧' ≫
        (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} R)) (r + 1) a (t + 1)
          (by omega)).inv.app (residueBaseSingle R)) hβ.symm

/-- The bounded-below comparison preserves native scalar multiplication as
the original scalar endomorphism of the source, followed by derived restriction. -/
theorem residueLineHomEquivPlus_symm_smul (hd : ringKrullDim R = (2 : ℕ))
    (M : DerivedCategory.Plus (ModuleCat.{u} k)) (r : ℤ) (a : k)
    (g : ShiftedHom (DerivedCategory.Plus.ι.obj M) (residueLineSingle R k) (r - 1)) :
    (residueLineHomEquivPlus R k hd M r).symm (a • g) =
      DerivedCategory.Plus.ι.map
          ((restrictScalars (algebraMap R k)).rightDerivedFunctorPlus.map (a • 𝟙 M)) ≫
        (residueLineHomEquivPlus R k hd M r).symm g := by
  rw [residueLineHomEquivPlus_symm_apply, residueLineHomEquiv_symm_smul,
    residueLineHomEquivPlus_symm_apply]
  let J : DerivedCategory.Plus (ModuleCat.{u} k) ⥤ DerivedCategory (ModuleCat.{u} k) :=
    DerivedCategory.Plus.ι
  have hscalar : J.map (a • 𝟙 M) = a • 𝟙 (J.obj M) := by
    calc
      J.map (a • 𝟙 M) = a • J.map (𝟙 M) := J.map_smul a (𝟙 M)
      _ = a • 𝟙 (J.obj M) := congrArg (fun f => a • f) (J.map_id M)
  have hβ := (residueDerivedRestrictionIso R k).hom.naturality (a • 𝟙 M)
  change DerivedCategory.Plus.ι.map
      ((restrictScalars (algebraMap R k)).rightDerivedFunctorPlus.map (a • 𝟙 M)) ≫
      (residueDerivedRestrictionIso R k).hom.app M =
    (residueDerivedRestrictionIso R k).hom.app M ≫
      (residueDerivedRestriction R k).map (J.map (a • 𝟙 M)) at hβ
  rw [hscalar] at hβ
  rw [← Category.assoc, ← hβ, Category.assoc]

end Surface

end ModuleCat
