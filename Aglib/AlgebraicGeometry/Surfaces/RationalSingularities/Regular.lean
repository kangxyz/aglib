/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Blowup.RegularPoint
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalFirstCohomology
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.AlgebraicGeometry.Surfaces.Birational.CommonDomination
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Aglib.RingTheory.RegularLocalRing.Normal

/-!
# Regular local surfaces and pre-resolution rationality

The universal vanishing predicate refers to the original structure module
on every supplied normal proper birational model. For a regular local
surface, actual point-blowup common domination constructs a regular
dominating source. Exactness of the original degree-one Leray complex and
regular-point higher-image vanishing make its H1 zero. The original
proper-birational H1 injection then gives vanishing on the supplied model.

No general surface resolution, projectivity of the supplied model, Nagata
or completeness premise is used. The rational-singularity terminology in
Stacks Definition 54.8.3 has its additional Nagata domain of definition;
the predicate here records the broader universal vanishing property.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Cohomology AlgebraicGeometry.Scheme.Blowup

namespace AlgebraicGeometry.Scheme.RationalSingularities

universe u

/-- The standard derived category of module sheaves for point-chain cohomology. -/
local instance regularRationalSource (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The standard derived category of `R`-modules for regular-local first cohomology. -/
local instance regularRationalTarget (R : Type u) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

/-- Universal original structure-H1 vanishing on actual normal proper
birational models. This bootstrap property does not assert Nagata. -/
public def NormalModificationH1Vanishing
    (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y]
    (f : Y ⟶ Spec (.of A)) [IsProper f] [IsDominant f],
    NormalStalks Y → IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) →
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf)) 1)

private theorem normalStalks_of_regularStalks {X : Scheme.{u}}
    (hX : RegularStalks X) : NormalStalks X := by
  intro x
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

private theorem functionFieldMap_congr
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {f g : X ⟶ Y} [IsDominant f] [IsDominant g] (h : f = g) :
    Scheme.functionFieldMap f = Scheme.functionFieldMap g := by
  subst g
  rfl

/-- A regular point step preserves structure-H1 vanishing, using only
middle exactness and its actual zero first higher direct image. -/
private theorem regularPoint_structureH1_vanishing
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (hX : RegularStalks X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hd : ringKrullDim (X.presheaf.stalk x) = 2)
    (hH : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1)) :
    Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf (blowupDatum (X.fromSpecResidueField x).ker).Y
        (SheafOfModules.unit
          (blowupDatum (X.fromSpecResidueField x).ker).Y.ringCatSheaf)) 1) := by
  let B := blowupDatum (X.fromSpecResidueField x).ker
  let c : PointBlowupChain B.map := by
    simpa only [Category.id_comp] using
      (PointBlowupChain.cons x hx hd (𝟙 B.Y) (PointBlowupChain.refl B.Y))
  let : IsIntegral B.Y := c.isIntegral inferInstance
  let : IsDominant B.map := c.isDominant inferInstance
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  have hff := c.functionFieldMap_isIso inferInstance
  have hnormal := normalStalks_of_regularStalks hX
  let α : Γ(X, ⊤) →+* Γ(X, ⊤) := RingHom.id _
  let T := moduleBirationalLerayTriangle X α B.map hnormal hff
  let S := moduleBirationalLerayShortComplex X α B.map hnormal hff
  have hS : S.Exact :=
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) 0).homologySequence_exact₂
      T (moduleBirationalLerayTriangle_distinguished X α B.map hnormal hff) 1
  let e₁ : S.X₁ ≃ Sheaf.H.{u + 1}
      (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1 :=
    (moduleBirationalLeraySourceEquiv X α B.map hnormal hff).toEquiv
  have h₁ : IsZero S.X₁ := ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun a b => e₁.injective (@Subsingleton.elim _ hH _ _)⟩
  have hR : IsZero (((Scheme.Modules.pushforward B.map).rightDerived 1).obj
      (SheafOfModules.unit B.Y.ringCatSheaf)) :=
    isZero_higherDirectImage_structure_of_regular_point X hX x hx hd 1 (by decide)
  have hΓ : IsZero ((moduleGlobalSectionsFunctorOfHom X α).obj
      (((Scheme.Modules.pushforward B.map).rightDerived 1).obj
        (SheafOfModules.unit B.Y.ringCatSheaf))) :=
    (moduleGlobalSectionsFunctorOfHom X α).map_isZero hR
  have h₃ : IsZero S.X₃ :=
    hΓ.of_iso (moduleBirationalLerayEdgeIso X α B.map hnormal hff)
  have h₂ : IsZero S.X₂ := hS.isZero_of_both_isZero h₁ h₃
  let e₂ : S.X₂ ≃ Sheaf.H.{u + 1}
      (moduleAddSheaf B.Y (SheafOfModules.unit B.Y.ringCatSheaf)) 1 :=
    (moduleBirationalLerayMiddleEquiv X α B.map hnormal hff).toEquiv
  have hs₂ : Subsingleton S.X₂ := ModuleCat.isZero_iff_subsingleton.mp h₂
  exact ⟨fun a b => e₂.symm.injective (@Subsingleton.elim _ hs₂ _ _)⟩

/-- Induct over the literal original point chain, carrying only H1
vanishing, regularity and the original locally Noetherian source data. -/
private theorem pointChain_structureH1_vanishing
    {X Y : Scheme.{u}} {f : Y ⟶ X} (c : PointBlowupChain f) :
    IsIntegral X → IsLocallyNoetherian X → RegularStalks X →
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) →
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf)) 1) := by
  induction c with
  | refl X => intro _ _ _ hH; exact hH
  | @cons X Y x hx hd g tail ih =>
    intro hI hN hX hH
    let : IsIntegral X := hI
    let : IsLocallyNoetherian X := hN
    let B := blowupDatum (X.fromSpecResidueField x).ker
    let c₀ : PointBlowupChain B.map := by
      simpa only [Category.id_comp] using
        (PointBlowupChain.cons x hx hd (𝟙 B.Y) (PointBlowupChain.refl B.Y))
    let : IsIntegral B.Y := c₀.isIntegral hI
    let : IsLocallyNoetherian B.Y := B.isLocallyNoetherian
    exact ih inferInstance inferInstance
      (Blowup.RegularPoint.regularStalks_pointBlowup X hX x hx hd)
      (regularPoint_structureH1_vanishing X hX x hx hd hH)

/-- A regular local surface has universal original structure-H1 vanishing
on every supplied normal proper birational model, before any general
resolution theorem. The domain instance is derived from regularity. -/
public theorem normalModificationH1Vanishing_of_regularLocal
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hd : ringKrullDim A = 2) :
    letI : IsDomain A := IsRegularLocalRing.isDomain_of_regularLocal A
    NormalModificationH1Vanishing A := by
  let : IsDomain A := IsRegularLocalRing.isDomain_of_regularLocal A
  let : IsRegularRing A := IsRegularLocalRing.isRegularRing_of_regularLocal A
  let S := Spec (.of A)
  have hS : RegularStalks S := regularStalks_spec A
  have hdim : topologicalKrullDim S ≤ 2 := by
    change topologicalKrullDim (PrimeSpectrum A) ≤ 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hd.le
  intro Y hY f hproper hdom hnormal hff
  let : IsIntegral Y := hY
  let : IsProper f := hproper
  let : IsDominant f := hdom
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := hff
  let e := asIso (CommRingCat.ofHom (Scheme.functionFieldMap f))
  let gη := Spec.map e.inv ≫ Y.fromSpecStalk (genericPoint Y)
  let : IsDominant gη := by dsimp only [gη]; infer_instance
  have hinv : Spec.map e.inv ≫ Spec.map e.hom = 𝟙 (Spec S.functionField) := by
    calc
      _ = Spec.map (e.hom ≫ e.inv) := (Spec.map_comp e.hom e.inv).symm
      _ = Spec.map (𝟙 (CommRingCat.of S.functionField)) :=
        congrArg Spec.map e.hom_inv_id
      _ = 𝟙 (Spec (CommRingCat.of S.functionField)) := by simp
      _ = _ := rfl
  have hnat : Y.fromSpecStalk (genericPoint Y) ≫ f =
      Spec.map e.hom ≫ S.fromSpecStalk (genericPoint S) :=
    Scheme.fromSpecStalk_genericPoint_naturality f
  have hgη : gη ≫ f = S.fromSpecStalk (genericPoint S) := by
    dsimp only [gη]
    rw [Category.assoc, hnat, ← Category.assoc, hinv]
    exact Category.id_comp (S.fromSpecStalk (genericPoint S))
  obtain ⟨Z, β, c, h, j, hpβ, hbir, hNZ, hregZ, hdimZ, hhproper, hsurj,
      hbase, hgeneric, hjβ, hjh⟩ :=
    CommonDomination.exists_proper_pointBlowupChain_commonDomination A hS hdim
      (𝟙 S) f gη (by simpa only [Category.comp_id] using hgη)
  let : IsIntegral Z := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  let : IsProper h := hhproper
  let : Surjective h := hsurj
  let : IsDominant h := inferInstance
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)) :=
    c.functionFieldMap_isIso inferInstance
  have htriangle : h ≫ f = β := hbase.trans (Category.comp_id β)
  have hmap : (Scheme.functionFieldMap h).comp (Scheme.functionFieldMap f) =
      Scheme.functionFieldMap β :=
    (Scheme.functionFieldMap_comp h f).symm.trans (functionFieldMap_congr htriangle)
  have hcomp : CommRingCat.ofHom (Scheme.functionFieldMap f) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap h) =
        CommRingCat.ofHom (Scheme.functionFieldMap β) := by
    rw [← CommRingCat.ofHom_comp, hmap]
  let : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f) ≫
      CommRingCat.ofHom (Scheme.functionFieldMap h)) := by
    rw [hcomp]
    infer_instance
  have hffh : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap h)) :=
    IsIso.of_isIso_comp_left (CommRingCat.ofHom (Scheme.functionFieldMap f)) _
  let : (SheafOfModules.unit S.ringCatSheaf).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_unit S
  have hS₁ : Subsingleton (Sheaf.H.{u + 1}
      (moduleAddSheaf S (SheafOfModules.unit S.ringCatSheaf)) 1) :=
    subsingleton_moduleAddSheafH_of_isAffine (X := S)
      (SheafOfModules.unit S.ringCatSheaf) 0
  have hZ₁ := pointChain_structureH1_vanishing c inferInstance inferInstance hS hS₁
  have hinj := moduleCohomologyMapAlongLinear_unit_injective_of_isProper_birational
    Y (RingHom.id Γ(Y, ⊤)) h hnormal hffh
  exact ⟨fun a b => hinj (@Subsingleton.elim _ hZ₁ _ _)⟩

end AlgebraicGeometry.Scheme.RationalSingularities
