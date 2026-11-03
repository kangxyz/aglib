/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.Cohomology.OpenTransfer.NormalizedScalarRestrictionSquare
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.TopComparison
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.CartesianSquare
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.OpenRestriction

/-! # The original module restriction square and its core laws

Supply original coefficient actions and maps to the complete four-category
Ext scalar construction. No native cohomology groups are rebuilt as input data.
The original scalar actions, adjunction mates and open transports are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original coefficient multiplication as a ring action on the same sheaf. -/
def moduleCoefficientScalarAction (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) : R →+* End (moduleAddSheaf X M) where
  toFun r := moduleScalarOfGlobal X M (α r)
  map_zero' := by rw [α.map_zero]; exact moduleScalarOfGlobal_zero X M
  map_one' := by rw [α.map_one]; exact moduleScalarOfGlobal_one X M
  map_add' a b := by rw [α.map_add]; exact moduleScalarOfGlobal_add X M (α a) (α b)
  map_mul' a b := by rw [α.map_mul]; exact moduleScalarOfGlobal_mul X M (α a) (α b)

/-- The complete Ext construction uses the literal original `Module.compHom`
action on each native open-cohomology group. -/
theorem moduleExtCoefficientModule_eq (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (n : ℕ) (U : X.Opens) :
    (TopCat.Sheaf.openFreeAbelianFunctor X.toTopCat).extCoefficientModule
      (moduleAddSheaf X M) (moduleCoefficientScalarAction X α M) n (op U) =
      moduleHPrimeModuleOfHom X α M n U := rfl

/-- Compatibility is supplied by the original module coefficient pullback,
not added as a new condition on the resulting cohomology square. -/
theorem moduleCoefficientScalarAction_compatible
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (r : R) :
    (TopCat.Sheaf.openCohomologyInverseImage p.base).map
        (moduleCoefficientScalarAction X α M r) ≫ moduleCoefficientPullback p φ =
      moduleCoefficientPullback p φ ≫ moduleCoefficientScalarAction Y β N (σ r) := by
  have hr : p.appTop (α r) = β (σ r) := DFunLike.congr_fun hσ r
  change (zariskiPullback p).map (moduleScalarOfGlobal X M (α r)) ≫
      moduleCoefficientPullback p φ =
    moduleCoefficientPullback p φ ≫ moduleScalarOfGlobal Y N (β (σ r))
  exact (moduleCoefficientPullback_scalar p φ (α r)).trans
    (congrArg (fun z => moduleCoefficientPullback p φ ≫ moduleScalarOfGlobal Y N z) hr)

/-- Construct the complete original module-coefficient square before inserting
actual pullback modules and the cartesian coefficient mate. All coefficient
scalar compatibilities and the original geometric family are produced here. -/
def moduleHPrimeScalarOpenMapCompCongrTopSquare
    {X Y W T : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ T) (p : Y ⟶ X) (j : T ⟶ X)
    (w : a ≫ p = b ≫ j) {M : X.Modules} {N : Y.Modules} {L : T.Modules} {P : W.Modules}
    (φp : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (φa : N ⟶ (Scheme.Modules.pushforward a).obj P)
    (φj : M ⟶ (Scheme.Modules.pushforward j).obj L)
    (φb : L ⟶ (Scheme.Modules.pushforward b).obj P)
    (hφ : φp ≫ (Scheme.Modules.pushforward p).map φa ≫
        (Scheme.Modules.pushforwardComp a p).hom.app P ≫
        (Scheme.Modules.pushforwardCongr w).hom.app P =
      φj ≫ (Scheme.Modules.pushforward j).map φb ≫
        (Scheme.Modules.pushforwardComp b j).hom.app P)
    {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (U : X.Opens) (ha : a ⁻¹ᵁ (p ⁻¹ᵁ U) = ⊤) (hj : j ⁻¹ᵁ U = ⊤) (n : ℕ) :
    Square (ModuleCat.{u + 1} S) := by
  let αT := j.appTop.hom.comp α
  let βW := a.appTop.hom.comp β
  let hs := moduleSectionsOpenSquare_scalars a b p j α β σ hσ w
  exact TopCat.Sheaf.openCohomologyNormalizedScalarRestrictionSquare.{u, u + 1}
    a.base b.base p.base j.base (congrArg (fun f : W ⟶ X => f.base) w)
    (moduleCoefficientPullback p φp) (moduleCoefficientPullback a φa)
    (moduleCoefficientPullback j φj) (moduleCoefficientPullback b φb)
    n σ (moduleCoefficientScalarAction X α M) (moduleCoefficientScalarAction Y β N)
    (moduleCoefficientScalarAction T αT L) (moduleCoefficientScalarAction W βW P)
    (moduleCoefficientScalarAction_compatible p σ α β hσ φp)
    (moduleCoefficientScalarAction_compatible a (RingHom.id S) β βW (by rfl) φa)
    (moduleCoefficientScalarAction_compatible j (RingHom.id R) α αT (by rfl) φj)
    (moduleCoefficientScalarAction_compatible b σ αT βW hs φb)
    U ha hj (additiveOpenTopIsoInteger T) (additiveOpenTopIsoInteger W)
    ((constantPullbackIso b).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)))
    (additiveOpenPullbackIso_top_inv b)
    (moduleHPrimeOpenMap_comp_congr a b p j w φp φa φj φb hφ n)

/-- The tensor square on the four original raw open-cohomology objects. -/
def moduleOpenPullbackExtTensorSquare
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (U : X.Opens) (n : ℕ) : Square (ModuleCat.{u + 1} S) := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let N := (Scheme.Modules.pullback p).obj M
  let P := (Scheme.Modules.pullback b).obj (M.restrict j)
  let ε : N.restrict a ⟶ P :=
    inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
  let φp := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let φa := (Scheme.Modules.restrictAdjunction a).unit.app N ≫
    (Scheme.Modules.pushforward a).map ε
  let φj := (Scheme.Modules.restrictAdjunction j).unit.app M
  let φb := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
  exact moduleHPrimeScalarOpenMapCompCongrTopSquare a b p j h.w φp φa φj φb
    (Scheme.Modules.cartesianPullbackBaseChangeMate_inv_unit_comp a b p j h M)
    σ α β hσ U V.ι_preimage_self U.ι_preimage_self n


/-- The upper edge is precisely the original open tensor mate, not merely an
independently chosen map with the same source and target. -/
theorem moduleOpenPullbackExtTensorSquare_top
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (U : X.Opens) (n : ℕ) :
    (moduleOpenPullbackExtTensorSquare p σ α β hσ M U n).f₁₂ =
      (moduleHPrimeTensorMap p σ α β hσ
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n).app (op U) := by
  let N := (Scheme.Modules.pullback p).obj M
  let φp := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let η := moduleHPrimeRestrictionMap p σ α β hσ φp n
  exact ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).whiskerRight_homEquiv_symm_app
    (moduleHPrimePresheaf X α M n)
    ((Opens.map p.base).op ⋙ moduleHPrimePresheaf Y β N n) η (op U)).symm

/-- The left edge retains the original restriction, preimage transport and top iso. -/
theorem moduleOpenPullbackExtTensorSquare_left
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (U : X.Opens) (n : ℕ) :
    let αU := U.ι.appTop.hom.comp α
    let L := M.restrict U.ι
    let C := moduleHPrimePresheaf U.toScheme αU L n
    let κJ := (eqToHom U.ι_preimage_self.symm).op
    letI := moduleHPrimeModuleOfHom U.toScheme αU L n ⊤
    letI := moduleCohomologyModuleOfHom U.toScheme αU L n
    (moduleOpenPullbackExtTensorSquare p σ α β hσ M U n).f₁₃ =
      (ModuleCat.extendScalars σ).map
        ((moduleHPrimeRestrictionMap U.ι (RingHom.id R) α αU
          (by rfl) ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) n).app (op U) ≫
          (ModuleCat.restrictScalars (RingHom.id R)).map (C.map κJ) ≫
          (ModuleCat.restrictScalars (RingHom.id R)).map
            (moduleHPrimeTopLinearEquivOfHom U.toScheme αU L n).toModuleIso.hom) := rfl

/-- The lower edge is the literal original global tensor mate. -/
theorem moduleHPrimeScalarOpenMap_comp_congr_top_square_bottom
    {X Y W T : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ T) (p : Y ⟶ X) (j : T ⟶ X)
    (w : a ≫ p = b ≫ j) {M : X.Modules} {N : Y.Modules} {L : T.Modules} {P : W.Modules}
    (φp : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (φa : N ⟶ (Scheme.Modules.pushforward a).obj P)
    (φj : M ⟶ (Scheme.Modules.pushforward j).obj L)
    (φb : L ⟶ (Scheme.Modules.pushforward b).obj P)
    (hφ : φp ≫ (Scheme.Modules.pushforward p).map φa ≫
        (Scheme.Modules.pushforwardComp a p).hom.app P ≫
        (Scheme.Modules.pushforwardCongr w).hom.app P =
      φj ≫ (Scheme.Modules.pushforward j).map φb ≫
        (Scheme.Modules.pushforwardComp b j).hom.app P)
    {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (U : X.Opens) (ha : a ⁻¹ᵁ (p ⁻¹ᵁ U) = ⊤) (hj : j ⁻¹ᵁ U = ⊤) (n : ℕ) :
    (moduleHPrimeScalarOpenMapCompCongrTopSquare a b p j w φp φa φj φb hφ
      σ α β hσ U ha hj n).f₃₄ =
      moduleCohomologyTensorMap b σ (j.appTop.hom.comp α) (a.appTop.hom.comp β)
        (moduleSectionsOpenSquare_scalars a b p j α β σ hσ w) φb n := by
  simp only [moduleHPrimeScalarOpenMapCompCongrTopSquare,
    TopCat.Sheaf.openCohomologyNormalizedScalarRestrictionSquare,
    CategoryTheory.Functor.extScalarNormalizedRestrictionSquare_bottom]
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change Sheaf.H.{u + 1} (moduleAddSheaf T L) n at x
  exact (CategoryTheory.Functor.extScalarSourceMate_one_tmul.{u + 1, u, u + 1, u, u, u + 1}
    (zariskiPullback b) σ
    (moduleAddSheaf T L) (moduleAddSheaf W P)
    (moduleCoefficientScalarAction T (j.appTop.hom.comp α) L)
    (moduleCoefficientScalarAction W (a.appTop.hom.comp β) P)
    (moduleCoefficientPullback b φb)
    (moduleCoefficientScalarAction_compatible b σ (j.appTop.hom.comp α)
      (a.appTop.hom.comp β) (moduleSectionsOpenSquare_scalars a b p j α β σ hσ w) φb) n
    ((constantPullbackIso b).inv.app (AddCommGrpCat.of (ULift.{u} ℤ))) x).trans
      (moduleCohomologyTensorMap_one_tmul b σ (j.appTop.hom.comp α) (a.appTop.hom.comp β)
        (moduleSectionsOpenSquare_scalars a b p j α β σ hσ w) φb n x).symm

end AlgebraicGeometry.Scheme.Cohomology
