/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.LocalComponentSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.StrictLocalOpenStalk

/-! # Original global sections as the finite product of actual geometric stalks -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u v

variable (A : Type v) [CommRing A] (R : Type u) [CommRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  [Algebra R A] [Module.Finite R A]

/-- Each component supplies its own native residue field geometric point.
No common imperfect separably closed field is used to index all finite lifts. -/
abbrev localComponentClosedPoint (p : MaximalSpectrum A) :
    (Spec (.of A)).smallEtaleTopology.Point := by
  let := HenselianLocalRing.henselian_localizationAtPrime R A p.asIdeal
  let := HenselianLocalRing.residueField_isSepClosed_localizationAtPrime R A p.asIdeal
  let := localComponentInclusion_isOpenImmersion A R p
  exact openComponentPoint (Localization.AtPrime p.asIdeal) (localComponentInclusion A p)

/-- The literal original component stalk, at the explicitly constructed point. -/
abbrev localComponentStalk (F : AbelianSheaf.{v, v + 1} (Spec (.of A)))
    (p : MaximalSpectrum A) : AddCommGrpCat.{v + 1} :=
  (localComponentClosedPoint A R p).presheafFiber.obj F.obj

/-- The actual restriction group on a local component is its original stalk. -/
def localComponentStalkIso (F : AbelianSheaf.{v, v + 1} (Spec (.of A)))
    (p : MaximalSpectrum A) :
    F.obj.obj (op (localComponentEtale A R p)) ≅ localComponentStalk A R F p := by
  let := HenselianLocalRing.henselian_localizationAtPrime R A p.asIdeal
  let := HenselianLocalRing.residueField_isSepClosed_localizationAtPrime R A p.asIdeal
  let := localComponentInclusion_isOpenImmersion A R p
  let := openComponent_germ_isIso (Localization.AtPrime p.asIdeal)
    (localComponentInclusion A p) F.obj
  exact asIso ((localComponentClosedPoint A R p).toPresheafFiber
    (localComponentEtale A R p)
    (openComponentFiberPoint (Localization.AtPrime p.asIdeal) (localComponentInclusion A p)) F.obj)

/-- Global sections on the entire finite scheme are the product of its actual
geometric stalks, with arbitrary original abelian coefficients. -/
def finiteStalkProductIso (F : AbelianSheaf.{v, v + 1} (Spec (.of A))) :
    (StrictlyLocal.globalSections.{v, v + 1} A).obj F ≅
      ∏ᶜ fun p : MaximalSpectrum A => localComponentStalk A R F p :=
  (localComponentSectionsFanIsLimit A R F).conePointUniqueUpToIso (productIsProduct _) ≪≫
    Limits.Pi.mapIso (localComponentStalkIso A R F)

/-- The original terminal-object field point for a component's geometric stalk. -/
def localComponentTerminalFiberPoint (p : MaximalSpectrum A) :
    (localComponentClosedPoint A R p).fiber.obj (StrictlyLocal.terminalObject A) :=
  Over.homMk (LocalRing.residueSpecMap (Localization.AtPrime p.asIdeal) ≫
    localComponentInclusion A p) (Category.comp_id _)

/-- Every projection of the finite product is exactly the original global germ. -/
@[reassoc (attr := simp)]
lemma finiteStalkProductIso_hom_π (F : AbelianSheaf.{v, v + 1} (Spec (.of A)))
    (p : MaximalSpectrum A) :
    (finiteStalkProductIso A R F).hom ≫
      Pi.π (fun p => localComponentStalk A R F p) p =
        (localComponentClosedPoint A R p).toPresheafFiber
          (StrictlyLocal.terminalObject A) (localComponentTerminalFiberPoint A R p) F.obj := by
  let := HenselianLocalRing.henselian_localizationAtPrime R A p.asIdeal
  let := HenselianLocalRing.residueField_isSepClosed_localizationAtPrime R A p.asIdeal
  let := localComponentInclusion_isOpenImmersion A R p
  change (_ ≫ (Limits.Pi.mapIso (localComponentStalkIso A R F)).hom) ≫ _ = _
  rw [Category.assoc, Limits.Pi.mapIso_hom_π, ← Category.assoc]
  have h := (localComponentSectionsFanIsLimit A R F).conePointUniqueUpToIso_hom_comp
    (productIsProduct _) ⟨p⟩
  exact (congrArg (fun k : F.obj.obj (op (StrictlyLocal.terminalObject A)) ⟶
      F.obj.obj (op (localComponentEtale A R p)) => k ≫ (localComponentStalkIso A R F p).hom)
    h).trans ((localComponentClosedPoint A R p).toPresheafFiber_w
      (localComponentArrow A R p)
      (openComponentFiberPoint (Localization.AtPrime p.asIdeal)
        (localComponentInclusion A p)) F.obj)

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
