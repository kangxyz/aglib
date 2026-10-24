/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.TriangleCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-! # Original Kummer classes as fixed-coefficient family values

The comparison retains the original roots pullback isomorphism and the
original section pullback. Only the receiving scheme needs a geometric
Galois-category point; the parameter family need not be connected.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleCohomology.PointedNaturality
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} {D : Type u} [Field D] [IsSepClosed D]
  (z : Spec (.of D) ⟶ X)
  [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite z)]

include z

/-- The original roots coefficient map at the identity is the native unit
comparison, proved from the actual composition law. -/
theorem rootsPullbackIso_identity (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (rootsPullbackIso (𝟙 X) n hn hinv).hom = (inverseImageId X).hom.app (mu X n) := by
  let : (inverseImage (𝟙 X)).Faithful := Functor.Faithful.of_iso (inverseImageId X).symm
  apply (inverseImage (𝟙 X)).map_injective
  apply (cancel_epi ((inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n))).mp
  have hc := TriangleCoherence.rootsPullbackIso_comp (𝟙 X) (𝟙 X) z n hn hinv
  have hg := TriangleCoherence.rootsPullbackIso_congr (Category.comp_id (𝟙 X)) n hn hinv
  have hu := congrArg (fun e => e.hom.app (mu X n)) (inverseImageComp_id_comp (𝟙 X))
  have hh : (inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n) ≫
      (inverseImage (𝟙 X)).map (rootsPullbackIso (𝟙 X) n hn hinv).hom =
      (eqToIso (congrArg (fun f => (inverseImage f).obj (mu X n))
        (Category.comp_id (𝟙 X)))).hom := by
    apply (cancel_mono (rootsPullbackIso (𝟙 X) n hn hinv).hom).mp
    simpa only [Category.assoc] using hc.trans hg.symm
  rw [hh]
  simp only [Iso.trans_hom, NatTrans.comp_app, CategoryTheory.Functor.isoWhiskerRight_hom,
    CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.leftUnitor_hom_app,
    eqToIso.hom, eqToHom_app] at hu
  change (inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n) ≫
    (inverseImage (𝟙 X)).map ((inverseImageId X).hom.app (mu X n)) ≫
      𝟙 ((inverseImage (𝟙 X)).obj (mu X n)) = eqToHom _ at hu
  let m := (inverseImage (𝟙 X)).map ((inverseImageId X).hom.app (mu X n))
  exact hu.symm.trans (congrArg
    (fun k : (inverseImage (𝟙 X)).obj ((inverseImage (𝟙 X)).obj (mu X n)) ⟶
        (inverseImage (𝟙 X)).obj (mu X n) =>
      (inverseImageComp (𝟙 X) (𝟙 X)).hom.app (mu X n) ≫ k)
    (Category.comp_id m))

/-- The literal roots coefficient maps contract along an actual section. -/
theorem roots_section_coefficients {Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImage a).map (rootsPullbackIso r n hn hinv).hom ≫
        (rootsPullbackIso a n hn (levelInvertible r n hinv)).hom =
      (sectionCoefficientIso r a ha (mu X n)).hom := by
  apply (cancel_epi ((inverseImageComp r a).hom.app (mu X n))).mp
  rw [TriangleCoherence.rootsPullbackIso_comp r a z]
  rw [← TriangleCoherence.rootsPullbackIso_congr ha n hn hinv,
    rootsPullbackIso_identity z]
  simp [sectionCoefficientIso]

/-- Pulling a Kummer family class to the fixed roots coefficient and then to
an actual section is exactly the original Kummer cohomology pullback. -/
theorem sectionPullback_roots {Y : Scheme.{u}} (r : Y ⟶ X) (a : X ⟶ Y)
    (ha : a ≫ r = 𝟙 X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} Y)]
    (c : H1Etale.{u, u + 1, w'} Y (mu Y n)) :
    sectionPullback r a ha (mu X n)
        (coefficientMap (rootsPullbackIso r n hn hinv).inv c) =
      Kummer.rootsCohomologyPullback a n hn (levelInvertible r n hinv) 1 c := by
  change coefficientMap (sectionCoefficientIso r a ha (mu X n)).hom
      (h1Pullback a _ (coefficientMap (rootsPullbackIso r n hn hinv).inv c)) =
    coefficientMap (rootsPullbackIso a n hn (levelInvertible r n hinv)).hom
      (h1Pullback a (mu Y n) c)
  rw [h1Pullback_coefficientMap, ← AddMonoidHom.comp_apply, ← coefficientMap_comp]
  congr 1
  rw [← roots_section_coefficients z r a ha n hn hinv, ← Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

end AlgebraicGeometry.Scheme.EtaleCohomology.KummerFamilyValues
