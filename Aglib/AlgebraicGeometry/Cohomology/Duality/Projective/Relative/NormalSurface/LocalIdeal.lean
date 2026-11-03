/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.StalkEmbedding
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.AffineRow
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.SectionQuotientComparison

/-!
# The same canonical coefficient and its original local numerator ideal

The original global canonical coefficient is pulled back to the original
local spectrum. Its native section/stalk comparison and the ONE accepted
numerator equivalence identify it with the actual affine-centre ideal
module. The original inclusion retains the same section, denominator and
generic-frame values. No canonical coefficient on a new model is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation.AffineRow

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R]
  (ι : Type u) {X : Scheme.{u}} [IsIntegral X]
  (i : X ⟶ ProjectiveSpace R ι) [IsClosedImmersion i]
  [IsDominant (i ≫ toSpec R ι)]
  (hX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hfin : (genericImageBaseMap R ι i).Finite)

/-- The SAME global coefficient pulled to the original local spectrum is the
actual ideal module of its accepted numerator, through the native section iso. -/
def normalSurfaceCanonicalLocalIdealIso (x : X) :
    (pullback (X.fromSpecStalk x)).obj (normalSurfaceCanonicalModule R ι i n) ≅
      Scheme.Hom.idealModule
        (affineCenter (X.presheaf.stalk x)
          (normalSurfaceCanonicalStalkFractionalImage
            R ι i hX hXdim n e hfin x).num).subschemeι := by
  let W := normalSurfaceCanonicalModule R ι i n
  let : W.IsFinitePresentation := normalSurfaceHomology_finitePresentation R ι i n e n
  let N := (pullback (X.fromSpecStalk x)).obj W
  let J := (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num
  let α := stalkFromSpecStalkSectionsIso X x W
  let E := (normalSurfaceCanonicalStalkEquivNum R ι i hX hXdim n e hfin x).toModuleIso
  exact Coherent.affineSheafIsoOfSectionIso N (ModuleCat.of (X.presheaf.stalk x) J)
    (α.symm ≪≫ E) ≪≫ (originalIdealIso J).symm

/-- The actual ideal inclusion has precisely the original section/stalk
comparison followed by the SAME numerator map and original ideal subtype. -/
theorem normalSurfaceCanonicalLocalIdealIso_sections (x : X) :
    moduleSpecΓFunctor.map
        ((normalSurfaceCanonicalLocalIdealIso R ι i hX hXdim n e hfin x).hom ≫
          Scheme.Hom.idealInclusion
            (affineCenter (X.presheaf.stalk x)
              (normalSurfaceCanonicalStalkFractionalImage
                R ι i hX hXdim n e hfin x).num).subschemeι) ≫
      (tilde.toTildeΓNatIso.app
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).inv =
    (stalkFromSpecStalkSectionsIso X x (normalSurfaceCanonicalModule R ι i n)).inv ≫
      (normalSurfaceCanonicalStalkEquivNum R ι i hX hXdim n e hfin x).toModuleIso.hom ≫
        ModuleCat.ofHom
          (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num.subtype := by
  let W := normalSurfaceCanonicalModule R ι i n
  let : W.IsFinitePresentation := normalSurfaceHomology_finitePresentation R ι i n e n
  let N := (pullback (X.fromSpecStalk x)).obj W
  let J := (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).num
  let α := stalkFromSpecStalkSectionsIso X x W
  let E := (normalSurfaceCanonicalStalkEquivNum R ι i hX hXdim n e hfin x).toModuleIso
  let F := Coherent.affineSheafIsoOfSectionIso N (ModuleCat.of (X.presheaf.stalk x) J)
    (α.symm ≪≫ E)
  change moduleSpecΓFunctor.map
      ((F.hom ≫ (originalIdealIso J).inv) ≫
        Scheme.Hom.idealInclusion (affineCenter (X.presheaf.stalk x) J).subschemeι) ≫
      (tilde.toTildeΓNatIso.app
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).inv =
    α.inv ≫ E.hom ≫ ModuleCat.ofHom J.subtype
  have hi : (F.hom ≫ (originalIdealIso J).inv) ≫
      Scheme.Hom.idealInclusion (affineCenter (X.presheaf.stalk x) J).subschemeι =
      F.hom ≫ tilde.map (ModuleCat.ofHom J.subtype) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => F.hom ≫ k) (originalIdealIso_inv_inclusion J))
  have hm := (moduleSpecΓFunctor (R := X.presheaf.stalk x)).map_comp
    F.hom (tilde.map (ModuleCat.ofHom J.subtype))
  have hn := tilde.toTildeΓNatIso.inv.naturality (ModuleCat.ofHom J.subtype)
  change moduleSpecΓFunctor.map (tilde.map (ModuleCat.ofHom J.subtype)) ≫
      (tilde.toTildeΓNatIso.app
        (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).inv =
    (tilde.toTildeΓNatIso.app (ModuleCat.of (X.presheaf.stalk x) J)).inv ≫
      ModuleCat.ofHom J.subtype at hn
  have h := Coherent.affineSheafIsoOfSectionIso_sections N
    (ModuleCat.of (X.presheaf.stalk x) J) (α.symm ≪≫ E)
  let u := (tilde.toTildeΓNatIso.app
    (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).inv
  exact (congrArg (fun k => moduleSpecΓFunctor.map k ≫ u) hi).trans
    ((congrArg (fun k => k ≫ u) hm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => moduleSpecΓFunctor.map F.hom ≫ k) hn).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun k => k ≫ ModuleCat.ofHom J.subtype) h).trans
              (Category.assoc _ _ _))))))

/-- On every original stalk element, the actual included local section has
the accepted denominator times its value in the ONE original generic frame. -/
theorem normalSurfaceCanonicalLocalIdealIso_algebraMap (x : X)
    (m : (moduleStalk X x).obj (normalSurfaceCanonicalModule R ι i n)) :
    algebraMap (X.presheaf.stalk x) X.functionField
      ((tilde.toTildeΓNatIso.app
          (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).inv
        (moduleSpecΓFunctor.map
          ((normalSurfaceCanonicalLocalIdealIso R ι i hX hXdim n e hfin x).hom ≫
            Scheme.Hom.idealInclusion
              (affineCenter (X.presheaf.stalk x)
                (normalSurfaceCanonicalStalkFractionalImage
                  R ι i hX hXdim n e hfin x).num).subschemeι)
          ((stalkFromSpecStalkSectionsIso X x
            (normalSurfaceCanonicalModule R ι i n)).hom m))) =
      (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).den •
        normalSurfaceCanonicalStalkEmbedding R ι i hX hXdim n e hfin x m := by
  have h := ConcreteCategory.congr_hom
    (normalSurfaceCanonicalLocalIdealIso_sections R ι i hX hXdim n e hfin x)
    ((stalkFromSpecStalkSectionsIso X x (normalSurfaceCanonicalModule R ι i n)).hom m)
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at h
  exact (congrArg (algebraMap (X.presheaf.stalk x) X.functionField) h).trans
    (normalSurfaceCanonicalStalkEquivNum_algebraMap R ι i hX hXdim n e hfin x m)

/-- The same actual included section retains the original neighbourhood germ
and the same global generic-frame value, with the original denominator. -/
theorem normalSurfaceCanonicalLocalIdealIso_germ (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(normalSurfaceCanonicalModule R ι i n, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField
      ((tilde.toTildeΓNatIso.app
          (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))).inv
        (moduleSpecΓFunctor.map
          ((normalSurfaceCanonicalLocalIdealIso R ι i hX hXdim n e hfin x).hom ≫
            Scheme.Hom.idealInclusion
              (affineCenter (X.presheaf.stalk x)
                (normalSurfaceCanonicalStalkFractionalImage
                  R ι i hX hXdim n e hfin x).num).subschemeι)
          ((stalkFromSpecStalkSectionsIso X x
            (normalSurfaceCanonicalModule R ι i n)).hom
              ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U x hx s)))) =
      (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).den •
        normalSurfaceCanonicalGenericFrame R ι i hX hXdim n e hfin
          ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U (genericPoint X)
            ((genericPoint_specializes x).mem_open U.isOpen hx) s) := by
  exact (normalSurfaceCanonicalLocalIdealIso_algebraMap R ι i hX hXdim n e hfin x
    ((normalSurfaceCanonicalModule R ι i n).presheaf.germ U x hx s)).trans
      (congrArg (fun z : X.functionField =>
        (normalSurfaceCanonicalStalkFractionalImage R ι i hX hXdim n e hfin x).den • z)
        (normalSurfaceCanonicalStalkEmbedding_germ R ι i hX hXdim n e hfin x U hx s))

end AlgebraicGeometry.Scheme.Cohomology
