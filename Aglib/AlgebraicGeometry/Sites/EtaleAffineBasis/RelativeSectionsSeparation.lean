/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.StageSectionsAmalgamation
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.CanonicalSectionGluing
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RelativeChartComparison
/-! # Separation of original sections on actual relative base-change covers -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private theorem native_representative_pull {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y Z B : Over X} (U : X.Etale)
    (e : Z ⟶ Y) (g : Y ⟶ B) (g' : Z ⟶ B)
    (a : Y ⟶ (Etale.forget X).obj U) (a' : Z ⟶ (Etale.forget X).obj U)
    (hg : e ≫ g = g') (ha : e ≫ a = a')
    (s : (pullbackSectionsFunctor F).obj (op B)) (t : F.obj.obj (op U))
    (h : (pullbackSectionsFunctor F).map g.op s = etaleRepresentativeSection F Y U a t) :
    (pullbackSectionsFunctor F).map g'.op s = etaleRepresentativeSection F Z U a' t := by
  have hmap := congrArg (pullbackSectionsFunctor F).map (congrArg Quiver.Hom.op hg)
  have hc := ConcreteCategory.congr_hom ((pullbackSectionsFunctor F).map_comp g.op e.op) s
  have he := congrArg ((pullbackSectionsFunctor F).map e.op) h
  have hr := etaleRepresentativeSection_restrict F e U a t
  have ha' := congrArg (fun q : Z ⟶ (Etale.forget X).obj U ↦
    etaleRepresentativeSection F Z U q t) ha
  exact (ConcreteCategory.congr_hom hmap s).symm.trans
    (hc.trans (he.trans (hr.trans ha')))

private theorem native_restriction_equality_pull {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y Z B : Over X}
    (e : Z ⟶ Y) (g : Y ⟶ B) (g' : Z ⟶ B) (hg : e ≫ g = g')
    (s t : (pullbackSectionsFunctor F).obj (op B))
    (h : (pullbackSectionsFunctor F).map g.op s =
      (pullbackSectionsFunctor F).map g.op t) :
    (pullbackSectionsFunctor F).map g'.op s =
      (pullbackSectionsFunctor F).map g'.op t := by
  have hmap := congrArg (pullbackSectionsFunctor F).map (congrArg Quiver.Hom.op hg)
  have hs := ConcreteCategory.congr_hom ((pullbackSectionsFunctor F).map_comp g.op e.op) s
  have ht := ConcreteCategory.congr_hom ((pullbackSectionsFunctor F).map_comp g.op e.op) t
  exact (ConcreteCategory.congr_hom hmap s).symm.trans
    (hs.trans ((congrArg ((pullbackSectionsFunctor F).map e.op) h).trans
      (ht.symm.trans (ConcreteCategory.congr_hom hmap t))))

/-- Reassociating the actual pullback square transports the original local
restriction equation, without changing the coefficient sheaf. -/
theorem baseChange_section_equation {S T X : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (W : Over S) [Etale W.hom] (U : X.Etale) (a : W.left ⟶ U.left)
    (ha : a ≫ U.hom = W.hom ≫ r) (t : F.obj.obj (op U))
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (τ ≫ r))))
    (h : (pullbackSectionsFunctor F).map
      (Over.homMk (baseChangeEtaleChart τ W).hom
        (U := Over.mk ((baseChangeEtaleChart τ W).hom ≫ (τ ≫ r)))
        (V := Over.mk (τ ≫ r))).op s =
      etaleRepresentativeSection F (Over.mk ((baseChangeEtaleChart τ W).hom ≫ (τ ≫ r)))
        U (unitRepresentativeArrow (τ ≫ r) (baseChangeChartTest τ r W U a ha)) t) :
    (pullbackSectionsFunctor F).map (relativeBaseChangeSource τ r W.hom).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject τ r W.hom) U
        (relativeBaseChangeRepresentative τ r W.hom U a ha) t := by
  exact native_representative_pull F U (relativeToNativeChart τ r W)
    (Over.homMk (baseChangeEtaleChart τ W).hom
      (U := Over.mk ((baseChangeEtaleChart τ W).hom ≫ (τ ≫ r)))
      (V := Over.mk (τ ≫ r)))
    (relativeBaseChangeSource τ r W.hom)
    (unitRepresentativeArrow (τ ≫ r) (baseChangeChartTest τ r W U a ha))
    (relativeBaseChangeRepresentative τ r W.hom U a ha)
    (relativeToNativeChart_source τ r W)
    (relativeToNativeChart_representative τ r W U a ha) s t h

/-- The original relative restrictions to the actual base-changed cover detect equality. -/
theorem relativeBaseChange_sections_ext {S T X : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → Over S) [∀ j, Etale (W j).hom]
    (hcover : ∀ x : S, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (s t : (pullbackSectionsFunctor F).obj (op (Over.mk (τ ≫ r))))
    (h : ∀ j, (pullbackSectionsFunctor F).map
        (relativeBaseChangeSource τ r (W j).hom).op s =
      (pullbackSectionsFunctor F).map (relativeBaseChangeSource τ r (W j).hom).op t) :
    s = t := by
  apply canonicalSections_eq_of_etale_cover (τ ≫ r) F
    (fun j ↦ baseChangeEtaleChart τ (W j)) (baseChangeEtaleChart_covering τ W hcover)
  intro j
  exact native_restriction_equality_pull F (nativeToRelativeChart τ r (W j))
    (relativeBaseChangeSource τ r (W j).hom)
    (Over.homMk (baseChangeEtaleChart τ (W j)).hom
      (U := Over.mk ((baseChangeEtaleChart τ (W j)).hom ≫ (τ ≫ r)))
      (V := Over.mk (τ ≫ r)))
    (nativeToRelativeChart_source τ r (W j)) s t (h j)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
