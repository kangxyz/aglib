/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSectionEquality

/-! # Eventual equality on actual affine-scheme limit diagrams -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private lemma transport_equality
    {X S : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (U V : X.Etale)
    {f f' : S ⟶ X} {a a' : S ⟶ U.left} {b b' : S ⟶ V.left}
    (ha : a ≫ U.hom = f) (hb : b ≫ V.hom = f)
    (ha' : a' ≫ U.hom = f') (hb' : b' ≫ V.hom = f')
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (hf : f = f') (hA : a = a') (hB : b = b')
    (h : etaleRepresentativeSection F (Over.mk f) U (Over.homMk a ha) s =
      etaleRepresentativeSection F (Over.mk f) V (Over.homMk b hb) t) :
    etaleRepresentativeSection F (Over.mk f') U (Over.homMk a' ha') s =
      etaleRepresentativeSection F (Over.mk f') V (Over.homMk b' hb') t := by
  cases hf
  cases hA
  cases hB
  exact h

private lemma equality_precomp {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) {Y Z : Over X} (g : Z ⟶ Y)
    (U V : X.Etale) (a : Y ⟶ (Etale.forget X).obj U)
    (b : Y ⟶ (Etale.forget X).obj V)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : etaleRepresentativeSection F Y U a s = etaleRepresentativeSection F Y V b t) :
    etaleRepresentativeSection F Z U (g ≫ a) s =
      etaleRepresentativeSection F Z V (g ≫ b) t :=
  (etaleRepresentativeSection_restrict F g U a s).symm.trans
    ((congrArg ((pullbackSectionsFunctor F).map g.op) h).trans
      (etaleRepresentativeSection_restrict F g V b t))

private lemma equality_of_iso_values {A B : Ab.{u + 1}} (e : A ≅ B)
    (x y : A) (x' y' : B) (hx : e.hom x = x') (hy : e.hom y = y')
    (h : x' = y') : x = y :=
  (ConcreteCategory.bijective_of_isIso e.hom).injective (hx.trans (h.trans hy.symm))

private lemma equality_isoSpec_iff {X S : Scheme.{u}} [IsAffine S]
    (F : AbelianSheaf.{u, u + 1} X) (U V : X.Etale)
    (r : S ⟶ X) (a : S ⟶ U.left) (b : S ⟶ V.left)
    (ha : a ≫ U.hom = r) (hb : b ≫ V.hom = r)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V)) :
    (etaleRepresentativeSection F (Over.mk r) U (Over.homMk a ha) s =
      etaleRepresentativeSection F (Over.mk r) V (Over.homMk b hb) t) ↔
    (etaleRepresentativeSection F (Over.mk (S.isoSpec.inv ≫ r)) U
        (Over.homMk (S.isoSpec.inv ≫ a) ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ S.isoSpec.inv ≫ z) ha))) s =
      etaleRepresentativeSection F (Over.mk (S.isoSpec.inv ≫ r)) V
        (Over.homMk (S.isoSpec.inv ≫ b) ((Category.assoc _ _ _).trans
          (congrArg (fun z ↦ S.isoSpec.inv ≫ z) hb))) t) := by
  let e : Over.mk (S.isoSpec.inv ≫ r) ≅ Over.mk r := Over.isoMk S.isoSpec.symm rfl
  constructor
  · exact equality_precomp F e.hom U V (Over.homMk a ha) (Over.homMk b hb) s t
  · intro h
    have hU := etaleRepresentativeSection_restrict F e.hom U (Over.homMk a ha) s
    have hV := etaleRepresentativeSection_restrict F e.hom V (Over.homMk b hb) t
    exact equality_of_iso_values ((pullbackSectionsFunctor F).mapIso e.op)
      (etaleRepresentativeSection F (Over.mk r) U (Over.homMk a ha) s)
      (etaleRepresentativeSection F (Over.mk r) V (Over.homMk b hb) t)
      (etaleRepresentativeSection F _ U (e.hom ≫ Over.homMk a ha) s)
      (etaleRepresentativeSection F _ V (e.hom ≫ Over.homMk b hb) t) hU hV h

/-- Eventual equality of original representatives on actual affine schemes.
The ring-colimit reduction uses the original global-section cocone and the
native `isoSpec` naturality squares. -/
theorem exists_affineScheme_representatives_eventually_equal
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)]
    (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (U V : X.Etale)
    (a : D.obj i ⟶ U.left) (b : D.obj i ⟶ V.left)
    (ha : a ≫ U.hom = r) (hb : b ≫ V.hom = r)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : etaleRepresentativeSection F (Over.mk (c.π.app i ≫ r)) U
          (Over.homMk (c.π.app i ≫ a) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ c.π.app i ≫ z) ha))) s =
      etaleRepresentativeSection F (Over.mk (c.π.app i ≫ r)) V
          (Over.homMk (c.π.app i ≫ b) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ c.π.app i ≫ z) hb))) t) :
    ∃ (k : I) (q : k ⟶ i),
      etaleRepresentativeSection F (Over.mk (D.map q ≫ r)) U
          (Over.homMk (D.map q ≫ a) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ D.map q ≫ z) ha))) s =
        etaleRepresentativeSection F (Over.mk (D.map q ≫ r)) V
          (Over.homMk (D.map q ≫ b) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ D.map q ≫ z) hb))) t := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have (j : I) : IsAffine (((Functor.const I).obj c.pt).obj j) :=
    inferInstanceAs (IsAffine c.pt)
  let R := D.op ⋙ Scheme.Γ
  let d := Scheme.Γ.mapCocone c.op
  have hd : IsColimit d := (nonempty_isColimit_Γ_mapCocone D c hc).some
  have hcomp {A : Scheme.{u}} (z : D.obj i ⟶ A) :
      c.pt.isoSpec.inv ≫ (c.π.app i ≫ z) =
        Spec.map (c.π.app i).appTop ≫ ((D.obj i).isoSpec.inv ≫ z) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ z) (Scheme.isoSpec_inv_naturality (c.π.app i)).symm).trans
        (Category.assoc _ _ _))
  have haC : (c.π.app i ≫ a) ≫ U.hom = c.π.app i ≫ r :=
    (Category.assoc _ _ _).trans (congrArg (fun z ↦ c.π.app i ≫ z) ha)
  have hbC : (c.π.app i ≫ b) ≫ V.hom = c.π.app i ≫ r :=
    (Category.assoc _ _ _).trans (congrArg (fun z ↦ c.π.app i ≫ z) hb)
  have hpre := (equality_isoSpec_iff F U V (c.π.app i ≫ r)
    (c.π.app i ≫ a) (c.π.app i ≫ b) haC hbC s t).mp h
  have haR : ((D.obj i).isoSpec.inv ≫ a) ≫ U.hom = (D.obj i).isoSpec.inv ≫ r :=
    (Category.assoc _ _ _).trans (congrArg (fun z ↦ (D.obj i).isoSpec.inv ≫ z) ha)
  have hbR : ((D.obj i).isoSpec.inv ≫ b) ≫ V.hom = (D.obj i).isoSpec.inv ≫ r :=
    (Category.assoc _ _ _).trans (congrArg (fun z ↦ (D.obj i).isoSpec.inv ≫ z) hb)
  have hring := transport_equality F U V
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ c.pt.isoSpec.inv ≫ z) haC))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ c.pt.isoSpec.inv ≫ z) hbC))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ Spec.map (c.π.app i).appTop ≫ z) haR))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ Spec.map (c.π.app i).appTop ≫ z) hbR))
    s t (hcomp r) (hcomp a) (hcomp b) hpre
  obtain ⟨k, q, hk⟩ := exists_affine_representatives_eventually_equal R d hd (op i)
    ((D.obj i).isoSpec.inv ≫ r) F U V ((D.obj i).isoSpec.inv ≫ a)
    ((D.obj i).isoSpec.inv ≫ b) haR hbR s t hring
  have hstage {A : Scheme.{u}} (z : D.obj i ⟶ A) :
      Spec.map (D.map q.unop).appTop ≫ ((D.obj i).isoSpec.inv ≫ z) =
        (D.obj k.unop).isoSpec.inv ≫ (D.map q.unop ≫ z) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ z) (Scheme.isoSpec_inv_naturality (D.map q.unop))).trans
        (Category.assoc _ _ _))
  have hfinal := transport_equality F U V
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ Spec.map (D.map q.unop).appTop ≫ z) haR))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ Spec.map (D.map q.unop).appTop ≫ z) hbR))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (D.obj k.unop).isoSpec.inv ≫ z)
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ D.map q.unop ≫ z) ha))))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ (D.obj k.unop).isoSpec.inv ≫ z)
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ D.map q.unop ≫ z) hb))))
    s t (hstage r) (hstage a) (hstage b) hk
  refine ⟨k.unop, q.unop, ?_⟩
  exact (equality_isoSpec_iff F U V (D.map q.unop ≫ r)
    (D.map q.unop ≫ a) (D.map q.unop ≫ b)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ D.map q.unop ≫ z) ha))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ D.map q.unop ≫ z) hb)) s t).mpr hfinal

end AlgebraicGeometry.Scheme.EtaleAffineBasis
