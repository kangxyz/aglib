/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.OverlapBaseChangeMaps
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSections

/-! # Actual overlap equality supplied by one relative section -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- The actual base-changed scheme, with its original relative structural map. -/
def relativeBaseChangeObject {X S T U : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (f : U ⟶ S) : Over X :=
  Over.mk (pullback.snd τ f ≫ f ≫ r)

/-- The original projection to the relative source. -/
def relativeBaseChangeSource {X S T U : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (f : U ⟶ S) :
    relativeBaseChangeObject τ r f ⟶ Over.mk (τ ≫ r) :=
  Over.homMk (pullback.fst τ f)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z ↦ z ≫ r) pullback.condition).trans (Category.assoc _ _ _)))

/-- An original coefficient representative pulled to the actual base change. -/
def relativeBaseChangeRepresentative {X S T U : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (f : U ⟶ S) (A : X.Etale)
    (a : U ⟶ A.left) (ha : a ≫ A.hom = f ≫ r) :
    relativeBaseChangeObject τ r f ⟶ (Etale.forget X).obj A :=
  Over.homMk (pullback.snd τ f ≫ a)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ pullback.snd τ f ≫ z) ha))

/-- First relative projection from the actual base-changed overlap. -/
def relativeBaseChangeOverlapLeft {X S T U V : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (f : U ⟶ S) (g : V ⟶ S) :
    relativeBaseChangeObject τ r (pullback.fst f g ≫ f) ⟶
      relativeBaseChangeObject τ r f :=
  Over.homMk (overlapBaseChangeLeft τ f g) (by
    change overlapBaseChangeLeft τ f g ≫ (pullback.snd τ f ≫ f ≫ r) =
      pullback.snd τ (pullback.fst f g ≫ f) ≫ (pullback.fst f g ≫ f) ≫ r
    simp only [overlapBaseChangeLeft, pullback.lift_snd_assoc, Category.assoc])

/-- Second relative projection from the actual base-changed overlap. -/
def relativeBaseChangeOverlapRight {X S T U V : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (f : U ⟶ S) (g : V ⟶ S) :
    relativeBaseChangeObject τ r (pullback.fst f g ≫ f) ⟶
      relativeBaseChangeObject τ r g :=
  Over.homMk (overlapBaseChangeRight τ f g) (by
    change overlapBaseChangeRight τ f g ≫ (pullback.snd τ g ≫ g ≫ r) =
      pullback.snd τ (pullback.fst f g ≫ f) ≫ (pullback.fst f g ≫ f) ≫ r
    simp only [overlapBaseChangeRight, pullback.lift_snd_assoc, Category.assoc]
    exact congrArg (fun z ↦ pullback.snd τ (pullback.fst f g ≫ f) ≫ z ≫ r)
      (pullback.condition (f := f) (g := g)).symm)

private theorem overlap_same_source {X S T U V : Scheme.{u}}
    (τ : T ⟶ S) (r : S ⟶ X) (f : U ⟶ S) (g : V ⟶ S) :
    relativeBaseChangeOverlapLeft τ r f g ≫ relativeBaseChangeSource τ r f =
      relativeBaseChangeOverlapRight τ r f g ≫ relativeBaseChangeSource τ r g := by
  apply Over.OverMorphism.ext
  exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm

private theorem common_section_overlap
    {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Ab.{u + 1})
    {Y U V T : C} (a : U ⟶ Y) (b : V ⟶ Y) (p : T ⟶ U) (q : T ⟶ V)
    (h : p ≫ a = q ≫ b) (s : P.obj (op Y))
    (x : P.obj (op U)) (y : P.obj (op V))
    (hx : P.map a.op s = x) (hy : P.map b.op s = y) :
    P.map p.op x = P.map q.op y := by
  have hp := ConcreteCategory.congr_hom (P.map_comp a.op p.op) s
  have hq := ConcreteCategory.congr_hom (P.map_comp b.op q.op) s
  exact (congrArg (P.map p.op) hx).symm.trans
    (hp.symm.trans ((congrArg (fun z ↦ P.map z.op s) h).trans
      (hq.trans (congrArg (P.map q.op) hy))))

/-- Two local original representatives of one section agree on their actual
base-changed overlap. This supplies, rather than assumes, the limit matching
equality used by finite-stage descent. -/
theorem relativeBaseChange_representatives_overlap
    {X S T U V : Scheme.{u}} (τ : T ⟶ S) (r : S ⟶ X)
    (f : U ⟶ S) (g : V ⟶ S) (F : AbelianSheaf.{u, u + 1} X)
    (A B : X.Etale) (a : U ⟶ A.left) (b : V ⟶ B.left)
    (ha : a ≫ A.hom = f ≫ r) (hb : b ≫ B.hom = g ≫ r)
    (x : F.obj.obj (op A)) (y : F.obj.obj (op B))
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (τ ≫ r))))
    (hx : (pullbackSectionsFunctor F).map (relativeBaseChangeSource τ r f).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject τ r f) A
        (relativeBaseChangeRepresentative τ r f A a ha) x)
    (hy : (pullbackSectionsFunctor F).map (relativeBaseChangeSource τ r g).op s =
      etaleRepresentativeSection F (relativeBaseChangeObject τ r g) B
        (relativeBaseChangeRepresentative τ r g B b hb) y) :
    etaleRepresentativeSection F
      (relativeBaseChangeObject τ r (pullback.fst f g ≫ f)) A
      (relativeBaseChangeOverlapLeft τ r f g ≫
        relativeBaseChangeRepresentative τ r f A a ha) x =
    etaleRepresentativeSection F
      (relativeBaseChangeObject τ r (pullback.fst f g ≫ f)) B
      (relativeBaseChangeOverlapRight τ r f g ≫
        relativeBaseChangeRepresentative τ r g B b hb) y := by
  have h := common_section_overlap (pullbackSectionsFunctor F)
    (relativeBaseChangeSource τ r f) (relativeBaseChangeSource τ r g)
    (relativeBaseChangeOverlapLeft τ r f g) (relativeBaseChangeOverlapRight τ r f g)
    (overlap_same_source τ r f g) s _ _ hx hy
  exact (etaleRepresentativeSection_restrict F (relativeBaseChangeOverlapLeft τ r f g) A
      (relativeBaseChangeRepresentative τ r f A a ha) x).symm.trans
    (h.trans (etaleRepresentativeSection_restrict F (relativeBaseChangeOverlapRight τ r f g) B
      (relativeBaseChangeRepresentative τ r g B b hb) y))

end AlgebraicGeometry.Scheme.EtaleAffineBasis
