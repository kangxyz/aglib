/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.MappedCoverSectionRepresentatives
/-! # Original section representative equations at a fixed geometric boundary -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- The literal original section equation on one base-changed chart. -/
def IsBaseChangeSectionRepresentative {S T X : Scheme.{u}}
    (σ : S ⟶ T) (r : T ⟶ X) (f : S ⟶ X) (hf : σ ≫ r = f)
    (F : AbelianSheaf.{u, u + 1} X) (W : Over T) (U : X.Etale)
    (a : W.left ⟶ U.left) (ha : a ≫ U.hom = W.hom ≫ r)
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk f)))
    (t : F.obj.obj (op U)) : Prop :=
  (pullbackSectionsFunctor F).map (relativeBaseChangeSource σ r W.hom).op
      ((pullbackSectionsFunctor F).map (relativeSourceEquality hf).op s) =
    etaleRepresentativeSection F (relativeBaseChangeObject σ r W.hom) U
      (relativeBaseChangeRepresentative σ r W.hom U a ha) t

/-- Unfold the actual representative equation before specializing its geometry. -/
theorem IsBaseChangeSectionRepresentative.eq {S T X : Scheme.{u}}
    {σ : S ⟶ T} {r : T ⟶ X} {f : S ⟶ X} {hf : σ ≫ r = f}
    {F : AbelianSheaf.{u, u + 1} X} {W : Over T} {U : X.Etale}
    {a : W.left ⟶ U.left} {ha : a ≫ U.hom = W.hom ≫ r}
    {s : (pullbackSectionsFunctor F).obj (op (Over.mk f))}
    {t : F.obj.obj (op U)}
    (h : IsBaseChangeSectionRepresentative σ r f hf F W U a ha s t) :
    (pullbackSectionsFunctor F).map (relativeBaseChangeSource σ r W.hom).op
        ((pullbackSectionsFunctor F).map (relativeSourceEquality hf).op s) =
      etaleRepresentativeSection F (relativeBaseChangeObject σ r W.hom) U
        (relativeBaseChangeRepresentative σ r W.hom U a ha) t := h
end AlgebraicGeometry.Scheme.EtaleAffineBasis
