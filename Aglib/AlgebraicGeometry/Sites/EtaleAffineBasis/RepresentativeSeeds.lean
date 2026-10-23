/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSections

/-! # Original representatives with canonical relative-section endpoint types -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- The original representative at the identity, typed from the start as a value
of the canonical relative-section functor, rather than a reconstructed carrier. -/
def etaleRepresentativeSeed {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (U : X.Etale) (x : F.obj.obj (op U)) :
    (pullbackSectionsFunctor F).obj (op ((Etale.forget X).obj U)) :=
  etaleRepresentativeSection F ((Etale.forget X).obj U) U (𝟙 _) x

/-- Mapping the native identity representative gives the original representative. -/
theorem map_etaleRepresentativeSeed {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (Y : Over X) (U : X.Etale) (a : Y ⟶ (Etale.forget X).obj U)
    (x : F.obj.obj (op U)) :
    (pullbackSectionsFunctor F).map a.op (etaleRepresentativeSeed F U x) =
      etaleRepresentativeSection F Y U a x := by
  exact (etaleRepresentativeSection_restrict F a U (𝟙 _) x).trans
    (congrArg (fun k : Y ⟶ (Etale.forget X).obj U ↦
      etaleRepresentativeSection F Y U k x) (Category.comp_id a))

/-- Equality of mapped native seeds is exactly equality of original representatives. -/
theorem map_etaleRepresentativeSeed_eq_iff {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (Y : Over X) (U V : X.Etale)
    (a : Y ⟶ (Etale.forget X).obj U) (b : Y ⟶ (Etale.forget X).obj V)
    (x : F.obj.obj (op U)) (y : F.obj.obj (op V)) :
    ((pullbackSectionsFunctor F).map a.op (etaleRepresentativeSeed F U x) =
      (pullbackSectionsFunctor F).map b.op (etaleRepresentativeSeed F V y)) ↔
    etaleRepresentativeSection F Y U a x = etaleRepresentativeSection F Y V b y := by
  have hx := map_etaleRepresentativeSeed F Y U a x
  have hy := map_etaleRepresentativeSeed F Y V b y
  exact ⟨fun h ↦ hx.symm.trans (h.trans hy), fun h ↦ hx.trans (h.trans hy.symm)⟩

end AlgebraicGeometry.Scheme.EtaleAffineBasis
