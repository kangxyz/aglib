/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Arc.MarkedPath
public import Aglib.AlgebraicGeometry.Blowup.RegularPoint.Scheme
public import Aglib.AlgebraicGeometry.Stalk.PrincipalBaseChange

/-!
# Original point blowups over their actual local spectra

The existing universal base-change map retains an arbitrary original blowup
datum. Its native pullback and stalk-arrow comparisons lift an original closed
point and identify its original point-local-ring map with the literal local
blowup stalkScalar. The MarkedPath import supplies only the existing original
pointLocalRingMap; no arc, marking, regularity or completeness is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Blowup.PointLocalization

/-- A closed point of an arbitrary original point blowup lifts to the same
local-spectrum blowup, with both native projections and the exact original
point-local-ring/scalar square. No replacement path or local ring is chosen. -/
theorem exists_closed_point_stalkIso
    {X : Scheme.{u}} (x : X) (hx : IsClosed ({x} : Set X))
    (B : BlowupDatum (X.fromSpecResidueField x).ker)
    (y : B.Y) (hy : IsClosed ({y} : Set B.Y)) (hbase : B.map y = x) :
    let D := Arc.pointBlowup (X.presheaf.stalk x)
    let c := BaseChange.map (X.fromSpecStalk x)
      (RegularPoint.pointCentre_comap_fromSpecStalk X x hx) B D
    let H := BaseChange.isPullback_of_flat (X.fromSpecStalk x)
      (Scheme.fromSpecStalk_flat X x)
      (RegularPoint.pointCentre_comap_fromSpecStalk X x hx) B D
    H.isoPullback.hom ≫ pullback.fst B.map (X.fromSpecStalk x) = c ∧
      H.isoPullback.hom ≫ pullback.snd B.map (X.fromSpecStalk x) = D.map ∧
      ∃ z : D.Y, IsClosed ({z} : Set D.Y) ∧ D.map z = closedPoint (X.presheaf.stalk x) ∧
        ∃ hcy : c z = y, ∃ ε : B.Y.presheaf.stalk y ≅ D.Y.presheaf.stalk z,
          ε.hom = Arc.pointLocalRingMap c z y hcy ∧
          ε.hom.hom.comp (Arc.pointLocalRingMap B.map y x hbase).hom =
            D.map.stalkScalar z := by
  let A := X.presheaf.stalk x
  let D := Arc.pointBlowup A
  let c := BaseChange.map (X.fromSpecStalk x)
    (RegularPoint.pointCentre_comap_fromSpecStalk X x hx) B D
  let H := BaseChange.isPullback_of_flat (X.fromSpecStalk x)
    (Scheme.fromSpecStalk_flat X x)
    (RegularPoint.pointCentre_comap_fromSpecStalk X x hx) B D
  let : Flat (X.fromSpecStalk x) := Scheme.fromSpecStalk_flat X x
  let : IsPreimmersion c :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip inferInstance
  refine ⟨H.isoPullback_hom_fst, H.isoPullback_hom_snd, ?_⟩
  have hcompatible : B.map y = X.fromSpecStalk x (closedPoint A) :=
    hbase.trans (Scheme.fromSpecStalk_closedPoint (X := X) (x := x)).symm
  obtain ⟨p, hp, hp'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := B.map) (g := X.fromSpecStalk x) y (closedPoint A) hcompatible
  let z : D.Y := H.isoPullback.inv p
  have hcy : c z = y :=
    (congrArg (fun f : pullback B.map (X.fromSpecStalk x) ⟶ B.Y => f p)
      H.isoPullback_inv_fst).trans hp
  have hzbase : D.map z = closedPoint A :=
    (congrArg (fun f : pullback B.map (X.fromSpecStalk x) ⟶ Spec (.of A) => f p)
      H.isoPullback_inv_snd).trans hp'
  have hzclosed : IsClosed ({z} : Set D.Y) := by
    have hset : c ⁻¹' ({y} : Set B.Y) = {z} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        exact c.isEmbedding.injective (h.trans hcy.symm)
      · rintro rfl
        exact hcy
    rw [← hset]
    exact hy.preimage c.continuous
  let E : Arrow.mk (B.map.stalkMap y) ≅ Arrow.mk (D.map.stalkMap z) :=
    Scheme.Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion H z y hcy
  let ε : B.Y.presheaf.stalk y ≅ D.Y.presheaf.stalk z := Arrow.rightFunc.mapIso E
  have he : ε.hom = Arc.pointLocalRingMap c z y hcy := rfl
  have hs : Arc.pointLocalRingMap B.map y x hbase ≫ ε.hom =
      CommRingCat.ofHom (D.map.stalkScalar z) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk x)).mp
    calc
      Spec.map (Arc.pointLocalRingMap B.map y x hbase ≫ ε.hom) ≫ X.fromSpecStalk x =
          Spec.map ε.hom ≫ B.Y.fromSpecStalk y ≫ B.map := by
        rw [Spec.map_comp, Category.assoc, Arc.pointLocalRingMap_fromSpecStalk]
      _ = D.Y.fromSpecStalk z ≫ c ≫ B.map := by
        rw [he, ← Category.assoc, Arc.pointLocalRingMap_fromSpecStalk, Category.assoc]
      _ = D.Y.fromSpecStalk z ≫ D.map ≫ X.fromSpecStalk x := by rw [H.w]
      _ = Spec.map (CommRingCat.ofHom (D.map.stalkScalar z)) ≫ X.fromSpecStalk x := by
        rw [← Category.assoc, Scheme.Hom.fromSpecStalk_comp_structure]
  refine ⟨z, hzclosed, hzbase, hcy, ε, he, ?_⟩
  exact congrArg (fun f : X.presheaf.stalk x ⟶ D.Y.presheaf.stalk z => f.hom) hs

end AlgebraicGeometry.Scheme.Blowup.PointLocalization
