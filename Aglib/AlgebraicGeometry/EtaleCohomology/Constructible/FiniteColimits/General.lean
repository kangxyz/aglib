/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.LocalMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.LocalTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Values
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Actual general finite-diagram constructible colimits

A common actual etale chart trivializes the object family. Finite
intersections of original section-lifting covers make all original arrows
actual value maps on a further chart. Original-unit injectivity proves
the value functor laws; the entire original restricted diagram is
naturally isomorphic to that finite-value diagram.

Preservation of the original colimit and finite values then gives finite
local constancy on arbitrary schemes. Actual common locally closed
partitions give geometric constructible finite-colimit closure. No
Noetherian, connectedness or base quasi-compactness hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits

universe u v w

attribute [local instance] hasSheafifyLarge

/-- The original colimit of a finite diagram of finite locally constant
coefficients is finite locally constant, on every scheme. -/
theorem isFiniteLocallyConstant_of_isColimit {X : Scheme.{u}}
    {J : Type v} [Category.{w} J] [Finite (Arrow J)]
    (D : J ⥤ AbelianSheaf.{u, u + 1} X) {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, IsFiniteLocallyConstant (D.obj j)) : IsFiniteLocallyConstant c.pt := by
  have : Finite J := Finite.of_surjective (fun a : Arrow J => a.left)
    (fun j => ⟨Arrow.mk (𝟙 j), rfl⟩)
  have hx (x : X) : ∃ (V : X.Etale) (z : V.left), V.hom z = x ∧
      ∃ Q : AddCommGrpCat.{u + 1}, Finite Q ∧ Nonempty
        ((inverseImage V.hom).obj c.pt ≅
          (constantSheaf V.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj Q) := by
    obtain ⟨t, y, hy⟩ := exists_etaleFamilyTrivialization D.obj hD x
    let A := t.value
    have : ∀ j, Finite (A j) := t.finite_value
    let D₀ := D ⋙ inverseImage t.chart.hom
    let q (a : Arrow J) :
        (constantSheaf t.chart.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A a.left) ⟶
          (constantSheaf t.chart.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A a.right) :=
      (t.trivialization a.left).inv ≫ D₀.map a.hom ≫ (t.trivialization a.right).hom
    obtain ⟨U, z, hz, g, hg⟩ := exists_etale_valueMaps_at_point t.chart.left
      (fun a : Arrow J => A a.left) (fun a : Arrow J => A a.right) q y
    let R : AbelianSheaf.{u, u + 1} t.chart.left ⥤ AbelianSheaf.{u, u + 1} U.left :=
      etaleRestriction U.hom
    have : PreservesColimitsOfShape J R :=
      preservesColimitsOfShape_of_natIso (inverseImageEtaleIso U.hom)
    let D₁ := D₀ ⋙ R
    let C := constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}
    let b (j : J) : C.obj (A j) ≅ R.obj
        ((constantSheaf t.chart.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A j)) :=
      etaleRestrictionConstantIso U.hom (A j)
    let a (j : J) : D₁.obj j ≅ C.obj (A j) :=
      R.mapIso (t.trivialization j) ≪≫ (b j).symm
    have hg' {i j : J} (f : i ⟶ j) :
        C.map (g (Arrow.mk f)) = (a i).inv ≫ D₁.map f ≫ (a j).hom := by
      have h := congrArg (fun k => k ≫ (b j).inv) (hg (Arrow.mk f))
      change (b i).hom ≫ R.map (q (Arrow.mk f)) ≫ (b j).inv =
        C.map (g (Arrow.mk f)) ≫ (b j).hom ≫ (b j).inv at h
      simp only [Iso.hom_inv_id, Category.comp_id] at h
      simp only [a, D₁, Functor.comp_map, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom,
        Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
      simpa only [q, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Functor.map_comp, Category.assoc] using h.symm
    let E : J ⥤ AddCommGrpCat.{u + 1} := {
      obj := A
      map := fun f => g (Arrow.mk f)
      map_id := by
        intro j
        apply constant_map_injective_at_point U.left (A j) (A j) z
        change C.map (g (Arrow.mk (𝟙 j))) = C.map (𝟙 (A j))
        rw [hg', D₁.map_id, C.map_id]
        simpa only [Category.id_comp] using (a j).inv_hom_id
      map_comp := by
        intro i j k f f'
        apply constant_map_injective_at_point U.left (A i) (A k) z
        rw [C.map_comp, hg', hg', hg', D₁.map_comp]
        simp }
    let e : D₁ ≅ E ⋙ C := NatIso.ofComponents a (by
      intro i j f
      change D₁.map f ≫ (a j).hom = (a i).hom ≫ C.map (g (Arrow.mk f))
      rw [hg']
      simp)
    have : ∀ j, Finite (E.obj j) := fun j => by
      change Finite (A j)
      exact t.finite_value j
    have : Finite (Limits.colimit E : AddCommGrpCat.{u + 1}) := finite_colimit E
    let d := R.mapCocone ((inverseImage t.chart.hom).mapCocone c)
    have hd : IsColimit d :=
      isColimitOfPreserves R (isColimitOfPreserves (inverseImage t.chart.hom) hc)
    let : HasColimit D₁ := ⟨d, hd⟩
    let : C.IsLeftAdjoint := (constantAdjunction U.left).isLeftAdjoint
    let eCol : d.pt ≅ C.obj (Limits.colimit E) :=
      (colimit.isoColimitCocone ⟨d, hd⟩).symm ≪≫ HasColimit.isoOfNatIso e ≪≫
        (preservesColimitIso C E).symm
    let p : U.left ⟶ X := U.hom ≫ t.chart.hom
    let eOriginal : (inverseImage p).obj c.pt ≅ C.obj (Limits.colimit E) :=
      (inverseImageComp t.chart.hom U.hom).app c.pt ≪≫
        (inverseImageEtaleIso U.hom).app ((inverseImage t.chart.hom).obj c.pt) ≪≫ eCol
    refine ⟨Scheme.Etale.mk p, z, ?_, Limits.colimit E, inferInstance, ⟨eOriginal⟩⟩
    change t.chart.hom (U.hom z) = x
    rw [hz, hy]
  choose V z hz Q hQ e using hx
  exact ⟨{
    index := X
    chart := V
    covers := fun x => ⟨x, z x, hz x⟩
    value := Q
    finite_value := hQ
    trivialization := fun x => (e x).some }⟩

/-- Original finite colimits of geometrically constructible coefficients
are geometrically constructible on every scheme. -/
theorem isConstructible_of_isColimit {X : Scheme.{u}}
    {J : Type v} [Category.{w} J] [Finite (Arrow J)]
    (D : J ⥤ AbelianSheaf.{u, u + 1} X) {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, IsConstructible (D.obj j)) : IsConstructible c.pt := by
  have : Finite J := Finite.of_surjective (fun a : Arrow J => a.left)
    (fun j => ⟨Arrow.mk (𝟙 j), rfl⟩)
  intro U
  obtain ⟨p, hp⟩ := exists_common_partition_on_affine D.obj hD U
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro j
  exact isFiniteLocallyConstant_of_isColimit
    ((D ⋙ inverseImage U.1.ι) ⋙ inverseImage (p.inclusion j))
    (isColimitOfPreserves (inverseImage (p.inclusion j))
      (isColimitOfPreserves (inverseImage U.1.ι) hc)) (fun i => hp i j)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits
