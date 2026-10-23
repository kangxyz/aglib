/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Values
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.LocalTrivialization
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConstantFullness
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite

/-! # Actual finite colimits on locally Artinian bases

Common actual etale charts can be restricted to open singleton
neighbourhoods on a locally Artinian base. On a nonempty one-point scheme,
the proved finite-constant fullness theorem lifts every original diagram
arrow to an actual additive value arrow. The original sheaf colimit is then
constant with its finite original value colimit.

This proves finite local constancy and geometric constructibility of
finite colimits under the explicit locally Artinian hypothesis. It does
not assert the corresponding closure on arbitrary qcqs or Noetherian bases.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits

universe u v w

attribute [local instance] hasSheafifyLarge

/-- On a nonempty one-point scheme, the original constant functor is fully
faithful between finite abelian values in the original coefficient universe. -/
theorem constant_map_bijective_of_onePoint (X : Scheme.{u}) [Nonempty X] [Subsingleton X]
    (A B : AddCommGrpCat.{u + 1}) [Finite A] [Finite B] :
    Function.Bijective ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map :
      (A ⟶ B) → _) := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  have : Small.{u} A := Small.mk' ((Fintype.equivFin A).trans (Equiv.ulift.{u}).symm)
  have : Small.{u} B := Small.mk' ((Fintype.equivFin B).trans (Equiv.ulift.{u}).symm)
  let DA := Shrink.{u} A
  let DB := Shrink.{u} B
  have : Finite DA := Finite.of_equiv A (equivShrink A)
  have : Finite DB := Finite.of_equiv B (equivShrink B)
  let a : ConstantFinite.value DA ≅ A :=
    AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := A)))
  let b : ConstantFinite.value DB ≅ B :=
    AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (Shrink.addEquiv (α := B)))
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have h := ConstantFinite.constant_map_bijective X DA DB
  constructor
  · intro f g hfg
    have h' : a.hom ≫ f ≫ b.inv = a.hom ≫ g ≫ b.inv := h.injective (by
      simpa only [Functor.map_comp] using
        congrArg (fun k => C.map a.hom ≫ k ≫ C.map b.inv) hfg)
    calc
      f = a.inv ≫ (a.hom ≫ f ≫ b.inv) ≫ b.hom := by simp
      _ = a.inv ≫ (a.hom ≫ g ≫ b.inv) ≫ b.hom := by rw [h']
      _ = g := by simp
  · intro f
    obtain ⟨g, hg⟩ := h.surjective ((C.mapIso a).hom ≫ f ≫ (C.mapIso b).inv)
    refine ⟨a.inv ≫ g ≫ b.hom, ?_⟩
    simp only [Functor.map_comp, hg, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    simp

section ConstantDiagrams

variable (X : Scheme.{u}) [Nonempty X] [Subsingleton X]
    {J : Type v} [Category.{w} J] (D : J ⥤ AbelianSheaf.{u, u + 1} X)
    (A : J → AddCommGrpCat.{u + 1}) [∀ j, Finite (A j)]
    (e : ∀ j, D.obj j ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A j))

/-- Lift an original coefficient arrow through the proved finite-constant
fullness bijection; no value map is supplied as a premise. -/
def constantValueMap {i j : J} (f : i ⟶ j) : A i ⟶ A j :=
  ((constant_map_bijective_of_onePoint X (A i) (A j)).surjective
    ((e i).inv ≫ D.map f ≫ (e j).hom)).choose

/-- The lifted value map induces exactly the original transported arrow. -/
theorem constantValueMap_fac {i j : J} (f : i ⟶ j) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (constantValueMap X D A e f) = (e i).inv ≫ D.map f ≫ (e j).hom :=
  ((constant_map_bijective_of_onePoint X (A i) (A j)).surjective
    ((e i).inv ≫ D.map f ≫ (e j).hom)).choose_spec

/-- The original transported arrows form an actual diagram of finite
additive values, with all functor laws proved by faithfulness. -/
def constantValueDiagram : J ⥤ AddCommGrpCat.{u + 1} where
  obj := A
  map := constantValueMap X D A e
  map_id j := by
    apply (constant_map_bijective_of_onePoint X (A j) (A j)).injective
    rw [constantValueMap_fac, D.map_id]
    simp
  map_comp f g := by
    apply (constant_map_bijective_of_onePoint X _ _).injective
    rw [(constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map_comp,
      constantValueMap_fac, constantValueMap_fac,
      constantValueMap_fac, D.map_comp]
    simp

/-- The lifted constant-value diagram is naturally isomorphic to the
entire original coefficient diagram, including its original arrows. -/
def constantValueDiagramIso :
    D ≅ constantValueDiagram X D A e ⋙
      constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents e (by
    intro i j f
    change D.map f ≫ (e j).hom = (e i).hom ≫
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (constantValueMap X D A e f)
    rw [constantValueMap_fac]
    simp)

/-- The original sheaf colimit is the constant sheaf of the original
additive value colimit, with no replacement of its coefficient object. -/
def constantValueColimitIso [Finite J] {c : Cocone D} (hc : IsColimit c) :
    c.pt ≅ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Limits.colimit (constantValueDiagram X D A e)) := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : C.IsLeftAdjoint := (constantAdjunction X).isLeftAdjoint
  let : HasColimit D := ⟨c, hc⟩
  exact (colimit.isoColimitCocone ⟨c, hc⟩).symm ≪≫
    HasColimit.isoOfNatIso (constantValueDiagramIso X D A e) ≪≫
      (preservesColimitIso C _).symm

end ConstantDiagrams

/-- On a locally Artinian base, the original colimit of a finite object
family of finite locally constant sheaves is finite locally constant. -/
theorem locallyArtinian_isFiniteLocallyConstant_of_isColimit
    {X : Scheme.{u}} [IsLocallyArtinian X] {J : Type v} [Category.{w} J] [Finite J]
    (D : J ⥤ AbelianSheaf.{u, u + 1} X) {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, IsFiniteLocallyConstant (D.obj j)) : IsFiniteLocallyConstant c.pt := by
  have hx (x : X) : ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧
      ∃ Q : AddCommGrpCat.{u + 1}, Finite Q ∧ Nonempty
        ((inverseImage U.hom).obj c.pt ≅
          (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).obj Q) := by
    obtain ⟨t, y, hy⟩ := exists_etaleFamilyTrivialization D.obj hD x
    have : IsLocallyArtinian t.chart.left :=
      IsLocallyArtinian.of_locallyQuasiFinite (X := t.chart.left) (Y := X) t.chart.hom
    let V : t.chart.left.Opens := ⟨{y}, isOpen_discrete _⟩
    let z : V.toScheme := ⟨y, rfl⟩
    have : Nonempty V.toScheme := ⟨z⟩
    have : Subsingleton V.toScheme := by
      constructor
      intro a b
      exact Subtype.ext (a.property.trans b.property.symm)
    let p := V.ι ≫ t.chart.hom
    let A := t.value
    have : ∀ j, Finite (A j) := t.finite_value
    let e (j : J) : (inverseImage p).obj (D.obj j) ≅
        (constantSheaf V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A j) :=
      (inverseImageComp t.chart.hom V.ι).app (D.obj j) ≪≫
        (inverseImage V.ι).mapIso (t.trivialization j) ≪≫
        (inverseImageConstantIso V.ι).app (A j)
    let E := constantValueDiagram V.toScheme (D ⋙ inverseImage p) A e
    have : ∀ j, Finite (E.obj j) := fun j => by
      change Finite (A j)
      exact t.finite_value j
    have : Finite (Limits.colimit E : AddCommGrpCat.{u + 1}) := finite_colimit E
    refine ⟨Scheme.Etale.mk p, z, hy, Limits.colimit E, inferInstance, ⟨?_⟩⟩
    exact constantValueColimitIso V.toScheme (D ⋙ inverseImage p) A e
      (isColimitOfPreserves (inverseImage p) hc)
  choose U y hy Q hQ e using hx
  exact ⟨{
    index := X
    chart := U
    covers := fun x => ⟨x, y x, hy x⟩
    value := Q
    finite_value := hQ
    trivialization := fun x => (e x).some }⟩

/-- Common actual constructible partitions and the preceding local
construction prove finite-colimit closure on a locally Artinian base. -/
theorem locallyArtinian_isConstructible_of_isColimit
    {X : Scheme.{u}} [IsLocallyArtinian X] {J : Type v} [Category.{w} J] [Finite J]
    (D : J ⥤ AbelianSheaf.{u, u + 1} X) {c : Cocone D} (hc : IsColimit c)
    (hD : ∀ j, IsConstructible (D.obj j)) : IsConstructible c.pt := by
  intro U
  obtain ⟨p, hp⟩ := exists_common_partition_on_affine D.obj hD U
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro j
  have := p.immersion j
  have : IsLocallyArtinian (p.stratum j) :=
    IsLocallyArtinian.of_isImmersion (p.inclusion j)
  exact locallyArtinian_isFiniteLocallyConstant_of_isColimit
    ((D ⋙ inverseImage U.1.ι) ⋙ inverseImage (p.inclusion j))
    (isColimitOfPreserves (inverseImage (p.inclusion j))
      (isColimitOfPreserves (inverseImage U.1.ι) hc)) (fun i => hp i j)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits
