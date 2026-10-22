/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.DiagramGluing

/-! # Original diagram maps under successive open restrictions -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
universe u v w
variable {X U V : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- Change only the target functor coordinates using the specified natural iso. -/
def diagramHomTransport {D : Type*} [Category D]
    {R S : X.Modules ⥤ D} (e : R ≅ S) {F G : C ⥤ X.Modules}
    (q : F ⋙ S ⟶ G ⋙ S) : F ⋙ R ⟶ G ⋙ R :=
  (Functor.isoWhiskerLeft F e).hom ≫ q ≫ (Functor.isoWhiskerLeft G e).inv

/-- Opposite native coordinate transports cancel without changing an arrow. -/
theorem diagramHomTransport_symm {D : Type*} [Category D]
    {R S : X.Modules ⥤ D} (e : R ≅ S) {F G : C ⥤ X.Modules}
    (q : F ⋙ R ⟶ G ⋙ R) :
    diagramHomTransport e (diagramHomTransport e.symm q) = q := by
  apply NatTrans.ext
  funext c
  change e.hom.app (F.obj c) ≫
    (e.inv.app (F.obj c) ≫ q.app c ≫ e.hom.app (G.obj c)) ≫ e.inv.app (G.obj c) = _
  simp only [Category.assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  exact Category.comp_id _

/-- The specified coordinate transport is injective on actual arrows. -/
theorem diagramHomTransport_injective {D : Type*} [Category D]
    {R S : X.Modules ⥤ D} (e : R ≅ S) {F G : C ⥤ X.Modules}
    (q r : F ⋙ S ⟶ G ⋙ S) (h : diagramHomTransport e q = diagramHomTransport e r) :
    q = r := by
  apply (cancel_epi (Functor.isoWhiskerLeft F e).hom).mp
  apply (cancel_mono (Functor.isoWhiskerLeft G e).inv).mp
  simpa only [diagramHomTransport, Category.assoc] using h

/-- Original comparison equations are retained under this specified transport. -/
theorem diagramHomTransport_comp {D : Type*} [Category D]
    {R S : X.Modules ⥤ D} (e : R ≅ S) {F G T : C ⥤ X.Modules}
    (q : F ⋙ S ⟶ G ⋙ S) (ψ : G ⟶ T) (γ : F ⟶ T)
    (hq : q ≫ Functor.whiskerRight ψ S = Functor.whiskerRight γ S) :
    diagramHomTransport e q ≫ Functor.whiskerRight ψ R = Functor.whiskerRight γ R := by
  apply NatTrans.ext
  funext c
  have hc := congrArg (fun η => η.app c) hq
  change q.app c ≫ S.map (ψ.app c) = S.map (γ.app c) at hc
  change (e.hom.app (F.obj c) ≫ q.app c ≫ e.inv.app (G.obj c)) ≫ R.map (ψ.app c) = _
  rw [Category.assoc, Category.assoc, ← e.inv.naturality,
    ← Category.assoc (q.app c), hc, ← Category.assoc, ← e.hom.naturality,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- The native composition comparison for a whole original coefficient diagram. -/
def restrictionDiagramCompIso (j : U ⟶ X) (k : V ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion k] (F : C ⥤ X.Modules) :
    F ⋙ restrictFunctor (k ≫ j) ≅ (F ⋙ restrictFunctor j) ⋙ restrictFunctor k :=
  Functor.isoWhiskerLeft F (restrictFunctorComp k j) ≪≫
    (Functor.associator F (restrictFunctor j) (restrictFunctor k)).symm

/-- Restriction along the original composite open immersion. -/
def restrictionDiagramHomMap (j : U ⟶ X) (k : V ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion k] {F G : C ⥤ X.Modules}
    (q : F ⋙ restrictFunctor j ⟶ G ⋙ restrictFunctor j) :
    F ⋙ restrictFunctor (k ≫ j) ⟶ G ⋙ restrictFunctor (k ≫ j) :=
  (restrictionDiagramCompIso j k F).hom ≫ Functor.whiskerRight q (restrictFunctor k) ≫
    (restrictionDiagramCompIso j k G).inv

/-- Native successive restriction preserves an original factorization equation. -/
theorem restrictionDiagramHomMap_comp
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    {F G T : C ⥤ X.Modules}
    (q : F ⋙ restrictFunctor j ⟶ G ⋙ restrictFunctor j)
    (ψ : G ⟶ T) (γ : F ⟶ T)
    (hq : q ≫ Functor.whiskerRight ψ (restrictFunctor j) =
      Functor.whiskerRight γ (restrictFunctor j)) :
    restrictionDiagramHomMap j k q ≫ Functor.whiskerRight ψ (restrictFunctor (k ≫ j)) =
      Functor.whiskerRight γ (restrictFunctor (k ≫ j)) := by
  apply NatTrans.ext
  funext c
  have hc := congrArg (fun η => η.app c) hq
  change q.app c ≫ (restrictFunctor j).map (ψ.app c) =
    (restrictFunctor j).map (γ.app c) at hc
  change ((restrictFunctorComp k j).hom.app (F.obj c) ≫
    (restrictFunctor k).map (q.app c) ≫ (restrictFunctorComp k j).inv.app (G.obj c)) ≫
      (restrictFunctor (k ≫ j)).map (ψ.app c) = _
  rw [Category.assoc, Category.assoc,
    ← (restrictFunctorComp k j).inv.naturality (ψ.app c),
    ← Category.assoc ((restrictFunctor k).map (q.app c)), Functor.comp_map,
    ← Functor.map_comp, hc]
  rw [← Functor.comp_map, ← Category.assoc,
    ← (restrictFunctorComp k j).hom.naturality (γ.app c),
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- Equality after native composite transport is equality of the successively
restricted original arrows. -/
theorem restrictionDiagramHomMap_injective
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    {F G : C ⥤ X.Modules}
    (q r : F ⋙ restrictFunctor j ⟶ G ⋙ restrictFunctor j)
    (h : restrictionDiagramHomMap j k q = restrictionDiagramHomMap j k r) :
    Functor.whiskerRight q (restrictFunctor k) =
      Functor.whiskerRight r (restrictFunctor k) := by
  apply (cancel_epi (restrictionDiagramCompIso j k F).hom).mp
  apply (cancel_mono (restrictionDiagramCompIso j k G).inv).mp
  simpa only [restrictionDiagramHomMap, Category.assoc] using h

end AlgebraicGeometry.Scheme.Modules.InternalHom
