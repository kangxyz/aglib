/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.DiagramRestriction

/-! # Gluing uniquely determined original comparison diagrams

Affine uniqueness applies to whole compatible families. Refining an overlap
by affine opens forces the native overlap equation, without assuming any
individual comparison coefficient is injective.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules.InternalHom
universe u v w
variable {X : Scheme.{u}} {C : Type v} [Category.{w} C]
  {F G T : C ⥤ X.Modules} (ψ : G ⟶ T) (γ : F ⟶ T)

/-- Affine whole-family uniqueness implies whole-family uniqueness on every
open, by the native affine cover of that open. -/
theorem factorization_unique_on_open
    (hlocal : ∀ (B : CommRingCat.{u}) (j : Spec B ⟶ X) [IsOpenImmersion j],
      ∃! q : F ⋙ restrictFunctor j ⟶ G ⋙ restrictFunctor j,
        q ≫ Functor.whiskerRight ψ (restrictFunctor j) =
          Functor.whiskerRight γ (restrictFunctor j))
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (q r : F ⋙ restrictFunctor j ⟶ G ⋙ restrictFunctor j)
    (hq : q ≫ Functor.whiskerRight ψ (restrictFunctor j) =
      Functor.whiskerRight γ (restrictFunctor j))
    (hr : r ≫ Functor.whiskerRight ψ (restrictFunctor j) =
      Functor.whiskerRight γ (restrictFunctor j)) : q = r := by
  apply NatTrans.ext
  funext c
  apply hom_ext_of_openCover (fun i => Spec (U.affineOpenCover.X i)) U.affineOpenCover.f
    (fun x => ⟨U.affineOpenCover.idx x, U.affineOpenCover.covers x⟩)
  intro i
  let k := U.affineOpenCover.f i
  obtain ⟨s, _, hs⟩ := hlocal (U.affineOpenCover.X i) (k ≫ j)
  have heq : restrictionDiagramHomMap j k q = restrictionDiagramHomMap j k r :=
    (hs _ (restrictionDiagramHomMap_comp j k q ψ γ hq)).trans
      (hs _ (restrictionDiagramHomMap_comp j k r ψ γ hr)).symm
  exact congrArg (fun η => η.app c) (restrictionDiagramHomMap_injective j k q r heq)

/-- Whisker a diagram arrow using the native associators before specializing
any geometric restriction functor. -/
private def whiskerDiagram {D E : Type*} [Category D] [Category E]
    (R : X.Modules ⥤ D) (S : D ⥤ E)
    (q : F ⋙ R ⟶ G ⋙ R) : F ⋙ (R ⋙ S) ⟶ G ⋙ (R ⋙ S) :=
  (Functor.associator F R S).inv ≫ Functor.whiskerRight q S ≫
    (Functor.associator G R S).hom

private theorem whiskerDiagram_app {D E : Type*} [Category D] [Category E]
    (R : X.Modules ⥤ D) (S : D ⥤ E)
    (q : F ⋙ R ⟶ G ⋙ R) (c : C) :
    (whiskerDiagram R S q).app c = S.map (q.app c) := by
  simp only [whiskerDiagram, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem whiskerDiagram_comp {D E : Type*} [Category D] [Category E]
    (R : X.Modules ⥤ D) (S : D ⥤ E)
    (q : F ⋙ R ⟶ G ⋙ R)
    (hq : q ≫ Functor.whiskerRight ψ R = Functor.whiskerRight γ R) :
    whiskerDiagram R S q ≫ Functor.whiskerRight ψ (R ⋙ S) =
      Functor.whiskerRight γ (R ⋙ S) := by
  apply NatTrans.ext
  funext c
  have hc := congrArg (fun η => η.app c) hq
  change q.app c ≫ R.map (ψ.app c) = R.map (γ.app c) at hc
  simp only [NatTrans.comp_app, whiskerDiagram_app, Functor.whiskerRight_app,
    Functor.comp_map, ← Functor.map_comp, hc]

/-- Local factorizations agree on original overlaps because their entire
restricted diagrams satisfy the same original equation. -/
theorem factorization_overlap_compatible
    (hlocal : ∀ (B : CommRingCat.{u}) (j : Spec B ⟶ X) [IsOpenImmersion j],
      ∃! q : F ⋙ restrictFunctor j ⟶ G ⋙ restrictFunctor j,
        q ≫ Functor.whiskerRight ψ (restrictFunctor j) =
          Functor.whiskerRight γ (restrictFunctor j))
    {ι : Type*} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (a i)]
    (q : ∀ i, F ⋙ restrictFunctor (a i) ⟶ G ⋙ restrictFunctor (a i))
    (hq : ∀ i, q i ≫ Functor.whiskerRight ψ (restrictFunctor (a i)) =
      Functor.whiskerRight γ (restrictFunctor (a i))) (c : C) :
    RestrictionHomCompatible a (F.obj c) (G.obj c) (fun i => (q i).app c) := by
  intro i k
  let l := pullback.fst (a i) (a k)
  let r := pullback.snd (a i) (a k)
  let e := overlapRestrictIso (a i) (a k)
  let ql := whiskerDiagram (restrictFunctor (a i)) (restrictFunctor l) (q i)
  let qr := whiskerDiagram (restrictFunctor (a k)) (restrictFunctor r) (q k)
  have hl : ql ≫ Functor.whiskerRight ψ (restrictFunctor (a i) ⋙ restrictFunctor l) =
      Functor.whiskerRight γ (restrictFunctor (a i) ⋙ restrictFunctor l) :=
    whiskerDiagram_comp ψ γ _ _ _ (hq i)
  have hr : qr ≫ Functor.whiskerRight ψ (restrictFunctor (a k) ⋙ restrictFunctor r) =
      Functor.whiskerRight γ (restrictFunctor (a k) ⋙ restrictFunctor r) :=
    whiskerDiagram_comp ψ γ _ _ _ (hq k)
  have heq := factorization_unique_on_open ψ γ hlocal (l ≫ a i)
    (diagramHomTransport (restrictFunctorComp l (a i)) ql)
    (diagramHomTransport (restrictFunctorComp l (a i)) (diagramHomTransport e qr))
    (diagramHomTransport_comp _ ql ψ γ hl)
    (diagramHomTransport_comp _ _ ψ γ (diagramHomTransport_comp e qr ψ γ hr))
  have hqr := diagramHomTransport_injective _ _ _ heq
  have hc := congrArg (fun η => η.app c) hqr
  simp only [diagramHomTransport, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, ql, qr, whiskerDiagram_app] at hc
  change (restrictFunctor l).map ((q i).app c) =
    e.hom.app (F.obj c) ≫ (restrictFunctor r).map ((q k).app c) ≫
      e.inv.app (G.obj c) at hc
  dsimp only [e, r] at hc
  rw [hc]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact congrArg (fun z => (overlapRestrictIso (a i) (a k)).hom.app (F.obj c) ≫ z)
    (Category.comp_id ((restrictFunctor r).map ((q k).app c)))

/-- Affine-local unique factorization glues to an actual unique global
factorization of the original diagrams. -/
theorem existsUnique_factorization_of_affine
    (hlocal : ∀ (B : CommRingCat.{u}) (j : Spec B ⟶ X) [IsOpenImmersion j],
      ∃! q : F ⋙ restrictFunctor j ⟶ G ⋙ restrictFunctor j,
        q ≫ Functor.whiskerRight ψ (restrictFunctor j) =
          Functor.whiskerRight γ (restrictFunctor j)) :
    ∃! q : F ⟶ G, q ≫ ψ = γ := by
  classical
  let Y i := Spec (X.affineOpenCover.X i)
  let a := X.affineOpenCover.f
  have hcover : ∀ x : X, ∃ (i : X.affineOpenCover.I₀) (y : Y i), a i y = x :=
    fun x => ⟨X.affineOpenCover.idx x, X.affineOpenCover.covers x⟩
  let q i := (hlocal (X.affineOpenCover.X i) (a i)).choose
  have hq i := (hlocal (X.affineOpenCover.X i) (a i)).choose_spec.1
  let hc := factorization_overlap_compatible ψ γ hlocal Y a q hq
  refine ⟨glueRestrictionDiagramHom Y a hcover F G q hc,
    glueRestrictionDiagramHom_comp Y a hcover F G q hc T ψ γ hq, ?_⟩
  intro r hr
  apply glueRestrictionDiagramHom_unique
  intro i
  exact (hlocal (X.affineOpenCover.X i) (a i)).choose_spec.2 _ (by
    dsimp only
    rw [← Functor.whiskerRight_comp, hr])

end AlgebraicGeometry.Scheme.Modules.InternalHom
