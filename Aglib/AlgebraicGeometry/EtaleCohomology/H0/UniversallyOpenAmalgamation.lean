/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.UniversallyOpenDescent
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteSectionRepresentatives
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Basic
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.CanonicalSectionGluing
public import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Local original-section lifts for universally open descent

The comparison object below is the existing native Over pullback followed by
its original base map. A matching section and an original local representative
produce an actual open of that representative's etale test. On this open all
relative restrictions agree, and every point admitting that representative
lies in the open. This is the local input to original etale sheaf gluing.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open Continuity Scheme.LocalRepresentability
attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}}

private abbrev comparisonObject (T U : Over X) : Over X :=
  (Over.map T.hom).obj ((Over.pullback T.hom).obj U)

private def comparisonToSource (T U : Over X) : comparisonObject T U ⟶ T :=
  Over.homMk (pullback.snd U.hom T.hom)

private def comparisonToTest (T U : Over X) : comparisonObject T U ⟶ U :=
  Over.homMk (pullback.fst U.hom T.hom) pullback.condition

private theorem comparisonToTest_eq_counit (T U : Over X) :
    comparisonToTest T U = (Over.mapPullbackAdj T.hom).counit.app U := by
  simp only [Over.mapPullbackAdj_counit_app, comparisonToTest]

private instance comparisonToTest_surjective (T U : Over X) [Surjective T.hom] :
    Surjective (comparisonToTest T U).left :=
  inferInstanceAs (Surjective (pullback.fst U.hom T.hom))

private instance comparisonToTest_universallyOpen (T U : Over X)
    [UniversallyOpen T.hom] : UniversallyOpen (comparisonToTest T U).left :=
  inferInstanceAs (UniversallyOpen (pullback.fst U.hom T.hom))

private def comparisonLift {T U R : Over X} (a : R ⟶ T) (b : R ⟶ U) :
    R ⟶ comparisonObject T U :=
  Over.homMk (pullback.lift b.left a.left ((Over.w b).trans (Over.w a).symm))
    (by simp only [comparisonObject, Over.map_obj_hom, Over.pullback_obj_hom,
      ← Category.assoc, pullback.lift_snd, Over.w])

private theorem comparisonLift_source {T U R : Over X} (a : R ⟶ T) (b : R ⟶ U) :
    comparisonLift a b ≫ comparisonToSource T U = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

private theorem comparisonLift_test {T U R : Over X} (a : R ⟶ T) (b : R ⟶ U) :
    comparisonLift a b ≫ comparisonToTest T U = b := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

private theorem section_map_comp_apply (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1})
    {R U T : Over X} (a : R ⟶ U) (b : U ⟶ T) (s : P.obj (op T)) :
    P.map a.op (P.map b.op s) = P.map (a ≫ b).op s :=
  (ConcreteCategory.congr_hom (P.map_comp b.op a.op) s).symm

/-- Restriction across a commuting original square transports a glued section's
boundary equation to the matching section. Both restrictions and their
composite are formed before the native inverse-image functor is substituted. -/
private theorem section_square_gluing
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) {R T U B : Over X}
    (a : R ⟶ T) (b : R ⟶ U) (q : T ⟶ B) (d : U ⟶ B)
    (h : a ≫ q = b ≫ d) (v : P.obj (op B)) (s : P.obj (op T))
    (t : P.obj (op U)) (hv : P.map d.op v = t)
    (ht : P.map a.op s = P.map b.op t) :
    P.map a.op (P.map q.op v) = P.map a.op s := by
  calc
    P.map a.op (P.map q.op v) = P.map (a ≫ q).op v :=
      section_map_comp_apply P a q v
    _ = P.map (b ≫ d).op v := congrArg (fun k : R ⟶ B => P.map k.op v) h
    _ = P.map b.op (P.map d.op v) := (section_map_comp_apply P b d v).symm
    _ = P.map b.op t := congrArg (P.map b.op) hv
    _ = P.map a.op s := ht.symm

private theorem terminal_from_left {Y : Scheme.{u}} (U : Y.Etale) :
    ((etaleTerminalIsTerminal Y).from U).left = U.hom := by
  have h : ((etaleTerminalIsTerminal Y).from U).left ≫ 𝟙 Y = U.hom :=
    ((etaleTerminalIsTerminal Y).from U).w
  exact (Category.comp_id _).symm.trans h

/-- The complete comparison-open agreement construction is proved with the
original section functor variable before native coefficient specialization. -/
private theorem comparisonOpen_agreement
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1})
    (Z : ∀ R : Over X, P.obj (op R) → R.left.Opens)
    (hZ : ∀ {R U : Over X} (a : R ⟶ U) (s : P.obj (op U)),
      Z R (P.map a.op s) = a.left ⁻¹ᵁ Z U s)
    (hzero : ∀ (R : Over X) (s : P.obj (op R)), Z R s = ⊤ ↔ s = 0)
    (T U : Over X) (s : P.obj (op T)) (t : P.obj (op U))
    (V : U.left.Opens)
    (hV : (comparisonToTest T U).left ⁻¹ᵁ V = Z (comparisonObject T U)
      (P.map (comparisonToSource T U).op s - P.map (comparisonToTest T U).op t)) :
    (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ overOpens U V),
      P.map a.op s = P.map (b ≫ overOpensι U V).op t) ∧
    (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ U),
      P.map a.op s = P.map b.op t → b.left ⁻¹ᵁ V = ⊤) := by
  let Q := comparisonObject T U
  let a₀ : Q ⟶ T := comparisonToSource T U
  let b₀ : Q ⟶ U := comparisonToTest T U
  let δ := P.map a₀.op s - P.map b₀.op t
  have hmap (R : Over X) (a : R ⟶ T) (b : R ⟶ U) :
      P.map (comparisonLift a b).op δ = P.map a.op s - P.map b.op t := by
    change P.map (comparisonLift a b).op (P.map a₀.op s - P.map b₀.op t) = _
    rw [map_sub, section_map_comp_apply, section_map_comp_apply,
      comparisonLift_source, comparisonLift_test]
  have hopen (R : Over X) (a : R ⟶ T) (b : R ⟶ U) :
      Z R (P.map a.op s - P.map b.op t) = b.left ⁻¹ᵁ V := by
    rw [← hmap R a b, hZ, ← hV, ← Scheme.Hom.comp_preimage]
    have hl : (comparisonLift a b).left ≫ b₀.left = b.left :=
      congrArg (fun z : R ⟶ U => z.left) (comparisonLift_test a b)
    rw [hl]
  constructor
  · intro R a b
    apply sub_eq_zero.mp
    apply (hzero R _).mp
    rw [hopen]
    change (b.left ≫ V.ι) ⁻¹ᵁ V = ⊤
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]
  · intro R a b hab
    rw [← hopen R a b, hab, sub_self]
    exact (hzero R 0).mpr rfl

private theorem exists_comparisonOpen_agreement
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1})
    (Z : ∀ R : Over X, P.obj (op R) → R.left.Opens)
    (hZ : ∀ {R U : Over X} (a : R ⟶ U) (s : P.obj (op U)),
      Z R (P.map a.op s) = a.left ⁻¹ᵁ Z U s)
    (hzero : ∀ (R : Over X) (s : P.obj (op R)), Z R s = ⊤ ↔ s = 0)
    (T U : Over X) (s : P.obj (op T)) (t : P.obj (op U))
    (hex : ∃! V : U.left.Opens,
      (comparisonToTest T U).left ⁻¹ᵁ V = Z (comparisonObject T U)
        (P.map (comparisonToSource T U).op s - P.map (comparisonToTest T U).op t)) :
    ∃ V : U.left.Opens,
      (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ overOpens U V),
        P.map a.op s = P.map (b ≫ overOpensι U V).op t) ∧
      (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ U),
        P.map a.op s = P.map b.op t → b.left ⁻¹ᵁ V = ⊤) := by
  obtain ⟨V, hV, _⟩ := hex
  exact ⟨V, comparisonOpen_agreement P Z hZ hzero T U s t V hV⟩

/-- A matching section has a maximal comparison open at an original test
representative. Restrictions agree on that open, and every point at which the
original representative already agrees belongs to it. No local-lifting or
section-descent premise is imposed. -/
theorem exists_open_of_matching_representative
    (F : AbelianSheaf.{u, u + 1} X) (T U : Over X)
    [UniversallyOpen T.hom] [Surjective T.hom]
    (s : (pullbackSectionsFunctor F).obj (op T))
    (hs : IsMatchingRelativeSection F T s)
    (t : (pullbackSectionsFunctor F).obj (op U)) :
    ∃ V : U.left.Opens,
      (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ overOpens U V),
        (pullbackSectionsFunctor F).map a.op s =
          (pullbackSectionsFunctor F).map (b ≫ overOpensι U V).op t) ∧
      (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ U),
        (pullbackSectionsFunctor F).map a.op s =
          (pullbackSectionsFunctor F).map b.op t →
        b.left ⁻¹ᵁ V = ⊤) := by
  exact exists_comparisonOpen_agreement (pullbackSectionsFunctor F)
    (relativeSectionZeroOpen F) (fun a s => relativeSectionZeroOpen_map F a s)
    (relativeSectionZeroOpen_top_iff F) T U s t
    (existsUnique_comparisonOpen F (comparisonToSource T U) (comparisonToTest T U)
      (comparisonToTest T U).left.isOpenMap s hs t)

/-- An original point representative, including its actual relative arrows
and the section equation. This shares the complete local construction without
introducing another sheaf or another realization of its sections. -/
structure RelativePointSectionRepresentative
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) (T : Over X) (s : P.obj (op T)) (x : T.left) where
  scheme : Over X
  point : scheme.left
  test : X.Etale
  toSource : scheme ⟶ T
  toTest : scheme ⟶ (Etale.forget X).obj test
  value : P.obj (op ((Etale.forget X).obj test))
  point_eq : toSource.left point = x
  section_eq : P.map toSource.op s = P.map toTest.op value

/-- Pointwise lifting from an original locally surjective presentation. The
whole geometric-point lifting and original relative representative are built
with the presheaves variable, before applying inverse-image construction. -/
private theorem pointRepresentative_of_presentation
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) (T : Over X) (s : P.obj (op T))
    (A G : T.left.Etaleᵒᵖ ⥤ Ab.{u + 1}) (q : A ⟶ G)
    [Presheaf.IsLocallySurjective T.left.smallEtaleTopology q]
    (s₀ : G.obj (op (etaleTerminal T.left)))
    (hrep : ∀ (W : T.left.Etale) (g : W ⟶ etaleTerminal T.left) (v : A.obj (op W)),
      q.app (op W) v = G.map g.op s₀ →
      ∃ (U : X.Etale) (a : Over.mk (W.hom ≫ T.hom) ⟶ (Etale.forget X).obj U)
        (t : P.obj (op ((Etale.forget X).obj U))),
        P.map (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ T).op s = P.map a.op t)
    (x : T.left) : Nonempty (RelativePointSectionRepresentative P T s x) := by
  let η := FibrewiseClosed.geometricPoint x
  let p : (pointSmallEtale η).fiber.obj (etaleTerminal T.left) :=
    Over.homMk η (by simp)
  obtain ⟨W, g, hg, y, hy⟩ := (pointSmallEtale η).jointly_surjective
    (Presheaf.imageSieve q s₀) (Presheaf.imageSieve_mem T.left.smallEtaleTopology q s₀) p
  obtain ⟨U, a, t, ht⟩ := hrep W g (Presheaf.localPreimage q s₀ g hg)
    (Presheaf.app_localPreimage q s₀ g hg)
  refine ⟨{
    scheme := Over.mk (W.hom ≫ T.hom)
    point := y.left (default : Spec (.of (FibrewiseClosed.pointField x)))
    test := U
    toSource := Over.homMk W.hom
    toTest := a
    value := t
    point_eq := ?_
    section_eq := ht }⟩
  have hl : y.left ≫ g.left = p.left :=
    congrArg (fun z : (pointSmallEtale η).fiber.obj (etaleTerminal T.left) => z.left) hy
  have he := congrArg
    (fun k : Spec (.of (FibrewiseClosed.pointField x)) ⟶ T.left => k default) hl
  have hg' : g.left = W.hom := by
    have h : g.left ≫ 𝟙 T.left = W.hom := g.w
    exact (Category.comp_id _).symm.trans h
  rw [hg'] at he
  exact he.trans (FibrewiseClosed.geometricPoint_apply x _)

/-- Complete lifting of a presentation generator through its original map.
The actual generator maps, their comparison and the original restriction
transport are retained as inputs. The representative is the existing
`Functor.representativeSection` for the same functor and its original
etale evaluation natural isomorphism, rather than independently reconstructed
group carriers. All dependent elimination and normalization occur here before
native inverse-image specialization. -/
private theorem relativeRepresentative_of_presentation_generators
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) (Q : X.Etaleᵒᵖ ⥤ Ab.{u + 1})
    (T : Over X) (s : P.obj (op T)) (W : T.left.Etale)
    (A G : Ab.{u + 1}) (q : A ⟶ G) (v : A) (s₀ : G) (hv : q v = s₀)
    (e : (Etale.forget X).op ⋙ P ≅ Q)
    (raw : P.obj (op T) ⟶ P.obj (op (Over.mk (W.hom ≫ T.hom))))
    (hrawmap : P.map (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ T).op = raw)
    (genA : ∀ U : X.Etale, (W ⟶ (siteBaseChange T.hom).obj U) → Q.obj (op U) → A)
    (genG : ∀ U : X.Etale, (W ⟶ (siteBaseChange T.hom).obj U) → Q.obj (op U) → G)
    (hgen : ∃ (U : X.Etale) (a : W ⟶ (siteBaseChange T.hom).obj U)
      (t : Q.obj (op U)), genA U a t = v)
    (hmap : ∀ U a t, q (genA U a t) = genG U a t)
    (htransport : ∀ U a t, genG U a t = s₀ →
      raw s = Functor.representativeSection (Etale.forget X) P e U
        (unitRepresentativeArrow T.hom a) t) :
    ∃ (U : X.Etale) (a : Over.mk (W.hom ≫ T.hom) ⟶ (Etale.forget X).obj U)
      (t : P.obj (op ((Etale.forget X).obj U))),
      P.map (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ T).op s = P.map a.op t := by
  obtain ⟨U, a, t, ht⟩ := hgen
  refine ⟨U, unitRepresentativeArrow T.hom a, (e.app (op U)).inv t, ?_⟩
  have hu := htransport U a t ((hmap U a t).symm.trans ((congrArg q ht).trans hv))
  exact (ConcreteCategory.congr_hom hrawmap s).trans hu

/-- The same original restriction morphism with its target written as the
original Over object or its native `Over.mk` constructor. This is an equality
of complete section morphisms, not a scalar definitional conversion. -/
private theorem relativeRestrictionMap_target_mk
    (F : AbelianSheaf.{u, u + 1} X) (T : Over X) (W : T.left.Etale) :
    pullbackSectionsMap F
      (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ T) =
    pullbackSectionsMap F
      (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ Over.mk T.hom) := rfl

/-- The original functor restriction and the original unit transport use the
same complete map, with the target constructor normalization kept explicit. -/
private theorem relativeRestrictionMap_normalized
    (F : AbelianSheaf.{u, u + 1} X) (T : Over X) (W : T.left.Etale) :
    (pullbackSectionsFunctor F).map
      (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ T).op =
    pullbackSectionsMap F
      (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ Over.mk T.hom) :=
  (pullbackSectionsFunctor_map F
    (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ T)).trans
      (relativeRestrictionMap_target_mk F T W)

/-- Original Kan representatives and the original unit transport, on a fixed
source test. The point construction does not re-eliminate this presentation. -/
private theorem relativeRepresentative_of_nativePresentation
    (F : AbelianSheaf.{u, u + 1} X) (T : Over X)
    (s : (pullbackSectionsFunctor F).obj (op T))
    (W : T.left.Etale) (g : W ⟶ etaleTerminal T.left)
    (v : (EtaleAffineBasis.inverseImagePresentation T.hom F).obj (op W))
    (hv : (EtaleAffineBasis.inverseImagePresentationMap T.hom F).app (op W) v =
      ((inverseImage T.hom).obj F).obj.map g.op s) :
    ∃ (U : X.Etale) (a : Over.mk (W.hom ≫ T.hom) ⟶ (Etale.forget X).obj U)
      (t : (pullbackSectionsFunctor F).obj (op ((Etale.forget X).obj U))),
      (pullbackSectionsFunctor F).map
        (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ T).op s =
          (pullbackSectionsFunctor F).map a.op t := by
  exact relativeRepresentative_of_presentation_generators (pullbackSectionsFunctor F) F.obj
    T s W ((EtaleAffineBasis.inverseImagePresentation T.hom F).obj (op W))
    (((inverseImage T.hom).obj F).obj.obj (op W))
    ((EtaleAffineBasis.inverseImagePresentationMap T.hom F).app (op W)) v
    (((inverseImage T.hom).obj F).obj.map g.op s) hv
    (pullbackSectionsEtaleNatIso F)
    (pullbackSectionsMap F
      (Over.homMk W.hom : Over.mk (W.hom ≫ T.hom) ⟶ Over.mk T.hom))
    (relativeRestrictionMap_normalized F T W)
    (fun U a t => (EtaleAffineBasis.inverseImagePresentation T.hom F).map a.op
      (((siteBaseChange T.hom).op.lanUnit.app F.obj).app (op U) t))
    (fun U a t => ((inverseImage T.hom).obj F).obj.map a.op
      (((inverseImageAdjunction T.hom).unit.app F).hom.app (op U) t))
    (EtaleAffineBasis.exists_inverseImagePresentation_representative T.hom F W v)
    (EtaleAffineBasis.inverseImagePresentationMap_representative T.hom F W)
    (fun U a t h => EtaleAffineBasis.pullbackSectionsMap_eq_representative_of_unit_eq
      T.hom F W U a g s t h)

/-- At any original source point, a section admits a representative through
its actual inverse-image presentation and original coefficient unit. -/
theorem exists_relative_section_representative_at_point
    (F : AbelianSheaf.{u, u + 1} X) (T : Over X)
    (s : (pullbackSectionsFunctor F).obj (op T)) (x : T.left) :
    Nonempty (RelativePointSectionRepresentative (pullbackSectionsFunctor F) T s x) :=
  pointRepresentative_of_presentation (pullbackSectionsFunctor F) T s
    (EtaleAffineBasis.inverseImagePresentation T.hom F) ((inverseImage T.hom).obj F).obj
    (EtaleAffineBasis.inverseImagePresentationMap T.hom F) s
    (relativeRepresentative_of_nativePresentation F T s) x

/-- The actual open-refined cover construction for a variable original
section functor. Representatives retain their original schemes, points and
arrows; no new coefficient realization is introduced. -/
private theorem exists_etale_cover_of_local_agreement
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) (T : Over X) [Surjective T.hom]
    (s : P.obj (op T))
    (hrep : ∀ x : T.left, Nonempty (RelativePointSectionRepresentative P T s x))
    (hopen : ∀ (U : Over X) (t : P.obj (op U)), ∃ V : U.left.Opens,
      (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ overOpens U V),
        P.map a.op s = P.map (b ≫ overOpensι U V).op t) ∧
      (∀ (R : Over X) (a : R ⟶ T) (b : R ⟶ U),
        P.map a.op s = P.map b.op t → b.left ⁻¹ᵁ V = ⊤)) :
    ∃ (J : Type u) (D : J → X.Etale)
      (t : ∀ j, P.obj (op ((Etale.forget X).obj (D j)))),
      (∀ x : X, ∃ j, ∃ y : (D j).left, (D j).hom y = x) ∧
      (∀ j (R : Over X) (a : R ⟶ T) (b : R ⟶ (Etale.forget X).obj (D j)),
        P.map a.op s = P.map b.op (t j)) := by
  let r (x : T.left) := Classical.choice (hrep x)
  let R (x : T.left) := (r x).scheme
  let y (x : T.left) := (r x).point
  let U (x : T.left) := (r x).test
  let c (x : T.left) := (r x).toSource
  let a (x : T.left) := (r x).toTest
  let t (x : T.left) := (r x).value
  have hy (x : T.left) := (r x).point_eq
  have ht (x : T.left) := (r x).section_eq
  have hex (j : T.left) := hopen ((Etale.forget X).obj (U j)) (t j)
  choose V hV using hex
  let D (j : T.left) : X.Etale := by
    letI : AlgebraicGeometry.Etale (U j).hom := (U j).prop
    exact Scheme.Etale.mk ((V j).ι ≫ (U j).hom)
  let tD (j : T.left) : P.obj (op ((Etale.forget X).obj (D j))) :=
    P.map (overOpensι ((Etale.forget X).obj (U j)) (V j)).op (t j)
  have hmem (j : T.left) : (a j).left ⁻¹ᵁ V j = ⊤ :=
    (hV j).2 (R j) (c j) (a j) (ht j)
  refine ⟨T.left, D, tD, ?_, ?_⟩
  · intro x
    obtain ⟨z, hz⟩ := T.hom.surjective x
    have hyV : (a z).left (y z) ∈ V z := by
      change y z ∈ (a z).left ⁻¹ᵁ V z
      rw [hmem]; trivial
    refine ⟨z, ⟨(a z).left (y z), hyV⟩, ?_⟩
    change (U z).hom ((a z).left (y z)) = x
    have hw : (a z).left ≫ (U z).hom = (c z).left ≫ T.hom :=
      (Over.w (a z)).trans (Over.w (c z)).symm
    exact (congrArg (fun k : (R z).left ⟶ X => k (y z)) hw).trans
      ((congrArg T.hom (hy z)).trans hz)
  · intro j R b c
    exact ((hV j).1 R b c).trans (section_map_comp_apply P c
      (overOpensι ((Etale.forget X).obj (U j)) (V j)) (t j)).symm

/-- Original local representatives of a matching section produce an actual
etale covering of the base with universally compatible original relative
sections. The native pointwise representative producer imposes no
quasi-compactness or coefficient finiteness condition. -/
theorem exists_etale_cover_of_matching_section
    (F : AbelianSheaf.{u, u + 1} X) (T : Over X)
    [UniversallyOpen T.hom] [Surjective T.hom]
    (s : (pullbackSectionsFunctor F).obj (op T))
    (hs : IsMatchingRelativeSection F T s) :
    ∃ (J : Type u) (D : J → X.Etale)
      (t : ∀ j, (pullbackSectionsFunctor F).obj (op ((Etale.forget X).obj (D j)))),
      (∀ x : X, ∃ j, ∃ y : (D j).left, (D j).hom y = x) ∧
      (∀ j (R : Over X) (a : R ⟶ T) (b : R ⟶ (Etale.forget X).obj (D j)),
        (pullbackSectionsFunctor F).map a.op s =
          (pullbackSectionsFunctor F).map b.op (t j)) := by
  exact exists_etale_cover_of_local_agreement (pullbackSectionsFunctor F) T s
    (exists_relative_section_representative_at_point F T s)
    (fun U t => exists_open_of_matching_representative F T U s hs t)

/-- Original sheaf amalgamation transported through its given evaluation
isomorphisms. The complete gluing and restriction equations are constructed
before specializing the relative inverse-image sections. -/
private theorem exists_glued_relative_section
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) (F : AbelianSheaf.{u, u + 1} X)
    (e : ∀ U : X.Etale, P.obj (op ((Etale.forget X).obj U)) ≅ F.obj.obj (op U))
    (he : ∀ {U V : X.Etale} (a : U ⟶ V),
      P.map ((Etale.forget X).map a).op ≫ (e U).hom =
        (e V).hom ≫ F.obj.map a.op)
    {J : Type u} (D : J → X.Etale)
    (t : ∀ j, P.obj (op ((Etale.forget X).obj (D j))))
    (hc : Sieve.ofArrows D (fun j => (etaleTerminalIsTerminal X).from (D j)) ∈
      X.smallEtaleTopology (etaleTerminal X))
    (ht : ∀ (i j : J) (V : X.Etale) (a : V ⟶ D i) (b : V ⟶ D j),
      P.map ((Etale.forget X).map a).op (t i) =
        P.map ((Etale.forget X).map b).op (t j)) :
    ∃ v : P.obj (op ((Etale.forget X).obj (etaleTerminal X))),
      ∀ j, P.map ((Etale.forget X).map
        ((etaleTerminalIsTerminal X).from (D j))).op v = t j := by
  have hcompatible : Presieve.Arrows.Compatible
      (F.obj ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j => (etaleTerminalIsTerminal X).from (D j))
      (fun j => (e (D j)).hom (t j)) := by
    intro i j V a b _
    exact (ConcreteCategory.congr_hom (he a) (t i)).symm.trans
      ((congrArg (e V).hom (ht i j V a b)).trans
        (ConcreteCategory.congr_hom (he b) (t j)))
  have htype : Presieve.IsSheaf X.smallEtaleTopology
      (F.obj ⋙ CategoryTheory.forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget Ab.{u + 1})).obj F).property
  obtain ⟨v, hv, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp
    (htype.isSheafFor (Presieve.ofArrows D
      (fun j => (etaleTerminalIsTerminal X).from (D j))) hc)
      (fun j => (e (D j)).hom (t j)) hcompatible
  refine ⟨(e (etaleTerminal X)).inv v, ?_⟩
  intro j
  apply (ConcreteCategory.bijective_of_isIso (e (D j)).hom).injective
  have hn := ConcreteCategory.congr_hom
    (he ((etaleTerminalIsTerminal X).from (D j))) ((e (etaleTerminal X)).inv v)
  have hval : (e (etaleTerminal X)).hom ((e (etaleTerminal X)).inv v) = v :=
    Iso.inv_hom_id_apply (e (etaleTerminal X)) v
  have hv' := hv j
  change F.obj.map ((etaleTerminalIsTerminal X).from (D j)).op v = _ at hv'
  exact hn.trans ((congrArg (F.obj.map
    ((etaleTerminalIsTerminal X).from (D j)).op) hval).trans hv')

/-- The original relative sections are separated on an actual base-changed
etale covering. This is the original sheaf separation theorem, with the same
comparison objects used by amalgamation. -/
private theorem relativeSections_separated_on_baseChange
    (F : AbelianSheaf.{u, u + 1} X) (T : Over X)
    {J : Type u} (D : J → X.Etale)
    (hD : ∀ x : X, ∃ j, ∃ y : (D j).left, (D j).hom y = x)
    (v w : (pullbackSectionsFunctor F).obj (op T))
    (h : ∀ j, (pullbackSectionsFunctor F).map
      (comparisonToSource T ((Etale.forget X).obj (D j))).op v =
        (pullbackSectionsFunctor F).map
          (comparisonToSource T ((Etale.forget X).obj (D j))).op w) : v = w := by
  let W (j : J) := (siteBaseChange T.hom).obj (D j)
  have hw : Sieve.ofArrows W
      (fun j => (etaleTerminalIsTerminal T.left).from (W j)) ∈
      T.left.smallEtaleTopology (etaleTerminal T.left) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨j, y, hy⟩ := hD (T.hom z)
    obtain ⟨r, _, hr⟩ := Scheme.Pullback.exists_preimage_pullback y z hy
    exact ⟨j, r, (congrArg (fun f : (W j).left ⟶ T.left => f r)
      (terminal_from_left (W j))).trans hr⟩
  exact EtaleAffineBasis.canonicalSections_eq_of_etale_cover T.hom F W hw v w h

/-- Complete unique amalgamation from original local agreement, original
sheaf gluing, surjective detection and original cover separation. All section
operations belong to the given functor, and specialization does not eliminate
or reconstruct dependent covering families. -/
private theorem unique_amalgamation_of_local_agreement
    (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) (F : AbelianSheaf.{u, u + 1} X)
    (e : ∀ U : X.Etale, P.obj (op ((Etale.forget X).obj U)) ≅ F.obj.obj (op U))
    (he : ∀ {U V : X.Etale} (a : U ⟶ V),
      P.map ((Etale.forget X).map a).op ≫ (e U).hom =
        (e V).hom ≫ F.obj.map a.op)
    (hinj : ∀ {R U : Over X} (a : R ⟶ U), Surjective a.left →
      Function.Injective (P.map a.op))
    (T : Over X) [Surjective T.hom]
    (hsep : ∀ {J : Type u} (D : J → X.Etale),
      (∀ x : X, ∃ j, ∃ y : (D j).left, (D j).hom y = x) →
      ∀ v w : P.obj (op T),
      (∀ j, P.map (comparisonToSource T ((Etale.forget X).obj (D j))).op v =
        P.map (comparisonToSource T ((Etale.forget X).obj (D j))).op w) → v = w)
    (s : P.obj (op T))
    (hcover : ∃ (J : Type u) (D : J → X.Etale)
      (t : ∀ j, P.obj (op ((Etale.forget X).obj (D j)))),
      (∀ x : X, ∃ j, ∃ y : (D j).left, (D j).hom y = x) ∧
      (∀ j (R : Over X) (a : R ⟶ T) (b : R ⟶ (Etale.forget X).obj (D j)),
        P.map a.op s = P.map b.op (t j))) :
    ∃! t : P.obj (op (Over.mk (𝟙 X))),
      P.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 X)).op t = s := by
  obtain ⟨J, D, t, hD, ht⟩ := hcover
  have hrelative {V : Over X} (i j : J)
      (a : V ⟶ (Etale.forget X).obj (D i))
      (b : V ⟶ (Etale.forget X).obj (D j)) :
      P.map a.op (t i) =
        P.map b.op (t j) := by
    let R := comparisonObject T V
    let r : R ⟶ V := comparisonToTest T V
    let c : R ⟶ T := comparisonToSource T V
    let : Surjective r.left :=
      inferInstanceAs (Surjective (pullback.fst V.hom T.hom))
    apply hinj r inferInstance
    rw [section_map_comp_apply, section_map_comp_apply]
    exact (ht i R c (r ≫ a)).symm.trans (ht j R c (r ≫ b))
  have hc : Sieve.ofArrows D (fun j => (etaleTerminalIsTerminal X).from (D j)) ∈
      X.smallEtaleTopology (etaleTerminal X) := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨j, y, hy⟩ := hD x
    exact ⟨j, y, (congrArg (fun f : (D j).left ⟶ X => f y)
      (terminal_from_left (D j))).trans hy⟩
  obtain ⟨u₀, hu⟩ := exists_glued_relative_section P F e he
    D t hc (fun i j V a b =>
      hrelative i j ((Etale.forget X).map a) ((Etale.forget X).map b))
  let q : T ⟶ Over.mk (𝟙 X) := Over.homMk T.hom (by simp)
  have hu₀ : P.map q.op u₀ = s := by
    apply hsep D hD
    intro j
    let U := (Etale.forget X).obj (D j)
    let R := comparisonObject T U
    let a : R ⟶ T := comparisonToSource T U
    let b : R ⟶ U := comparisonToTest T U
    let d : U ⟶ Over.mk (𝟙 X) :=
      (Etale.forget X).map ((etaleTerminalIsTerminal X).from (D j))
    change P.map a.op
      (P.map q.op u₀) =
      P.map a.op s
    have htri : a ≫ q = b ≫ d := Over.mkIdTerminal.hom_ext _ _
    exact section_square_gluing P a b q d htri
      u₀ s (t j) (hu j) (ht j R a b)
  refine ⟨u₀, hu₀, ?_⟩
  intro v' hv'
  let : Surjective q.left := inferInstanceAs (Surjective T.hom)
  exact hinj q inferInstance (hv'.trans hu₀.symm)

/-- Matching original relative sections descend uniquely along a universally
open surjection. The coefficient is an arbitrary
original abelian sheaf. The target section is on the original terminal relative
scheme, not in a replacement sheaf. -/
theorem existsUnique_relative_section_of_universallyOpen_surjective
    (F : AbelianSheaf.{u, u + 1} X) (T : Over X)
    [UniversallyOpen T.hom] [Surjective T.hom]
    (s : (pullbackSectionsFunctor F).obj (op T))
    (hs : IsMatchingRelativeSection F T s) :
    ∃! t : (pullbackSectionsFunctor F).obj (op (Over.mk (𝟙 X))),
      (pullbackSectionsFunctor F).map
        (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 X)).op t = s := by
  exact unique_amalgamation_of_local_agreement (pullbackSectionsFunctor F) F
    (pullbackSectionsEtaleEvaluationIso F) (fun a => pullbackSectionsMap_etaleEvaluation F a)
    (fun a ha => @pullbackSectionsMap_injective_of_surjective _ F _ _ a ha)
    T (relativeSections_separated_on_baseChange F T) s
    (exists_etale_cover_of_matching_section F T s hs)

/-- Evaluation at the unchanged terminal etale test identifies relative
restriction with the original global-section pullback, as an equality of maps. -/
theorem terminalRelativeSectionPullback_eq {S : Scheme.{u}} (f : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) :
    (pullbackSectionsEtaleEvaluationIso F (etaleTerminal X)).inv ≫
      pullbackSectionsMap F
        (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 X)) =
      globalSectionsPullback f F := by
  have h := pullbackSectionsMap_relativeTerminalTest F f (etaleTerminal X) f
    (Category.comp_id f)
  have ht : relativeTerminalTest f (etaleTerminal X) f (Category.comp_id f) =
      (siteBaseChangeTerminalIso f).inv :=
    ((etaleTerminalIsTerminal X).isTerminalObj (siteBaseChange f)).hom_ext _ _
  exact h.trans (congrArg (unitSectionMap f F) ht)

/-- The unique descended section is an actual section of the original sheaf,
and its equation is the literal original inverse-image section map. -/
theorem existsUnique_globalSection_of_universallyOpen_surjective
    {S : Scheme.{u}} (f : S ⟶ X)
    [UniversallyOpen f] [Surjective f]
    (F : AbelianSheaf.{u, u + 1} X)
    (s : (globalSections S).obj ((inverseImage f).obj F))
    (hs : IsMatchingRelativeSection F (Over.mk f) s) :
    ∃! t : (globalSections X).obj F, globalSectionsPullback f F t = s := by
  let : UniversallyOpen (Over.mk f).hom := inferInstanceAs (UniversallyOpen f)
  let : Surjective (Over.mk f).hom := inferInstanceAs (Surjective f)
  obtain ⟨u₀, hu, huniq⟩ :=
    existsUnique_relative_section_of_universallyOpen_surjective F (Over.mk f) s hs
  let e := pullbackSectionsEtaleEvaluationIso F (etaleTerminal X)
  let q : Over.mk f ⟶ Over.mk (𝟙 X) := Over.homMk f (by simp)
  have hmap (t : (globalSections X).obj F) :
      (pullbackSectionsFunctor F).map q.op (e.inv t) = globalSectionsPullback f F t :=
    ConcreteCategory.congr_hom (terminalRelativeSectionPullback_eq f F) t
  have hq : q = (Over.homMk (Over.mk f).hom (by simp) :
      Over.mk f ⟶ Over.mk (𝟙 X)) := Over.mkIdTerminal.hom_ext _ _
  have hu' : (pullbackSectionsFunctor F).map q.op u₀ = s :=
    (congrArg (fun k : Over.mk f ⟶ Over.mk (𝟙 X) =>
      (pullbackSectionsFunctor F).map k.op u₀) hq).trans hu
  refine ⟨e.hom u₀, ?_, ?_⟩
  · exact (hmap (e.hom u₀)).symm.trans
      ((congrArg ((pullbackSectionsFunctor F).map q.op)
        (ConcreteCategory.congr_hom e.hom_inv_id u₀)).trans hu')
  · intro t ht
    have he : e.inv t = u₀ := huniq (e.inv t) (by
      rw [← hq]
      exact (hmap t).trans ht)
    have h := congrArg e.hom he
    simpa only [Iso.inv_hom_id_apply] using h

end AlgebraicGeometry.Scheme.EtaleCohomology
