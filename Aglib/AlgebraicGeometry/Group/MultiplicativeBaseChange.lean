/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.RootsFiniteEtale
/-!
# Actual multiplicative group and roots-of-unity base change

For every scheme morphism `f : S ⟶ X`, this module constructs genuine
isomorphisms in `Grp (Over S)` from `(Over.pullback f).mapGrp` applied to the
fixed multiplicative group and roots group over X to those over S.
The roots comparison works at every natural level, including zero.

The proof first equips the actual Over.map/Over.pullback adjunction on
sections with its multiplicative equivalence. It then applies fully faithful
group-valued Yoneda to the literal unit/root coordinate comparisons. Thus
the isomorphisms respect multiplication, identity, and inversion of the
already constructed group objects. They do not merely identify schemes.

The section formulas identify base change with pullback of the actual global
unit. Identity and composition coherence are proved on the underlying Over
arrows using canonical pullback projections; these arrows determine the
group morphisms faithfully. No standard theorem premise is retained.

Consumer boundary: for positive invertible n, `RootsFiniteEtale` supplies the
étale hypothesis required to use A's represented-sheaf inverse-image
comparison for μ_n. The group-scheme comparison for Gm does not assert an
inverse-image isomorphism for the small-étale Gm sheaf under arbitrary base
change. This module imports neither Cohomology nor Curves.

Mathematical source: `K2-018#lem:k2018-geometric-exact-order`, at source
revision `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Read-only `MultiplicativeGroup.lean` SHA-256:
`00d2f93b8d66e0059bf60def78b7ace6d0420906d1aa114a62daca46972179ea`.
Read-only `RootsFiniteEtale.lean` SHA-256:
`2e7f1464a9906715d3bed4f4ff162c10268e9737d457960f1bb1ff2f3976821a`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj
namespace AlgebraicGeometry.Scheme.Group.MultiplicativeBaseChange
universe u
variable {X S T : Scheme.{u}}

/-- The group object over `S` obtained by pulling back a group object over `X` along `f`. -/
abbrev baseChangedGroup (f : S ⟶ X) (H : Grp (Over X)) : Grp (Over S) :=
  (Over.pullback f).mapGrp.obj H

@[simp] theorem pullbackAdj_symm_left (f : S ⟶ X) (U : Over S) (V : Over X)
    (a : U ⟶ (Over.pullback f).obj V) :
    (((Over.mapPullbackAdj f).homEquiv U V).symm a).left =
      a.left ≫ pullback.fst V.hom f := rfl

/-- The pullback adjunction preserves the actual multiplication on sections. -/
def pullbackSectionsEquiv (f : S ⟶ X) (H : Grp (Over X)) (U : Over S) :
    (U ⟶ (baseChangedGroup f H).X) ≃* ((Over.map f).obj U ⟶ H.X) where
  toEquiv := (Over.mapPullbackAdj f).homEquiv U H.X |>.symm
  map_mul' a b := by
    apply Over.OverMorphism.ext
    change (lift a b).left ≫ (Functor.LaxMonoidal.μ (Over.pullback f) H.X H.X).left ≫
      ((Over.pullback f).map μ[H.X]).left ≫ pullback.fst H.X.hom f =
      (lift (((Over.mapPullbackAdj f).homEquiv U H.X).symm a)
        (((Over.mapPullbackAdj f).homEquiv U H.X).symm b)).left ≫ μ[H.X].left
    simp only [Over.pullback_map_left, pullback.lift_fst]
    simp only [← Category.assoc]
    apply congrArg (fun k : U.left ⟶ (H.X ⊗ H.X).left => k ≫ μ[H.X].left)
    apply pullback.hom_ext
    · have hm := congrArg (fun k => (lift a b).left ≫ k)
        (Over.μ_pullback_left_fst_fst (f := f) H.X H.X)
      simpa [Over.lift_left, Category.assoc] using hm
    · have hm := congrArg (fun k => (lift a b).left ≫ k)
        (Over.μ_pullback_left_fst_snd (f := f) H.X H.X)
      simpa [Over.lift_left, Category.assoc] using hm

/-- Unit coordinates are multiplicative for the actual represented group. -/
def unitsSectionsEquiv (X : Scheme.{u}) (U : Over X) :
    (U ⟶ (MultiplicativeGroup.groupScheme X).X) ≃* Γ(U.left, ⊤)ˣ where
  toEquiv := MultiplicativeGroup.sectionsUnitsEquiv X U
  map_mul' := MultiplicativeGroup.sectionsUnitsEquiv_mul X U

/-- Root coordinates are multiplicative for the actual represented group. -/
def rootsSectionsEquiv (X : Scheme.{u}) (n : ℕ) (U : Over X) :
    (U ⟶ (MultiplicativeGroup.rootsGroupScheme X n).X) ≃* rootsOfUnity n Γ(U.left, ⊤) where
  toEquiv := MultiplicativeGroup.rootsHomEquiv X n U
  map_mul' a b := by
    let := MultiplicativeGroup.rootsCommGroup X n
    exact ((yonedaMonObjIsoOfRepresentableBy (MultiplicativeGroup.rootsScheme X n)
      (MultiplicativeGroup.rootsFunctor X n ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat)
      (MultiplicativeGroup.rootsRepresentable X n)).hom.app (op U)).hom.map_mul a b


theorem pullbackSectionsEquiv_naturality (f : S ⟶ X) (H : Grp (Over X))
    {U V : Over S} (h : U ⟶ V) (a : V ⟶ (baseChangedGroup f H).X) :
    pullbackSectionsEquiv f H U (h ≫ a) =
      (Over.map f).map h ≫ pullbackSectionsEquiv f H V a := by
  exact (Over.mapPullbackAdj f).homEquiv_naturality_left_symm h a

/-- Pullback Gm sections retain their literal unit coordinate. -/
def pullbackUnitsEquiv (f : S ⟶ X) (U : Over S) :
    (U ⟶ (baseChangedGroup f (MultiplicativeGroup.groupScheme X)).X) ≃* Γ(U.left, ⊤)ˣ :=
  (pullbackSectionsEquiv f _ U).trans (unitsSectionsEquiv X ((Over.map f).obj U))

/-- Pullback μ_n sections retain their literal root coordinate, for every n. -/
def pullbackRootsEquiv (f : S ⟶ X) (n : ℕ) (U : Over S) :
    (U ⟶ (baseChangedGroup f (MultiplicativeGroup.rootsGroupScheme X n)).X) ≃*
      rootsOfUnity n Γ(U.left, ⊤) :=
  (pullbackSectionsEquiv f _ U).trans (rootsSectionsEquiv X n ((Over.map f).obj U))

/-- The multiplicative equivalence comparing sections of the base-changed multiplicative group
with sections of the multiplicative group over `S`. -/
def unitsComparisonEquiv (f : S ⟶ X) (U : Over S) :
    (U ⟶ (baseChangedGroup f (MultiplicativeGroup.groupScheme X)).X) ≃*
      (U ⟶ (MultiplicativeGroup.groupScheme S).X) :=
  (pullbackUnitsEquiv f U).trans (unitsSectionsEquiv S U).symm

/-- The multiplicative equivalence comparing sections of base-changed roots of unity with
roots-of-unity sections over `S`. -/
def rootsComparisonEquiv (f : S ⟶ X) (n : ℕ) (U : Over S) :
    (U ⟶ (baseChangedGroup f (MultiplicativeGroup.rootsGroupScheme X n)).X) ≃*
      (U ⟶ (MultiplicativeGroup.rootsGroupScheme S n).X) :=
  (pullbackRootsEquiv f n U).trans (rootsSectionsEquiv S n U).symm

theorem unitsComparisonEquiv_naturality (f : S ⟶ X) {U V : Over S}
    (h : U ⟶ V) (a : V ⟶ (baseChangedGroup f (MultiplicativeGroup.groupScheme X)).X) :
    unitsComparisonEquiv f U (h ≫ a) = h ≫ unitsComparisonEquiv f V a := by
  change (MultiplicativeGroup.unitsRepresentable S).homEquiv.symm
      (pullbackUnitsEquiv f U (h ≫ a)) =
    h ≫ (MultiplicativeGroup.unitsRepresentable S).homEquiv.symm (pullbackUnitsEquiv f V a)
  rw [(MultiplicativeGroup.unitsRepresentable S).comp_homEquiv_symm]
  congr 1

theorem rootsComparisonEquiv_naturality (f : S ⟶ X) (n : ℕ) {U V : Over S}
    (h : U ⟶ V) (a : V ⟶ (baseChangedGroup f (MultiplicativeGroup.rootsGroupScheme X n)).X) :
    rootsComparisonEquiv f n U (h ≫ a) = h ≫ rootsComparisonEquiv f n V a := by
  change (MultiplicativeGroup.rootsRepresentable S n).homEquiv.symm
      (pullbackRootsEquiv f n U (h ≫ a)) =
    h ≫ (MultiplicativeGroup.rootsRepresentable S n).homEquiv.symm (pullbackRootsEquiv f n V a)
  rw [(MultiplicativeGroup.rootsRepresentable S n).comp_homEquiv_symm]
  congr 1

/-- A natural multiplicative section equivalence induces a genuine group-object isomorphism. -/
def groupYonedaIsoOfSections (H K : Grp (Over S))
    (e : ∀ U : Over S, (U ⟶ H.X) ≃* (U ⟶ K.X))
    (he : ∀ {U V : Over S} (h : U ⟶ V) (a : V ⟶ H.X), e U (h ≫ a) = h ≫ e V a) :
    yonedaGrp.obj H ≅ yonedaGrp.obj K :=
  NatIso.ofComponents (fun U => (e U.unop).toGrpIso) (by
    intro U V h
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact he h.unop a)

/-- The group-object isomorphism induced by a natural family of multiplicative equivalences on
all test-scheme sections. -/
def groupIsoOfSections (H K : Grp (Over S))
    (e : ∀ U : Over S, (U ⟶ H.X) ≃* (U ⟶ K.X))
    (he : ∀ {U V : Over S} (h : U ⟶ V) (a : V ⟶ H.X), e U (h ≫ a) = h ≫ e V a) :
    H ≅ K :=
  yonedaGrpFullyFaithful.preimageIso (groupYonedaIsoOfSections H K e he)

theorem groupIsoOfSections_hom (H K : Grp (Over S))
    (e : ∀ U : Over S, (U ⟶ H.X) ≃* (U ⟶ K.X))
    (he : ∀ {U V : Over S} (h : U ⟶ V) (a : V ⟶ H.X), e U (h ≫ a) = h ≫ e V a)
    (U : Over S) (a : U ⟶ H.X) :
    a ≫ (groupIsoOfSections H K e he).hom.hom.hom = e U a := by
  have h := yonedaGrpFullyFaithful.map_preimage (groupYonedaIsoOfSections H K e he).hom
  exact congrArg (fun q => (q.app (op U)).hom a) h

/-- Canonical actual Gm base change in the category of group objects. -/
def unitsBaseChangeIso (f : S ⟶ X) :
    baseChangedGroup f (MultiplicativeGroup.groupScheme X) ≅ MultiplicativeGroup.groupScheme S :=
  groupIsoOfSections _ _ (unitsComparisonEquiv f) (unitsComparisonEquiv_naturality f)

/-- Canonical actual μ_n base change in the category of group objects, including n=0. -/
def rootsBaseChangeIso (f : S ⟶ X) (n : ℕ) :
    baseChangedGroup f (MultiplicativeGroup.rootsGroupScheme X n) ≅
      MultiplicativeGroup.rootsGroupScheme S n :=
  groupIsoOfSections _ _ (rootsComparisonEquiv f n) (rootsComparisonEquiv_naturality f n)

/-- The actual group-scheme isomorphism preserves literal unit coordinates. -/
theorem unitsBaseChangeIso_sections (f : S ⟶ X) (U : Over S)
    (a : U ⟶ (baseChangedGroup f (MultiplicativeGroup.groupScheme X)).X) :
    MultiplicativeGroup.sectionsUnitsEquiv S U (a ≫ (unitsBaseChangeIso f).hom.hom.hom) =
      MultiplicativeGroup.sectionsUnitsEquiv X ((Over.map f).obj U)
        ((Over.mapPullbackAdj f).homEquiv U _ |>.symm <| a) := by
  rw [show a ≫ (unitsBaseChangeIso f).hom.hom.hom = unitsComparisonEquiv f U a from
    groupIsoOfSections_hom ..]
  exact (unitsSectionsEquiv S U).apply_symm_apply (pullbackUnitsEquiv f U a)

/-- The actual group-scheme isomorphism preserves literal nth-root coordinates. -/
theorem rootsBaseChangeIso_sections (f : S ⟶ X) (n : ℕ) (U : Over S)
    (a : U ⟶ (baseChangedGroup f (MultiplicativeGroup.rootsGroupScheme X n)).X) :
    MultiplicativeGroup.rootsHomEquiv S n U (a ≫ (rootsBaseChangeIso f n).hom.hom.hom) =
      MultiplicativeGroup.rootsHomEquiv X n ((Over.map f).obj U)
        ((Over.mapPullbackAdj f).homEquiv U _ |>.symm <| a) := by
  rw [show a ≫ (rootsBaseChangeIso f n).hom.hom.hom = rootsComparisonEquiv f n U a from
    groupIsoOfSections_hom ..]
  exact (rootsSectionsEquiv S n U).apply_symm_apply (pullbackRootsEquiv f n U a)


/-- Adjunction turns a pulled-back section into composition with the pullback projection. -/
theorem pullbackSectionsEquiv_map (f : S ⟶ X) (H : Grp (Over X)) (U : Over X)
    (a : U ⟶ H.X) :
    pullbackSectionsEquiv f H ((Over.pullback f).obj U) ((Over.pullback f).map a) =
      (Over.mapPullbackAdj f).counit.app U ≫ a := by
  apply Over.OverMorphism.ext
  change ((Over.pullback f).map a).left ≫ pullback.fst H.X.hom f =
    pullback.fst U.hom f ≫ a.left
  simp

/-- Base changing a Gm section pulls back precisely its invertible global function. -/
theorem unitsBaseChangeIso_pullback (f : S ⟶ X) (U : Over X)
    (a : U ⟶ MultiplicativeGroup.scheme X) :
    MultiplicativeGroup.sectionsUnitsEquiv S ((Over.pullback f).obj U)
      ((Over.pullback f).map a ≫ (unitsBaseChangeIso f).hom.hom.hom) =
    Units.map (pullback.fst U.hom f).appTop.hom.toMonoidHom
      (MultiplicativeGroup.sectionsUnitsEquiv X U a) := by
  rw [unitsBaseChangeIso_sections]
  change MultiplicativeGroup.sectionsUnitsEquiv X _
    (pullbackSectionsEquiv f (MultiplicativeGroup.groupScheme X) _ ((Over.pullback f).map a)) = _
  rw [pullbackSectionsEquiv_map]
  exact (MultiplicativeGroup.unitsRepresentable X).homEquiv_comp
    ((Over.mapPullbackAdj f).counit.app U) a

/-- Base changing a μ_n section pulls back precisely its unit, with its nth-power equation. -/
theorem rootsBaseChangeIso_pullback (f : S ⟶ X) (n : ℕ) (U : Over X)
    (a : U ⟶ MultiplicativeGroup.rootsScheme X n) :
    (MultiplicativeGroup.rootsHomEquiv S n ((Over.pullback f).obj U)
      ((Over.pullback f).map a ≫ (rootsBaseChangeIso f n).hom.hom.hom)).val =
    Units.map (pullback.fst U.hom f).appTop.hom.toMonoidHom
      (MultiplicativeGroup.rootsHomEquiv X n U a).val := by
  have h := rootsBaseChangeIso_sections f n ((Over.pullback f).obj U) ((Over.pullback f).map a)
  change MultiplicativeGroup.rootsHomEquiv S n _ _ =
    MultiplicativeGroup.rootsHomEquiv X n _
      (pullbackSectionsEquiv f (MultiplicativeGroup.rootsGroupScheme X n) _
        ((Over.pullback f).map a)) at h
  rw [pullbackSectionsEquiv_map] at h
  have h' := (MultiplicativeGroup.rootsRepresentable X n).homEquiv_comp
    ((Over.mapPullbackAdj f).counit.app U) a
  exact congrArg Subtype.val (h.trans h')


/-- The affine coordinate of a root-scheme section. -/
def rootCoordinate (X : Scheme.{u}) (n : ℕ) :
    (MultiplicativeGroup.rootsScheme X n).left ⟶ MultiplicativeGroup.affineScheme :=
  (MultiplicativeGroup.rootsInclusion X n).left ≫ Limits.prod.snd

theorem rootsHomEquiv_val (X : Scheme.{u}) (n : ℕ) (U : Over X)
    (a : U ⟶ MultiplicativeGroup.rootsScheme X n) :
    (MultiplicativeGroup.rootsHomEquiv X n U a).val =
      MultiplicativeGroup.affineHomUnits U.left (a.left ≫ rootCoordinate X n) := by
  change MultiplicativeGroup.affineHomUnits U.left
    ((a.left ≫ (MultiplicativeGroup.rootsInclusion X n).left) ≫ Limits.prod.snd) = _
  rw [Category.assoc]
  rfl

theorem unitsCoordinate_ext (X : Scheme.{u}) (U : Over X)
    {a b : U ⟶ MultiplicativeGroup.scheme X}
    (h : a.left ≫ Limits.prod.snd = b.left ≫ Limits.prod.snd) : a = b := by
  apply (MultiplicativeGroup.sectionsUnitsEquiv X U).injective
  exact congrArg (MultiplicativeGroup.affineHomUnits U.left) h

theorem rootsCoordinate_ext (X : Scheme.{u}) (n : ℕ) (U : Over X)
    {a b : U ⟶ MultiplicativeGroup.rootsScheme X n}
    (h : a.left ≫ rootCoordinate X n = b.left ≫ rootCoordinate X n) : a = b := by
  apply (MultiplicativeGroup.rootsHomEquiv X n U).injective
  apply Subtype.ext
  rw [rootsHomEquiv_val, rootsHomEquiv_val, h]

/-- The base-change isomorphism is literally the projection on the Laurent coordinate. -/
theorem unitsBaseChangeIso_coordinate (f : S ⟶ X) :
    (unitsBaseChangeIso f).hom.hom.hom.left ≫ Limits.prod.snd =
      pullback.fst (MultiplicativeGroup.scheme X).hom f ≫ Limits.prod.snd := by
  apply (MultiplicativeGroup.affineHomUnits _).injective
  have h := unitsBaseChangeIso_sections f
    ((Over.pullback f).obj (MultiplicativeGroup.scheme X)) (𝟙 _)
  change MultiplicativeGroup.affineHomUnits
      ((Over.pullback f).obj (MultiplicativeGroup.scheme X)).left
      (((𝟙 ((Over.pullback f).obj (MultiplicativeGroup.scheme X))) ≫
        (unitsBaseChangeIso f).hom.hom.hom).left ≫ Limits.prod.snd) =
    MultiplicativeGroup.affineHomUnits
      ((Over.pullback f).obj (MultiplicativeGroup.scheme X)).left
      ((((Over.mapPullbackAdj f).homEquiv _ (MultiplicativeGroup.scheme X)).symm
        (𝟙 ((Over.pullback f).obj (MultiplicativeGroup.scheme X)))).left ≫ Limits.prod.snd) at h
  simp only [Category.id_comp, pullbackAdj_symm_left, Over.id_left] at h
  exact h

/-- The root base-change isomorphism is literally the projection on the root coordinate. -/
theorem rootsBaseChangeIso_coordinate (f : S ⟶ X) (n : ℕ) :
    (rootsBaseChangeIso f n).hom.hom.hom.left ≫ rootCoordinate S n =
      pullback.fst (MultiplicativeGroup.rootsScheme X n).hom f ≫ rootCoordinate X n := by
  apply (MultiplicativeGroup.affineHomUnits _).injective
  have h := congrArg Subtype.val (rootsBaseChangeIso_sections f n
    ((Over.pullback f).obj (MultiplicativeGroup.rootsScheme X n)) (𝟙 _))
  rw [rootsHomEquiv_val, rootsHomEquiv_val] at h
  simp only [Category.id_comp, pullbackAdj_symm_left, Over.id_left] at h
  exact h

/-- The usual projection identifying a pullback along the identity. -/
def pullbackIdProjection (V : Over X) : (Over.pullback (𝟙 X)).obj V ⟶ V :=
  Over.homMk (pullback.fst V.hom (𝟙 X)) (by simpa using pullback.condition (f := V.hom) (g := 𝟙 X))

/-- Gm base change along the identity is the canonical pullback projection. -/
theorem unitsBaseChangeIso_id (X : Scheme.{u}) :
    (unitsBaseChangeIso (𝟙 X)).hom.hom.hom = pullbackIdProjection (MultiplicativeGroup.scheme X) :=
      by
  apply unitsCoordinate_ext
  rw [unitsBaseChangeIso_coordinate]
  rfl

/-- μ_n base change along the identity is the canonical pullback projection. -/
theorem rootsBaseChangeIso_id (X : Scheme.{u}) (n : ℕ) :
    (rootsBaseChangeIso (𝟙 X) n).hom.hom.hom =
      pullbackIdProjection (MultiplicativeGroup.rootsScheme X n) := by
  apply rootsCoordinate_ext
  rw [rootsBaseChangeIso_coordinate]
  rfl

/-- The canonical comparison from an iterated pullback to pullback along the composite. -/
def pullbackComposeMap (f : S ⟶ X) (g : X ⟶ T) (V : Over T) :
    (Over.pullback f).obj ((Over.pullback g).obj V) ⟶ (Over.pullback (f ≫ g)).obj V :=
  Over.homMk
    (pullback.lift
      (pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g)
      (pullback.snd ((Over.pullback g).obj V).hom f)
      (by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        change (pullback.fst (pullback.snd V.hom g) f ≫ pullback.snd V.hom g) ≫ g = _
        rw [pullback.condition, Category.assoc]
        rfl))
    (by simp)

/-- Composition coherence of the actual Gm group isomorphisms, on their underlying arrows. -/
theorem unitsBaseChangeIso_comp (f : S ⟶ X) (g : X ⟶ T) :
    (Over.pullback f).map (unitsBaseChangeIso g).hom.hom.hom ≫
        (unitsBaseChangeIso f).hom.hom.hom =
      pullbackComposeMap f g (MultiplicativeGroup.scheme T) ≫
        (unitsBaseChangeIso (f ≫ g)).hom.hom.hom := by
  apply unitsCoordinate_ext
  simp only [Over.comp_left, Category.assoc, unitsBaseChangeIso_coordinate,
    Over.pullback_map_left]
  erw [pullback.lift_fst_assoc]
  rw [Category.assoc]
  erw [unitsBaseChangeIso_coordinate g]
  simp [pullbackComposeMap, Category.assoc]
  rfl

/-- Composition coherence of the actual μ_n group isomorphisms, on their underlying arrows. -/
theorem rootsBaseChangeIso_comp (f : S ⟶ X) (g : X ⟶ T) (n : ℕ) :
    (Over.pullback f).map (rootsBaseChangeIso g n).hom.hom.hom ≫
        (rootsBaseChangeIso f n).hom.hom.hom =
      pullbackComposeMap f g (MultiplicativeGroup.rootsScheme T n) ≫
        (rootsBaseChangeIso (f ≫ g) n).hom.hom.hom := by
  apply rootsCoordinate_ext
  simp only [Over.comp_left, Category.assoc, rootsBaseChangeIso_coordinate,
    Over.pullback_map_left]
  erw [pullback.lift_fst_assoc]
  rw [Category.assoc]
  erw [rootsBaseChangeIso_coordinate g n]
  simp [pullbackComposeMap, Category.assoc]
  rfl

end AlgebraicGeometry.Scheme.Group.MultiplicativeBaseChange
