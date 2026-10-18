/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Connectedness
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! Actual terminal objects, pullbacks and finite coproducts of finite-etale
covers. All universal properties are constructed without Galois hypotheses. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (mk)

universe u
variable {X : Scheme.{u}}

/-- The identity morphism of `X` , regarded as a finite étale scheme over `X` . -/
abbrev terminalCover (X : Scheme.{u}) : Scheme.FiniteEtale X := mk (𝟙 X)

/-- The terminal-object structure on the identity cover, with maps given by structural
morphisms. -/
def terminalCoverIsTerminal (X : Scheme.{u}) : IsTerminal (terminalCover X) :=
  .ofUniqueHom
    (fun Y => ObjectProperty.homMk (Over.homMk Y.obj.hom (by simp)))
    (fun Y f => by
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change f.hom.left = Y.obj.hom
      have h := Over.w f.hom
      change f.hom.left ≫ (𝟙 X) = Y.obj.hom at h
      erw [Category.comp_id] at h
      exact h)

instance instHasTerminalCover (X : Scheme.{u}) : HasTerminal (Scheme.FiniteEtale X) :=
  (terminalCoverIsTerminal X).hasTerminal

attribute [local instance]
  Scheme.FiniteEtale.Connectedness.hom_isFinite
  Scheme.FiniteEtale.Connectedness.hom_etale

variable {Y Z W : Scheme.FiniteEtale X} (f : Y ⟶ W) (g : Z ⟶ W)

/-- The scheme pullback of `f` and `g` , with structural map through `Y` , as a finite étale
cover. -/
abbrev pullbackCover : Scheme.FiniteEtale X :=
  mk (pullback.fst f.hom.left g.hom.left ≫ Y.obj.hom)

/-- The first projection from the pullback cover of `f` and `g` to `Y` . -/
def pullbackCoverFst : pullbackCover f g ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (pullback.fst f.hom.left g.hom.left) rfl)

/-- The second projection from the pullback cover of `f` and `g` to `Z` . -/
def pullbackCoverSnd : pullbackCover f g ⟶ Z :=
  ObjectProperty.homMk (Over.homMk (pullback.snd f.hom.left g.hom.left) (by
    change pullback.snd f.hom.left g.hom.left ≫ Z.obj.hom =
      pullback.fst f.hom.left g.hom.left ≫ Y.obj.hom
    rw [← Over.w f.hom, ← Over.w g.hom]
    simp only [← Category.assoc, pullback.condition]))

theorem pullbackCover_condition :
    pullbackCoverFst f g ≫ f = pullbackCoverSnd f g ≫ g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.condition

/-- The pullback cone on `f` and `g` formed by the two scheme pullback projections. -/
def pullbackCoverCone : PullbackCone f g :=
  PullbackCone.mk (pullbackCoverFst f g) (pullbackCoverSnd f g)
    (pullbackCover_condition f g)

/-- The map from a pullback cone vertex to the pullback cover, induced by its two legs. -/
def pullbackCoverLift (s : PullbackCone f g) : s.pt ⟶ pullbackCover f g :=
  ObjectProperty.homMk (Over.homMk
    (pullback.lift s.fst.hom.left s.snd.hom.left
      (congrArg (fun k => k.hom.left) s.condition)) (by
        change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ Y.obj.hom = s.pt.obj.hom
        rw [pullback.lift_fst_assoc, Over.w]))

@[reassoc] theorem pullbackCoverLift_fst (s : PullbackCone f g) :
    pullbackCoverLift f g s ≫ pullbackCoverFst f g = s.fst := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[reassoc] theorem pullbackCoverLift_snd (s : PullbackCone f g) :
    pullbackCoverLift f g s ≫ pullbackCoverSnd f g = s.snd := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- The universal property of the pullback cover cone in finite étale schemes over `X` . -/
def pullbackCoverIsLimit : IsLimit (pullbackCoverCone f g) :=
  PullbackCone.IsLimit.mk (pullbackCover_condition f g) (pullbackCoverLift f g)
    (pullbackCoverLift_fst f g) (pullbackCoverLift_snd f g) (by
      intro s m hm₁ hm₂
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change m.hom.left ≫ pullback.fst f.hom.left g.hom.left =
          pullback.lift s.fst.hom.left s.snd.hom.left _ ≫ pullback.fst f.hom.left g.hom.left
        rw [pullback.lift_fst]
        exact congrArg (fun k => k.hom.left) hm₁
      · change m.hom.left ≫ pullback.snd f.hom.left g.hom.left =
          pullback.lift s.fst.hom.left s.snd.hom.left _ ≫ pullback.snd f.hom.left g.hom.left
        rw [pullback.lift_snd]
        exact congrArg (fun k => k.hom.left) hm₂)

instance instHasPullbackCover : HasPullback f g :=
  HasLimit.mk ⟨pullbackCoverCone f g, pullbackCoverIsLimit f g⟩

instance instHasPullbacksCover (X : Scheme.{u}) : HasPullbacks (Scheme.FiniteEtale X) :=
  hasPullbacks_of_hasLimit_cospan (Scheme.FiniteEtale X)

instance instHasFiniteLimitsCover (X : Scheme.{u}) : HasFiniteLimits (Scheme.FiniteEtale X) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The initial-object structure on the empty finite étale scheme over `X` . -/
def emptyCoverIsInitial (X : Scheme.{u}) :
    IsInitial (Scheme.FiniteEtale.Connectedness.emptyCover X) := by
  have : IsEmpty (Scheme.FiniteEtale.Connectedness.emptyCover X).obj.left := by
    change IsEmpty (∅ : Scheme.{u})
    infer_instance
  exact Scheme.FiniteEtale.Connectedness.isInitialCoverOfIsEmpty _

instance instHasInitialCover (X : Scheme.{u}) : HasInitial (Scheme.FiniteEtale X) :=
  (emptyCoverIsInitial X).hasInitial

theorem etale_coprodDesc {A B S : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
    [Etale a] [Etale b] : Etale (coprod.desc a b) := by
  let : IsZariskiLocalAtSource (@Etale.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource (@Etale.{u}) (@RingHom.Etale.{u})
      Etale.instHasRingHomPropertyEtale
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) (coprodOpenCover.{u, 0} A B)
  intro i
  cases i with
  | inl i => simpa [coprodOpenCover] using (inferInstance : Etale a)
  | inr i => simpa [coprodOpenCover] using (inferInstance : Etale b)

variable (Y Z : Scheme.FiniteEtale X)

/-- The disjoint union of `Y` and `Z` , with its induced finite étale structural map to `X` . -/
def binaryCoproductCover : Scheme.FiniteEtale X := by
  let : Etale (coprod.desc Y.obj.hom Z.obj.hom) := etale_coprodDesc _ _
  exact mk (coprod.desc Y.obj.hom Z.obj.hom)

/-- The inclusion of `Y` into the binary coproduct cover of `Y` and `Z` . -/
def binaryCoproductInl : Y ⟶ binaryCoproductCover Y Z :=
  ObjectProperty.homMk (Over.homMk coprod.inl (coprod.inl_desc _ _))

/-- The inclusion of `Z` into the binary coproduct cover of `Y` and `Z` . -/
def binaryCoproductInr : Z ⟶ binaryCoproductCover Y Z :=
  ObjectProperty.homMk (Over.homMk coprod.inr (coprod.inr_desc _ _))

/-- The binary cofan formed by the inclusions into the disjoint union cover. -/
def binaryCoproductCofan : BinaryCofan Y Z :=
  BinaryCofan.mk (binaryCoproductInl Y Z) (binaryCoproductInr Y Z)

/-- The map from the disjoint union cover to `T` induced by `a : Y ⟶ T` and `b : Z ⟶ T` . -/
def binaryCoproductDesc {T : Scheme.FiniteEtale X} (a : Y ⟶ T) (b : Z ⟶ T) :
    binaryCoproductCover Y Z ⟶ T :=
  ObjectProperty.homMk (Over.homMk (coprod.desc a.hom.left b.hom.left) (by
    change coprod.desc a.hom.left b.hom.left ≫ T.obj.hom = coprod.desc Y.obj.hom Z.obj.hom
    apply coprod.hom_ext
    · simp only [coprod.inl_desc_assoc, coprod.inl_desc, Over.w]
    · simp only [coprod.inr_desc_assoc, coprod.inr_desc, Over.w]))

@[reassoc] theorem binaryCoproductInl_desc {T : Scheme.FiniteEtale X} (a : Y ⟶ T) (b : Z ⟶ T) :
    binaryCoproductInl Y Z ≫ binaryCoproductDesc Y Z a b = a := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact coprod.inl_desc _ _

@[reassoc] theorem binaryCoproductInr_desc {T : Scheme.FiniteEtale X} (a : Y ⟶ T) (b : Z ⟶ T) :
    binaryCoproductInr Y Z ≫ binaryCoproductDesc Y Z a b = b := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact coprod.inr_desc _ _

/-- The universal property of the disjoint union cofan in finite étale schemes over `X` . -/
def binaryCoproductIsColimit : IsColimit (binaryCoproductCofan Y Z) :=
  BinaryCofan.IsColimit.mk _ (binaryCoproductDesc Y Z)
    (binaryCoproductInl_desc Y Z) (binaryCoproductInr_desc Y Z) (by
      intro T a b m hm₁ hm₂
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      apply coprod.hom_ext
      · change (coprod.inl : Y.obj.left ⟶ Y.obj.left ⨿ Z.obj.left) ≫ m.hom.left =
          coprod.inl ≫ coprod.desc a.hom.left b.hom.left
        rw [coprod.inl_desc]
        exact congrArg (fun k => k.hom.left) hm₁
      · change (coprod.inr : Z.obj.left ⟶ Y.obj.left ⨿ Z.obj.left) ≫ m.hom.left =
          coprod.inr ≫ coprod.desc a.hom.left b.hom.left
        rw [coprod.inr_desc]
        exact congrArg (fun k => k.hom.left) hm₂)

instance instHasBinaryCoproductCover : HasBinaryCoproduct Y Z :=
  HasColimit.mk ⟨binaryCoproductCofan Y Z, binaryCoproductIsColimit Y Z⟩

instance instHasBinaryCoproductsCover (X : Scheme.{u}) : HasBinaryCoproducts
    (Scheme.FiniteEtale X) :=
  hasBinaryCoproducts_of_hasColimit_pair (Scheme.FiniteEtale X)

instance instHasFiniteCoproductsCover (X : Scheme.{u}) : HasFiniteCoproducts
    (Scheme.FiniteEtale X) :=
  hasFiniteCoproducts_of_has_binary_and_initial

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ea8418ceec7505d8b96a7096a1fe0f6d04b6afa48c8de0ea55e1a1f3563ac505.
Definitions, hypotheses and universes are retained modulo native names. -/
