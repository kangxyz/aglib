/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverCoproductPreservation
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverConstant
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Mathlib.CategoryTheory.Extensive

/-! Actual finite trivial covers commute with arbitrary scheme base change.
The proof uses the universal finite coproduct of schemes. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange forget forgetToScheme)

universe u

/-- The section of the base-changed trivial cover indexed by `a`, defined by the
pullback lift of `f ≫ (trivialCoverι X A a).hom.left` and `𝟙 S`. -/
def trivialCoverBaseChangeSection {X S : Scheme.{u}} (f : S ⟶ X)
    (A : Type u) [Finite A] (a : A) :
    terminalCover S ⟶ (baseChange f).obj (trivialCover X A) := by
  refine ObjectProperty.homMk ?_
  change Over.mk (𝟙 S) ⟶ Over.mk (pullback.snd (trivialCover X A).obj.hom f)
  exact Over.homMk
    (pullback.lift (f ≫ (trivialCoverι X A a).hom.left) (𝟙 S)
      (by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun g : X ⟶ X => f ≫ g) (trivialCoverι_struct X A a)).trans
            ((Category.comp_id f).trans (Category.id_comp f).symm))))
    (pullback.lift_snd _ _ _)

/-- The morphism from the trivial cover over `S` to the base change of the trivial
cover over `X`, assembled from the label-indexed pullback sections. -/
def trivialCoverBaseChangeMap {X S : Scheme.{u}} (f : S ⟶ X) (A : Type u) [Finite A] :
    trivialCover S A ⟶ (baseChange f).obj (trivialCover X A) :=
  Sigma.desc (fun a => trivialCoverBaseChangeSection f A a)

@[reassoc] theorem trivialCoverι_baseChangeMap {X S : Scheme.{u}} (f : S ⟶ X)
    (A : Type u) [Finite A] (a : A) :
    trivialCoverι S A a ≫ trivialCoverBaseChangeMap f A = trivialCoverBaseChangeSection f A a :=
  Sigma.ι_comp_desc _ _

/-- The coproduct colimit structure on the underlying scheme of the base-changed
trivial cover, with legs `trivialCoverBaseChangeSection f A a`. -/
def trivialCoverBaseChangeSchemeIsColimit {X S : Scheme.{u}} (f : S ⟶ X)
    (A : Type u) [Finite A] :
    IsColimit (Cofan.mk (((baseChange f).obj (trivialCover X A)).obj.left)
      (fun a => (trivialCoverBaseChangeSection f A a).hom.left)) := by
  have hu : IsUniversalColimit (Cofan.mk (trivialCover X A).obj.left
      (fun a => (trivialCoverι X A a).hom.left)) :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts
      (isColimitOfHasCoproductOfPreservesColimit (forgetToScheme X)
        (fun _ : A => terminalCover X))
  let d := Cofan.mk (((baseChange f).obj (trivialCover X A)).obj.left)
    (fun a => (trivialCoverBaseChangeSection f A a).hom.left)
  exact (hu.nonempty_isColimit_of_pullbackCone_right (fun _ : A => 𝟙 X)
    (trivialCover X A).obj.hom f
    (fun _ => (IsPullback.id_vert f).cone)
    (fun _ => (IsPullback.id_vert f).isLimit)
    (pullback.cone (trivialCover X A).obj.hom f)
    (pullback.isLimit (trivialCover X A).obj.hom f) d (Iso.refl _)
    (fun a => trivialCoverι_struct X A a)
    (fun a => by
      change (trivialCoverBaseChangeSection f A a).hom.left ≫ 𝟙 _ ≫
        pullback.fst (trivialCover X A).obj.hom f = f ≫ (trivialCoverι X A a).hom.left
      exact (congrArg
        (fun g : pullback (trivialCover X A).obj.hom f ⟶ (trivialCover X A).obj.left =>
          (trivialCoverBaseChangeSection f A a).hom.left ≫ g)
        (Category.id_comp (pullback.fst (trivialCover X A).obj.hom f))).trans
        (pullback.lift_fst _ _ _))
    (fun a => by
      change (trivialCoverBaseChangeSection f A a).hom.left ≫ 𝟙 _ ≫
        pullback.snd (trivialCover X A).obj.hom f = 𝟙 S
      exact (congrArg
        (fun g : pullback (trivialCover X A).obj.hom f ⟶ S =>
          (trivialCoverBaseChangeSection f A a).hom.left ≫ g)
        (Category.id_comp (pullback.snd (trivialCover X A).obj.hom f))).trans
        (pullback.lift_snd _ _ _))).some

instance trivialCoverBaseChangeMap_isIso {X S : Scheme.{u}} (f : S ⟶ X)
    (A : Type u) [Finite A] : IsIso (trivialCoverBaseChangeMap f A) := by
  let d := Cofan.mk (((baseChange f).obj (trivialCover X A)).obj.left)
    (fun a => (trivialCoverBaseChangeSection f A a).hom.left)
  let hsource := isColimitOfHasCoproductOfPreservesColimit (forgetToScheme S)
    (fun _ : A => terminalCover S)
  have hd : IsColimit d := trivialCoverBaseChangeSchemeIsColimit f A
  have hi : IsIso (hsource.desc d) := by
    change IsIso (hsource.coconePointUniqueUpToIso hd).hom
    infer_instance
  have hleft : (trivialCoverBaseChangeMap f A).hom.left = hsource.desc d := by
    apply hsource.hom_ext
    intro a
    have hc := congrArg
      (fun g : terminalCover S ⟶ (baseChange f).obj (trivialCover X A) => g.hom.left)
      (trivialCoverι_baseChangeMap f A a.as)
    exact hc.trans (hsource.fac d a).symm
  have : IsIso ((Over.forget S).map (trivialCoverBaseChangeMap f A).hom) := by
    change IsIso (trivialCoverBaseChangeMap f A).hom.left
    rw [hleft]
    exact hi
  have : IsIso ((forget S).map (trivialCoverBaseChangeMap f A)) :=
    isIso_of_reflects_iso (trivialCoverBaseChangeMap f A).hom (Over.forget S)
  exact isIso_of_reflects_iso (trivialCoverBaseChangeMap f A) (forget S)

/-- The isomorphism from the trivial cover over `S` to the base change along `f`
of the trivial cover over `X`, induced by its label-indexed sections. -/
def trivialCoverBaseChangeIso {X S : Scheme.{u}} (f : S ⟶ X) (A : Type u) [Finite A] :
    trivialCover S A ≅ (baseChange f).obj (trivialCover X A) :=
  asIso (trivialCoverBaseChangeMap f A)

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 b5643f5dc3b66b52598075909a8875ff83ea56f4ecdf9fdb5c1514bae82f2f99.
Definitions, hypotheses and universes are retained modulo native names. -/
