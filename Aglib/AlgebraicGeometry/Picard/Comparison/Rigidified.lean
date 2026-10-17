/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Normalized
public import Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms
public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Pushforward

/-!
# Rigidified line bundles and the normalized Picard functor

Let `p : X ⟶ S` be a morphism of schemes with a section `o`, `o ≫ p = 𝟙 S`, and write
`o_T = originSection p o ho T : T ⟶ X ×_S T` for an `S`-scheme `T`. A *rigidified pair*
`RigidifiedPair p o ho T` is a line bundle `L` on `X ×_S T` together with an isomorphism
`α : o_T^* L ≅ O_T` of module sheaves on `T`. An isomorphism of pairs
(`RigidifiedPair.Iso`) is an isomorphism `φ : L ≅ L'` with `o_T^* φ ≫ α' = α`.
`rigidifiedPicardFunctor p o ho : (Over S)ᵒᵖ ⥤ Type (u + 1)` sends `T` to the isomorphism
classes of pairs; its maps pull back the bundle along `X ×_S T' ⟶ X ×_S T` and the
rigidification along `T' ⟶ T`, through Mathlib's pullback-composition isomorphisms and
`pullbackUnitIso` (`RigidifiedPair.map`). The rigidified functor is Kleiman's
(*The Picard scheme*, arXiv:math/0504020v1, Def. 2.8, p. 19) and that of
[Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N).

* **Lemma 2.9** (Kleiman, p. 19). Two pairs whose bundles are isomorphic are isomorphic
  (`RigidifiedPair.isoOfBundleIso`): the two rigidifications differ by a unit of `Γ(T, ⊤)`,
  and multiplying the bundle isomorphism by the pullback of that unit corrects it, because
  `o_T` is a section of `X ×_S T ⟶ T`. Hence forgetting the rigidification is a natural
  bijection onto `ker(o_T^*)` (`rigidifiedClass_bijective`), and
  `rigidifiedNormalizedIso : rigidifiedPicardFunctor p o ho ≅
  normalizedPicardFunctor p o ho ⋙ forget AddCommGrpCat`. Only the section is used.
* **Lemma 2.10** (Kleiman, p. 19). If the structure map `O_T ⟶ (X ×_S T ⟶ T)_* O` is an
  isomorphism (`IsIso (pullback.snd p T.hom).c`), isomorphisms of pairs over `T` are unique
  (`RigidifiedPair.Iso.eq_of_isIso_c`); in particular every automorphism of a pair is the
  identity (`RigidifiedPair.Iso.eq_refl_of_isIso_c`). Under the hypotheses of universal
  O-connectedness (`S` locally Noetherian, `p` proper, flat, geometrically integral) this
  holds over every `S`-scheme
  (`RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral`).

The functor laws and the well-definedness of the maps follow from Lemma 2.9, so no
coherence of the pullback pseudofunctor is used. The rigidified functor takes values in types
and carries no group structure here; `rigidifiedNormalizedIso` is a natural bijection, along
which the group structure of `normalizedPicardFunctor` could be transported.
`RigidifiedPair.Iso.map` pulls isomorphisms of pairs back along morphisms of `S`-schemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules Scheme.Modules.Invertible

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- A rigidified line bundle on `X ×_S T`: a line bundle `L` with an isomorphism
`o_T^* L ≅ O_T` along the origin section (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Def. 2.8, p. 19; Kleiman's `u : O_T ≅ o_T^* L` is the inverse of
`rigidification`). -/
structure RigidifiedPair (T : Over S) : Type (u + 1) where
  /-- The line bundle on `X ×_S T`. -/
  bundle : LineBundle (pullback p T.hom)
  /-- The rigidification along the origin section. -/
  rigidification : (Scheme.Modules.pullback (originSection p o ho T)).obj bundle.val ≅
    (SheafOfModules.unit T.left.ringCatSheaf : T.left.Modules)

namespace RigidifiedPair

variable {p o ho} {T : Over S}

/-- An isomorphism of rigidified pairs: an isomorphism of line bundles `φ` with
`o_T^* φ ≫ α' = α`. -/
structure Iso (P Q : RigidifiedPair p o ho T) : Type u where
  /-- The isomorphism of line bundles. -/
  iso : (P.bundle.val : (pullback p T.hom).Modules) ≅ Q.bundle.val
  /-- Compatibility with the rigidifications. -/
  comm : (Scheme.Modules.pullback (originSection p o ho T)).map iso.hom ≫
    Q.rigidification.hom = P.rigidification.hom

theorem Iso.ext' {P Q : RigidifiedPair p o ho T} {φ ψ : Iso P Q} (h : φ.iso.hom = ψ.iso.hom) :
    φ = ψ := by
  cases φ
  cases ψ
  congr
  exact CategoryTheory.Iso.ext h

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- The identity isomorphism of a rigidified pair. -/
def Iso.refl (P : RigidifiedPair p o ho T) : Iso P P where
  iso := CategoryTheory.Iso.refl _
  comm := by
    rw [CategoryTheory.Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp]

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of an isomorphism of rigidified pairs. -/
def Iso.symm {P Q : RigidifiedPair p o ho T} (φ : Iso P Q) : Iso Q P where
  iso := φ.iso.symm
  comm := by
    rw [CategoryTheory.Iso.symm_hom, ← φ.comm, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      CategoryTheory.Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- The composite of isomorphisms of rigidified pairs. -/
def Iso.trans {P Q R : RigidifiedPair p o ho T} (φ : Iso P Q) (ψ : Iso Q R) : Iso P R where
  iso := φ.iso ≪≫ ψ.iso
  comm := by
    rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc, ψ.comm,
      φ.comm]

/-- Isomorphism of rigidified pairs. -/
instance setoid (T : Over S) : Setoid (RigidifiedPair p o ho T) where
  r P Q := Nonempty (Iso P Q)
  iseqv := ⟨fun P => ⟨Iso.refl P⟩, fun ⟨φ⟩ => ⟨φ.symm⟩, fun ⟨φ⟩ ⟨ψ⟩ => ⟨φ.trans ψ⟩⟩

/-- The unit of `Γ(T, ⊤)` by which two rigidifications of isomorphic line bundles differ. -/
def defect (P Q : RigidifiedPair p o ho T)
    (e : (P.bundle.val : (pullback p T.hom).Modules) ≅ Q.bundle.val) : (Γ(T.left, ⊤))ˣ :=
  unitIsoGlobalUnit (Q.rigidification.symm ≪≫
    (Scheme.Modules.pullback (originSection p o ho T)).mapIso e.symm ≪≫ P.rigidification)

theorem originSection_appTop_snd_appTop (a : Γ(T.left, ⊤)) :
    (originSection p o ho T).appTop ((pullback.snd p T.hom).appTop a) = a := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, originSection_snd, Scheme.Hom.id_appTop]
  rfl

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman, Lemma 2.9.** Two rigidified pairs whose line bundles are isomorphic are
isomorphic: correct a bundle isomorphism by the pullback of the defect unit. -/
def isoOfBundleIso (P Q : RigidifiedPair p o ho T)
    (e : (P.bundle.val : (pullback p T.hom).Modules) ≅ Q.bundle.val) : Iso P Q where
  iso := e ≪≫ globalScalarIso Q.bundle.val
    (Units.map (pullback.snd p T.hom).appTop.hom.toMonoidHom (defect P Q e))
  comm := by
    have hc : globalScalarEndomorphism _
        ((Scheme.Modules.pullback (originSection p o ho T)).obj Q.bundle.val)
          (defect P Q e : Γ(T.left, ⊤)) ≫ Q.rigidification.hom =
        Q.rigidification.hom ≫ globalScalarEndomorphism _ _ (defect P Q e : Γ(T.left, ⊤)) :=
      ((globalScalarCenter _ (defect P Q e : Γ(T.left, ⊤))).naturality Q.rigidification.hom).symm
    rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Functor.map_comp, globalScalarIso_hom,
      pullback_map_globalScalarEndomorphism, Units.coe_map]
    change _ ≫ globalScalarEndomorphism _ _ ((originSection p o ho T).appTop
      ((pullback.snd p T.hom).appTop (defect P Q e : Γ(T.left, ⊤)))) ≫ _ = _
    rw [originSection_appTop_snd_appTop, hc, defect, globalScalarEndomorphism_unitIsoGlobalUnit]
    simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.symm_hom,
      CategoryTheory.Functor.mapIso_hom, CategoryTheory.Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, CategoryTheory.Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]

theorem setoid_r_iff (P Q : RigidifiedPair p o ho T) :
    P ≈ Q ↔ Nonempty ((P.bundle.val : (pullback p T.hom).Modules) ≅ Q.bundle.val) :=
  ⟨fun ⟨φ⟩ => ⟨φ.iso⟩, fun ⟨e⟩ => ⟨isoOfBundleIso P Q e⟩⟩

theorem originSection_comp_familyScheme_map {T T' : Over S} (f : T' ⟶ T) :
    originSection p o ho T' ≫ (familyScheme p).map f = f.left ≫ originSection p o ho T :=
  ((originSectionNatTrans p o ho).naturality f).symm

/-- Pullback of a rigidified pair along a morphism `f : T' ⟶ T` of `S`-schemes. -/
def map {T T' : Over S} (f : T' ⟶ T) (P : RigidifiedPair p o ho T) :
    RigidifiedPair p o ho T' where
  bundle := pullbackLineBundle ((familyScheme p).map f) P.bundle
  rigidification :=
    (Scheme.Modules.pullbackComp (originSection p o ho T') ((familyScheme p).map f)).app
        P.bundle.val ≪≫
      (Scheme.Modules.pullbackCongr (originSection_comp_familyScheme_map f)).app P.bundle.val ≪≫
      ((Scheme.Modules.pullbackComp f.left (originSection p o ho T)).app P.bundle.val).symm ≪≫
      (Scheme.Modules.pullback f.left).mapIso P.rigidification ≪≫
      Scheme.Modules.pullbackUnitIso f.left

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- Pullback of an isomorphism of rigidified pairs along `f : T' ⟶ T`: the pullback of the
bundle isomorphism is compatible with the pulled-back rigidifications, by naturality of the
pullback comparison isomorphisms. -/
def Iso.map {T T' : Over S} (f : T' ⟶ T) {P Q : RigidifiedPair p o ho T} (φ : Iso P Q) :
    Iso (map f P) (map f Q) where
  iso := (Scheme.Modules.pullback ((familyScheme p).map f)).mapIso φ.iso
  comm := by
    have h1 := (Scheme.Modules.pullbackComp (originSection p o ho T')
      ((familyScheme p).map f)).hom.naturality φ.iso.hom
    have h2 := (Scheme.Modules.pullbackCongr
      (originSection_comp_familyScheme_map (p := p) (o := o) (ho := ho) f)).hom.naturality
        φ.iso.hom
    have h3 := (Scheme.Modules.pullbackComp f.left (originSection p o ho T)).inv.naturality
      φ.iso.hom
    simp only [Functor.comp_map] at h1 h2 h3
    simp only [RigidifiedPair.map, CategoryTheory.Iso.trans_hom, CategoryTheory.Iso.app_hom,
      CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.app_inv, CategoryTheory.Functor.mapIso_hom]
    rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, ← CategoryTheory.Functor.map_comp_assoc,
      φ.comm]

theorem map_bundle {T T' : Over S} (f : T' ⟶ T) (P : RigidifiedPair p o ho T) :
    (map f P).bundle = pullbackLineBundle ((familyScheme p).map f) P.bundle := rfl

end RigidifiedPair

open RigidifiedPair

/-- The rigidified Picard functor: `T` goes to the isomorphism classes of rigidified pairs over
`T`, with pullback of pairs (`RigidifiedPair.map`) as maps. -/
def rigidifiedPicardFunctor : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (RigidifiedPair.setoid (p := p) (o := o) (ho := ho) T.unop)
  map {T T'} f := TypeCat.ofHom (Quotient.map (RigidifiedPair.map f.unop) (by
    intro P Q h
    obtain ⟨e⟩ := (setoid_r_iff P Q).mp h
    exact (setoid_r_iff _ _).mpr
      ⟨(Scheme.Modules.pullback ((familyScheme p).map f.unop)).mapIso e⟩))
  map_id T := by
    ext x
    induction x using Quotient.inductionOn with | h P =>
    apply Quotient.sound
    refine (setoid_r_iff _ _).mpr ⟨?_⟩
    exact (Scheme.Modules.pullbackCongr ((familyScheme p).map_id T.unop)).app P.bundle.val ≪≫
      (Scheme.Modules.pullbackId _).app P.bundle.val
  map_comp {T T' T''} f g := by
    ext x
    induction x using Quotient.inductionOn with | h P =>
    apply Quotient.sound
    refine (setoid_r_iff _ _).mpr ⟨?_⟩
    exact (Scheme.Modules.pullbackCongr ((familyScheme p).map_comp g.unop f.unop)).app
        P.bundle.val ≪≫
      ((Scheme.Modules.pullbackComp ((familyScheme p).map g.unop)
        ((familyScheme p).map f.unop)).app P.bundle.val).symm

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- The class of the line bundle of a rigidified pair lies in the kernel of `o_T^*`. -/
theorem RigidifiedPair.classOf_mem_normalizedSubgroup {T : Over S} (P : RigidifiedPair p o ho T) :
    classOf _ P.bundle ∈ normalizedSubgroup p o ho (op T) := by
  rw [AddMonoidHom.mem_ker]
  change pullbackClass (originSection p o ho T) (classOf _ P.bundle) =
    classOf _ (trivialLineBundle T.left)
  rw [pullbackClass_classOf]
  exact Quotient.sound ⟨P.rigidification ≪≫ (coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit T.left.ringCatSheaf)).symm⟩

/-- The class of the line bundle, as a map from isomorphism classes of rigidified pairs to the
normalized subgroup. -/
def rigidifiedClass (T : Over S) :
    Quotient (RigidifiedPair.setoid (p := p) (o := o) (ho := ho) T) →
      normalizedSubgroup p o ho (op T) :=
  Quotient.lift (fun P => ⟨classOf _ P.bundle, P.classOf_mem_normalizedSubgroup⟩) (by
    rintro P Q ⟨φ⟩
    exact Subtype.ext (Quotient.sound ⟨φ.iso⟩))

theorem rigidifiedClass_mk {T : Over S} (P : RigidifiedPair p o ho T) :
    (rigidifiedClass p o ho T (Quotient.mk _ P)).val = classOf _ P.bundle := rfl

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman, Lemma 2.9.** Forgetting the rigidification is a bijection from isomorphism
classes of rigidified pairs onto `ker(o_T^*)`. -/
theorem rigidifiedClass_bijective (T : Over S) : Function.Bijective (rigidifiedClass p o ho T) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with | h P =>
    induction y using Quotient.inductionOn with | h Q =>
    apply Quotient.sound
    obtain ⟨e⟩ := (class_eq_iff _ P.bundle Q.bundle).mp (congrArg Subtype.val hxy)
    exact (RigidifiedPair.setoid_r_iff P Q).mpr ⟨e⟩
  · rintro ⟨a, ha⟩
    induction a using Quotient.inductionOn with | h L =>
    rw [AddMonoidHom.mem_ker] at ha
    change classOf _ (pullbackLineBundle (originSection p o ho T) L) =
      classOf _ (trivialLineBundle T.left) at ha
    obtain ⟨e⟩ := (class_eq_iff _ _ _).mp ha
    exact ⟨Quotient.mk _ ⟨L, e ≪≫ coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit T.left.ringCatSheaf)⟩, rfl⟩

/-- **Kleiman, Lemma 2.9.** The rigidified Picard functor is the normalized Picard functor:
the class `[(L, α)] ↦ [L]` is a natural bijection onto `ker(o_T^*)`. Only the section is
used. -/
def rigidifiedNormalizedIso :
    rigidifiedPicardFunctor p o ho ≅
      normalizedPicardFunctor p o ho ⋙ CategoryTheory.forget AddCommGrpCat :=
  NatIso.ofComponents
    (fun T => (Equiv.ofBijective _ (rigidifiedClass_bijective p o ho T.unop)).toIso) (by
      intro T T' f
      ext x
      induction x using Quotient.inductionOn with | h P =>
      exact Subtype.ext rfl)

theorem rigidifiedNormalizedIso_hom_app_mk {T : (Over S)ᵒᵖ} (P : RigidifiedPair p o ho T.unop) :
    ((rigidifiedNormalizedIso p o ho).hom.app T (Quotient.mk _ P)).val = classOf _ P.bundle := rfl

/-- **Kleiman, Lemma 2.9**, in Kleiman's form: `[(L, α)] ↦ [L]` is a natural bijection from
isomorphism classes of rigidified pairs onto `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)`. It is
`rigidifiedNormalizedIso` followed by the inverse of `quotientNormalizedIso`. -/
def rigidifiedRelativeIso :
    rigidifiedPicardFunctor p o ho ≅
      relativePicardFunctor p ⋙ CategoryTheory.forget AddCommGrpCat :=
  rigidifiedNormalizedIso p o ho ≪≫
    Functor.isoWhiskerRight (quotientNormalizedIso p o ho).symm (CategoryTheory.forget _)

theorem rigidifiedRelativeIso_hom_app_mk {T : (Over S)ᵒᵖ} (P : RigidifiedPair p o ho T.unop) :
    (rigidifiedRelativeIso p o ho).hom.app T (Quotient.mk _ P) =
      (QuotientAddGroup.mk (classOf _ P.bundle) :
        (familyPicardFunctor p).obj T ⧸ baseImage p T) :=
  quotientNormalizedEquiv_symm_apply p o ho T _

-- Line bundles are `SheafOfModules` objects used as objects of `Scheme.Modules`; the two
-- categories agree only up to instance transparency.
set_option backward.isDefEq.respectTransparency false in
/-- **Kleiman, Lemma 2.10.** If `O_T ⟶ (X ×_S T ⟶ T)_* O` is an isomorphism, isomorphisms
of rigidified pairs over `T` are unique; equivalently, a rigidified pair has no automorphism
other than the identity. An endomorphism of the line bundle is a global function on
`X ×_S T`, hence comes from `T`; compatibility with the rigidification forces that function
to be `1`. -/
theorem RigidifiedPair.Iso.eq_of_isIso_c {T : Over S} [IsIso (pullback.snd p T.hom).c]
    {P Q : RigidifiedPair p o ho T} (φ ψ : RigidifiedPair.Iso P Q) : φ = ψ := by
  apply RigidifiedPair.Iso.ext'
  obtain ⟨r, hr⟩ := exists_eq_globalScalarEndomorphism_of_isLocallyRankOne P.bundle.property
    (φ.iso.hom ≫ ψ.iso.inv)
  have hbij : Function.Bijective (pullback.snd p T.hom).appTop :=
    ConcreteCategory.bijective_of_isIso ((pullback.snd p T.hom).c.app (op ⊤))
  obtain ⟨w, rfl⟩ := hbij.2 r
  have h1 : (Scheme.Modules.pullback (originSection p o ho T)).map (φ.iso.hom ≫ ψ.iso.inv) =
      𝟙 _ := by
    have h : (Scheme.Modules.pullback (originSection p o ho T)).map φ.iso.hom =
        (Scheme.Modules.pullback (originSection p o ho T)).map ψ.iso.hom := by
      rw [← cancel_mono Q.rigidification.hom, φ.comm, ψ.comm]
    rw [CategoryTheory.Functor.map_comp, h, ← CategoryTheory.Functor.map_comp,
      CategoryTheory.Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [hr, pullback_map_globalScalarEndomorphism, RigidifiedPair.originSection_appTop_snd_appTop]
    at h1
  have hw : w = 1 := globalScalarEndomorphism_injective_of_iso P.rigidification
    (h1.trans (globalScalarEndomorphism_one _).symm)
  subst hw
  rw [map_one, globalScalarEndomorphism_one] at hr
  rw [← cancel_mono ψ.iso.inv, hr, CategoryTheory.Iso.hom_inv_id]

theorem RigidifiedPair.Iso.subsingleton_of_isIso_c {T : Over S} [IsIso (pullback.snd p T.hom).c]
    (P Q : RigidifiedPair p o ho T) : Subsingleton (RigidifiedPair.Iso P Q) :=
  ⟨RigidifiedPair.Iso.eq_of_isIso_c p o ho⟩

/-- **Kleiman, Lemma 2.10**, automorphism form. -/
theorem RigidifiedPair.Iso.eq_refl_of_isIso_c {T : Over S} [IsIso (pullback.snd p T.hom).c]
    {P : RigidifiedPair p o ho T} (φ : RigidifiedPair.Iso P P) : φ = RigidifiedPair.Iso.refl P :=
  RigidifiedPair.Iso.eq_of_isIso_c p o ho φ _

/-- **Kleiman, Lemma 2.10, under universal O-connectedness.** For `S` locally Noetherian and
`p` proper, flat, with geometrically integral fibres, isomorphisms of rigidified pairs over
every `S`-scheme are unique. -/
theorem RigidifiedPair.Iso.eq_of_isProper_of_flat_of_geometricallyIntegral [IsLocallyNoetherian S]
    [IsProper p] [Flat p] [GeometricallyIntegral p] {T : Over S} {P Q : RigidifiedPair p o ho T}
    (φ ψ : RigidifiedPair.Iso P Q) : φ = ψ :=
  have := isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p T.hom
  RigidifiedPair.Iso.eq_of_isIso_c p o ho φ ψ

end AlgebraicGeometry.Scheme.RelativePicard
