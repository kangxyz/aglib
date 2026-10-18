/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.OpenRepresentatives
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.EtaleSectionDescent

/-!
# ChartSections

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)
namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.FiniteSetOpenRepresentation
universe u
variable {X : Scheme.{u}} {F : Scheme.EtaleH1.SetSheaf X} {U : X.Opens}

/-- The étale test object over `X` obtained by composing the representing cover over
`U.toScheme` with the open immersion `U.ι`. -/
abbrev site (r : FiniteSetOpenRepresentation F U) : X.Etale :=
  (Scheme.EtaleH1.siteEtalePostcompose U.ι).obj ((toEtale U.toScheme).obj r.cover)

/-- The section of `F` on the representing chart corresponding under `r.iso` to
the identity morphism of `r.cover.obj`. -/
def section_ (r : FiniteSetOpenRepresentation F U) : F.obj.obj (op r.site) :=
  r.iso.hom.hom.app (op ((toEtale U.toScheme).obj r.cover)) (ULift.up (𝟙 r.cover.obj))

/-- Regard a morphism from the postcomposed chart `W` to `r.site` as a morphism
over `U.toScheme`, by cancellation of the open immersion `U.ι`. -/
def localHom (r : FiniteSetOpenRepresentation F U) {W : U.toScheme.Etale}
    (g : (Scheme.EtaleH1.siteEtalePostcompose U.ι).obj W ⟶ r.site) :
    (Scheme.Etale.forget U.toScheme).obj W ⟶ r.cover.obj :=
  Over.homMk g.left (by
    apply (cancel_mono U.ι).1
    simpa [site, toEtale] using MorphismProperty.Over.w g)

/-- Compose the structural equation of a morphism over `U.toScheme` with `U.ι`
to obtain a morphism from the postcomposed chart `W` to `r.site`. -/
def globalHom (r : FiniteSetOpenRepresentation F U) {W : U.toScheme.Etale}
    (g : (Scheme.Etale.forget U.toScheme).obj W ⟶ r.cover.obj) :
    (Scheme.EtaleH1.siteEtalePostcompose U.ι).obj W ⟶ r.site :=
  MorphismProperty.Over.homMk g.left (by
    simp [site, toEtale]) (by trivial)

/-- The equivalence between chart morphisms over `X` to `r.site` and morphisms over
`U.toScheme` to `r.cover.obj`, with maps `localHom` and `globalHom`. -/
def homEquiv (r : FiniteSetOpenRepresentation F U) (W : U.toScheme.Etale) :
    ((Scheme.EtaleH1.siteEtalePostcompose U.ι).obj W ⟶ r.site) ≃
      ((Scheme.Etale.forget U.toScheme).obj W ⟶ r.cover.obj) where
  toFun := r.localHom
  invFun := r.globalHom
  left_inv g := by apply MorphismProperty.Over.Hom.ext; rfl
  right_inv g := by apply Over.OverMorphism.ext; rfl

lemma section_restrict (r : FiniteSetOpenRepresentation F U) {W : U.toScheme.Etale}
    (g : (Scheme.EtaleH1.siteEtalePostcompose U.ι).obj W ⟶ r.site) :
    F.obj.map g.op r.section_ = r.iso.hom.hom.app (op W) (ULift.up (r.localHom g)) := by
  have h := congrArg (fun k => k (ULift.up (𝟙 r.cover.obj)))
    (r.iso.hom.hom.naturality (finiteSectionSiteMap r.cover (r.localHom g)).op)
  change r.iso.hom.hom.app (op W) (ULift.up (r.localHom g ≫ 𝟙 r.cover.obj)) =
    F.obj.map _ r.section_ at h
  have hg : (Scheme.EtaleH1.siteEtalePostcompose U.ι).map (finiteSectionSiteMap r.cover
    (r.localHom g)) = g := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  simp only [Category.comp_id, Functor.op_map, Quiver.Hom.unop_op, hg] at h
  exact h.symm

/-- The local universal section determines every map from a test scheme on the open. -/
theorem section_bijective (r : FiniteSetOpenRepresentation F U) (W : U.toScheme.Etale) :
    Function.Bijective (fun g : (Scheme.EtaleH1.siteEtalePostcompose U.ι).obj W ⟶ r.site =>
      F.obj.map g.op r.section_) := by
  have h : Function.Bijective (r.iso.hom.hom.app (op W)) :=
    (CategoryTheory.isIso_iff_bijective _).1 inferInstance
  let E : ((Scheme.EtaleH1.siteEtalePostcompose U.ι).obj W ⟶ r.site) ≃
      ULift.{u + 1} ((Scheme.Etale.forget U.toScheme).obj W ⟶ r.cover.obj) :=
    (r.homEquiv W).trans Equiv.ulift.symm
  have heq : (fun g : (Scheme.EtaleH1.siteEtalePostcompose U.ι).obj W ⟶ r.site => F.obj.map g.op
    r.section_) =
      (fun g => r.iso.hom.hom.app (op W) (E g)) := funext (r.section_restrict)
  rw [heq]
  exact h.comp E.bijective

/-- The same universal property for an arbitrary etale test scheme factoring through the open. -/
theorem section_bijective_of_factor (r : FiniteSetOpenRepresentation F U)
    (W : X.Etale) (a : W.left ⟶ U.toScheme) (ha : a ≫ U.ι = W.hom) :
    Function.Bijective (fun g : W ⟶ r.site => F.obj.map g.op r.section_) := by
  have : Etale (a ≫ U.ι) := by rw [ha]; infer_instance
  have : Etale a := Etale.of_comp a U.ι
  let V : U.toScheme.Etale := Scheme.Etale.mk a
  let e : W ≅ (Scheme.EtaleH1.siteEtalePostcompose U.ι).obj V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simpa [V] using ha)
  let E : (W ⟶ r.site) ≃ ((Scheme.EtaleH1.siteEtalePostcompose U.ι).obj V ⟶ r.site) :=
    { toFun := fun g => e.inv ≫ g
      invFun := fun g => e.hom ≫ g
      left_inv := by intro g; simp
      right_inv := by intro g; simp }
  have hm : Function.Bijective (F.obj.map e.hom.op) :=
    (CategoryTheory.isIso_iff_bijective _).1 inferInstance
  convert hm.comp ((r.section_bijective V).comp E.bijective) using 1
  ext g
  dsimp [E]
  rw [← Functor.map_comp_apply, ← op_comp]
  simp

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.FiniteSetOpenRepresentation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 5ac362fd0e05c02f2cbb3d6f240106cfc3f65a1a19b7c3cf766a4ff98c41b06d.
Definitions, hypotheses and universes are retained modulo native names. -/
