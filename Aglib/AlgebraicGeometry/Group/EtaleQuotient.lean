/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.EffectiveEpi.Over
public import Aglib.AlgebraicGeometry.Morphisms.Etale.KernelPair
public import Aglib.AlgebraicGeometry.Curves.SmoothGeometry
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Actual descent for given etale surjective group quotients

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Tate.Classification`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, original lines 209–305.
Only the stated generic slice is admitted; its actual objects, maps and hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Group.EtaleQuotient
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F K : Type u} [Field F] [Field K] [IsAlgClosed K]
  (α : F →+* K) {G H J : Grp (FScheme F)}

/-- Actual etale surjective group maps cancel on the left, by the
underlying ordinary fpqc effective epimorphism. -/
theorem cancel_group_map (f : G ⟶ H)
    [Etale f.hom.hom.left] [Surjective f.hom.hom.left]
    (a b : H ⟶ J) (h : f ≫ a = f ≫ b) : a = b := by
  let : EffectiveEpi f.hom.hom := CategoryTheory.Over.effectiveEpi_of_left _
  apply Grp.hom_ext
  apply (cancel_epi f.hom.hom).1
  exact congrArg (fun m : G ⟶ J => m.hom.hom) h


/-- Inclusion of literal field-point kernels yields the actual all-test
cocycle. Reducedness and morphism detection are proved on the scheme kernel pair. -/
theorem kernel_inclusion_cocycle (f : G ⟶ H) (g : G ⟶ J)
    [Etale f.hom.hom.left] (hG : Curve.Properties G.X) (hJ : Curve.Properties J.X)
    (hker : ∀ x : extensionPointSource α ⟶ G.X,
      x ≫ f.hom.hom = 1 → x ≫ g.hom.hom = 1)
    {T : FScheme F} (a b : T ⟶ G.X)
    (hab : a ≫ f.hom.hom = b ≫ f.hom.hom) : a ≫ g.hom.hom = b ≫ g.hom.hom := by
  let : Smooth G.X.hom := by
    let : SmoothOfRelativeDimension 1 G.X.hom := hG.smooth
    exact SmoothOfRelativeDimension.smooth 1 G.X.hom
  let : IsProper J.X.hom := hJ.proper
  let : Smooth J.X.hom := by
    let : SmoothOfRelativeDimension 1 J.X.hom := hJ.smooth
    exact SmoothOfRelativeDimension.smooth 1 J.X.hom
  apply all_test_cocycle_of_kernelPair f.hom.hom g.hom.hom _ a b hab
  apply kernelPair_comp_eq_of_extension_points α
  intro x y hxy
  have hf : (x / y) ≫ f.hom.hom = 1 := by
    rw [GrpObj.div_comp, hxy]
    exact div_self' _
  have hg := hker (x / y) hf
  rwa [GrpObj.div_comp, div_eq_one] at hg

variable (f : G ⟶ H) (g : G ⟶ J)
  [Etale f.hom.hom.left] [Surjective f.hom.hom.left]
  (hG : Curve.Properties G.X) (hJ : Curve.Properties J.X)
  (hker : ∀ x : extensionPointSource α ⟶ G.X,
    x ≫ f.hom.hom = 1 → x ≫ g.hom.hom = 1)

/-- Actual original-field quotient comparison obtained by ordinary fpqc descent. -/
def quotientMap : H.X ⟶ J.X := by
  let : EffectiveEpi f.hom.hom := CategoryTheory.Over.effectiveEpi_of_left _
  exact EffectiveEpi.desc f.hom.hom g.hom.hom
    (kernel_inclusion_cocycle α f g hG hJ hker)

@[reassoc] theorem quotientMap_fac :
    f.hom.hom ≫ quotientMap α f g hG hJ hker = g.hom.hom := by
  let : EffectiveEpi f.hom.hom := CategoryTheory.Over.effectiveEpi_of_left _
  exact EffectiveEpi.fac f.hom.hom g.hom.hom
    (kernel_inclusion_cocycle α f g hG hJ hker)

theorem quotientMap_pointed :
    η[H.X] ≫ quotientMap α f g hG hJ hker = η[J.X] := by
  rw [← IsMonHom.one_hom f.hom.hom, Category.assoc, quotientMap_fac, IsMonHom.one_hom]

omit hker in
/-- Equal completed-field point kernels of actual etale surjective quotient maps
produce an actual original-field scheme isomorphism. The inverse is descended
symmetrically, rather than supplied or inferred from an unproved degree lemma. -/
def quotientSchemeIso
    [Etale g.hom.hom.left] [Surjective g.hom.hom.left]
    (hH : Curve.Properties H.X)
    (heq : ∀ x : extensionPointSource α ⟶ G.X,
      x ≫ f.hom.hom = 1 ↔ x ≫ g.hom.hom = 1) : H.X ≅ J.X where
  hom := quotientMap α f g hG hJ (fun x hx => (heq x).1 hx)
  inv := quotientMap α g f hG hH (fun x hx => (heq x).2 hx)
  hom_inv_id := by
    let : EffectiveEpi f.hom.hom := CategoryTheory.Over.effectiveEpi_of_left _
    apply (cancel_epi f.hom.hom).1
    rw [← Category.assoc, quotientMap_fac, quotientMap_fac, Category.comp_id]
  inv_hom_id := by
    let : EffectiveEpi g.hom.hom := CategoryTheory.Over.effectiveEpi_of_left _
    apply (cancel_epi g.hom.hom).1
    rw [← Category.assoc, quotientMap_fac, quotientMap_fac, Category.comp_id]

omit hker in
/-- The comparison is an actual group-scheme isomorphism. Its group law
compatibility is derived from the existing explicit proper-curve rigidity inputs. -/
def quotientGroupIso
    [Etale g.hom.hom.left] [Surjective g.hom.hom.left]
    (hH : Curve.Properties H.X)
    (heq : ∀ x : extensionPointSource α ⟶ G.X,
      x ≫ f.hom.hom = 1 ↔ x ≫ g.hom.hom = 1) : H ≅ J := by
  let e := quotientSchemeIso α f g hG hJ hH heq
  let : IsMonHom e.hom := Curve.pointedMorphism_of_curveProperties H J hH hJ e.hom
    (quotientMap_pointed α f g hG hJ (fun x hx => (heq x).1 hx))
  exact Grp.mkIso e (IsMonHom.one_hom _) (IsMonHom.mul_hom _)

omit hker in
/-- Exact compatibility with the two given outgoing actual group maps. -/
theorem quotientGroupIso_fac
    [Etale g.hom.hom.left] [Surjective g.hom.hom.left]
    (hH : Curve.Properties H.X)
    (heq : ∀ x : extensionPointSource α ⟶ G.X,
      x ≫ f.hom.hom = 1 ↔ x ≫ g.hom.hom = 1) :
    f ≫ (quotientGroupIso α f g hG hJ hH heq).hom = g := by
  apply Grp.hom_ext
  exact quotientMap_fac α f g hG hJ (fun x hx => (heq x).1 hx)


end AlgebraicGeometry.Scheme.Group.EtaleQuotient
