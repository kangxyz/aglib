/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.Classifying
public import Aglib.AlgebraicGeometry.Picard.Comparison.RepresentableBy
public import Aglib.AlgebraicGeometry.Picard.GroupLaw
public import Aglib.AlgebraicGeometry.Group.LineBundleCube.Rigidity

/-!
# Rigidity of normalized families on a proper group square

A represented normalized family on `X × (G × G)` is trivial when its origin
restriction and the two parameter-axis restrictions are trivial. The proof
uses the original classifying morphism into the same Picard representative,
whose target need only be separated and locally of finite type. It proves an
equality of scheme morphisms, so all subsequent nonreduced test-scheme
pullbacks are covered. The parameter group is geometrically integral; no
claim about arbitrary nonreduced parameter groups is made.

The representation is retained as the explicit input to this general lemma.
The projective cube leaf supplies it from the actual Picard construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Group.PointedMorphism

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (o : Spec (.of k) ⟶ X) (ho : o ≫ p = 𝟙 _)
  [IsProper p] [GeometricallyIntegral p]
  {P : LocallyNoetherianOver (Spec (.of k))} [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The normalized classifying map of the zero family is the original unit
of the Picard group scheme, for the same chosen representation. -/
theorem normalizedFamilyClassifyingMap_zero_hom
    (T : LocallyNoetherianOver (Spec (.of k))) :
    letI := picardCommGrpObj p P R
    (normalizedFamilyClassifyingMap p o ho
      (normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R) T 0).hom =
        (1 : T.obj ⟶ P.obj) := by
  let := picardCommGrpObj p P R
  let Rn := normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R
  have h : normalizedFamilyClassifyingMap p o ho Rn T 0 =
      ObjectProperty.homMk (1 : T.obj ⟶ P.obj) := by
    apply Rn.homEquiv.injective
    rw [homEquiv_normalizedFamilyClassifyingMap, normalizedFamilyClass_zero]
    change 0 = ((normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).inv.app
      (op T.obj)).hom (R.homEquiv (ObjectProperty.homMk (1 : T.obj ⟶ P.obj)))
    rw [picard_homEquiv_one, map_zero]
  exact congrArg (fun f : T ⟶ P => f.hom) h

include R in
/-- Scheme-level cube rigidity for a family whose Picard functor is
represented: vanishing of the three original face classes implies vanishing
of the original class. -/
theorem familyClass_eq_zero_of_group_axes [IsSeparated P.obj.hom]
    (G : Over (Spec (.of k))) [GrpObj G] [IsProper G.hom]
    [GeometricallyIntegral G.hom]
    (a : PicardGroup (pullback p (G ⊗ G).hom))
    (horigin : pullbackClass (originSection p o ho (G ⊗ G)) a = 0)
    (hleft : pullbackClass ((familyScheme p).map (lift (𝟙 G) (1 : G ⟶ G))) a = 0)
    (hright : pullbackClass ((familyScheme p).map (lift (1 : G ⟶ G) (𝟙 G))) a = 0) :
    a = 0 := by
  let := picardCommGrpObj p P R
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : IsLocallyNoetherian (G ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (G ⊗ G).hom
  let T : LocallyNoetherianOver (Spec (.of k)) := ⟨G ⊗ G, inferInstance⟩
  let T₀ : LocallyNoetherianOver (Spec (.of k)) := ⟨G, inferInstance⟩
  let Rn := normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral p o ho R
  let c : G ⊗ G ⟶ P.obj := (normalizedFamilyClassifyingMap p o ho Rn T a).hom
  have hc (f : G ⟶ G ⊗ G)
      (hf : pullbackClass ((familyScheme p).map f) a = 0) : f ≫ c = 1 := by
    let f' : T₀ ⟶ T := ObjectProperty.homMk f
    have h := normalizedFamilyClassifyingMap_pullback p o ho Rn f' a
    have h' := congrArg (fun g : T₀ ⟶ P => g.hom) h
    change (normalizedFamilyClassifyingMap p o ho Rn T₀
      (pullbackClass ((familyScheme p).map f) a)).hom = f ≫ c at h'
    have hz := congrArg (fun b : PicardGroup (pullback p G.hom) =>
      (normalizedFamilyClassifyingMap p o ho Rn T₀ b).hom) hf
    exact h'.symm.trans (hz.trans (normalizedFamilyClassifyingMap_zero_hom p o ho R T₀))
  have hc1 : c = 1 := rigidity_of_geometricallyIntegral_of_isSeparated G P.obj c
    (hc _ hleft) (hc _ hright)
  have hc0 : normalizedFamilyClassifyingMap p o ho Rn T a =
      normalizedFamilyClassifyingMap p o ho Rn T 0 := by
    apply ObjectProperty.hom_ext
    change c = _
    rw [hc1, normalizedFamilyClassifyingMap_zero_hom p o ho R T]
  exact eq_zero_of_normalizedFamilyClass_eq_zero p o ho (G ⊗ G) a
    ((normalizedFamilyClassifyingMap_eq_zero_iff p o ho Rn T a).mp hc0) horigin

end AlgebraicGeometry.Scheme.RelativePicard
