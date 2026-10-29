/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.BoundedFamily.Parameters
public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic
public import Aglib.AlgebraicGeometry.Picard.GroupLaw

/-!
# The Abel morphism `X^n ⟶ Pic_{X/k}` of the bounded graph family

Let `k` be a field, `X` a scheme over `k` that is smooth of relative dimension one, separated and
proper, with a rational point `o`, and let `P` be a scheme over `k` with a representation `R` of
`Pic_{X/k,(fppf)}` on locally Noetherian test schemes (for instance the Picard scheme of
[PicardScheme](PicardScheme.lean)). The parameter scheme `X^n = BoundedFamily.parameter X.hom n`
is proper and Noetherian over `k`, and carries the graph-sum line bundle
`BoundedFamily.lineBundle X.hom o ho n` of `(p_i) ↦ Σ (p_i - o)`.

* `BoundedFamily.abelMorphism o ho P R n : X^n ⟶ P`, **the Abel morphism**: the morphism of
  locally Noetherian `k`-schemes that `R` (Yoneda) attaches to the section of
  `Pic_{X/k,(fppf)}` over `X^n` given by the class of the graph-sum line bundle
  (`homEquiv_abelMorphism`). On a `T`-point `a` of `X^n` it is the class of the pullback of the
  family along `X ×_k T ⟶ X ×_k X^n` (`homEquiv_comp_abelMorphism`).
* The origin `(o, …, o)` goes to the unit of the group law `picardCommGrpObj X.hom P R`
  (`originPoint_comp_abelMorphism`), since the Abel class of the origin is trivial.
* `X^n` is connected when `X` is geometrically connected (`connectedSpace_parameter`; a
  geometrically connected universally open scheme over a field times a connected one is
  connected, Stacks, Tag 0385), so **the image of the Abel morphism lies in the identity
  component** `Pic⁰_{X/k}` (`range_abelMorphism_subset_identityComponent`).
* If `P` is separated over `k`, the Abel morphism is proper, since `X^n` is proper over `k`, so
  **its image is closed** (`isClosed_range_abelMorphism`).

The family and its point formulas are those of `Curve.Abel.BoundedFamily`
([BoundedFamily](../Abel/BoundedFamily.lean), [Parameters](../Abel/BoundedFamily/Parameters.lean)).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Group
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

section Connected

variable {S : Scheme.{u}}

/-- **A finite product of geometrically connected, universally open schemes over a connected base
is connected**, by induction on the number of factors: each step is the projection of a pullback
along a geometrically connected universally open structure morphism, an open map with connected
fibres onto a connected scheme (Stacks, Tag 0378; over a field, Stacks, Tag 0385). -/
theorem connectedSpace_finiteProductOver [ConnectedSpace S] {n : ℕ} (Y : Fin n → Over S)
    [∀ i, GeometricallyConnected (Y i).hom] [∀ i, UniversallyOpen (Y i).hom] :
    ConnectedSpace (finiteProductOver Y).left := by
  induction n with
  | zero => exact inferInstanceAs (ConnectedSpace S)
  | succ n ih =>
    have : ConnectedSpace (finiteProductOver (fun i : Fin n => Y i.succ)).left := ih _
    have : ConnectedSpace ↥(pullback (Y 0).hom
        (finiteProductOver (fun i : Fin n => Y i.succ)).hom) := inferInstance
    exact (Over.prodLeftIsoPullback (Y 0)
      (finiteProductOver (fun i : Fin n => Y i.succ))).hom.homeomorph.connectedSpace_iff.mpr this

variable {k : Type u} [Field k] {X : FScheme k}

/-- **The parameter scheme `X^n` of a curve is connected**: `X` is geometrically connected and
smooth, hence universally open, over `k`, and `Spec k` is connected. -/
theorem connectedSpace_parameter (hX : Properties X) (n : ℕ) :
    ConnectedSpace (parameter X.hom n).left := by
  have := curveProperties_smooth hX
  have : GeometricallyConnected (Over.mk X.hom).hom := hX.connected
  have : UniversallyOpen (Over.mk X.hom).hom := inferInstanceAs (UniversallyOpen X.hom)
  exact connectedSpace_finiteProductOver (fun _ : Fin n => Over.mk X.hom)

end Connected

section Family

variable {S X : Scheme.{u}} (p : X ⟶ S)

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances (as in
-- `familyScheme_map_fst`).
set_option backward.isDefEq.respectTransparency false in
/-- The map of the functor `T ↦ X ×_S T` of the Picard presheaves is the family map
`Hom.familyMap` of the graph line bundles. -/
theorem familyScheme_map_eq_familyMap {T T' : Over S} (a : T' ⟶ T) :
    (familyScheme p).map a = Hom.familyMap p T.hom T'.hom a.left (Over.w a) := by
  rw [familyScheme_map]
  apply pullback.hom_ext <;> simp [pullback.map, Hom.familyMap]

end Family

variable {k : Type u} [Field k] (X : FScheme k) [SmoothOfRelativeDimension 1 X.hom]
  [IsProper X.hom] (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)

/-- **The parameter scheme `X^n` as a locally Noetherian scheme over `k`**: it is proper over the
Noetherian `Spec k`, hence Noetherian (`parameter_isNoetherian`). -/
def locallyNoetherianParameter (n : ℕ) : LocallyNoetherianOver (Spec (.of k)) :=
  ⟨parameter X.hom n, by
    have := parameter_isNoetherian X.hom n
    infer_instance⟩

/-- The section of `Pic_{X/k,(fppf)}` over `X^n` given by the class of the graph-sum line bundle
of `(p_i) ↦ Σ (p_i - o)`. -/
def abelSection (n : ℕ) : (fppfPicardSheaf X.hom).obj.obj (op (parameter X.hom n)) :=
  (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op (parameter X.hom n))
    (classOf _ (lineBundle X.hom o ho n))

variable {X} (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- **The Abel morphism** `a_n : X^n ⟶ P`, `(p_i) ↦ Σ (p_i - o)`: the morphism of locally
Noetherian `k`-schemes attached by the representation `R` to the class of the graph-sum line
bundle on `X ×_k X^n`. -/
def abelMorphism (n : ℕ) : locallyNoetherianParameter X n ⟶ P :=
  R.homEquiv.symm (abelSection X o ho n)

/-- The Abel morphism corresponds under `R` to the class of the graph-sum line bundle. -/
theorem homEquiv_abelMorphism (n : ℕ) :
    R.homEquiv (abelMorphism o ho P R n) = abelSection X o ho n :=
  R.homEquiv.apply_symm_apply _

/-- **The Abel morphism on `T`-points**: for a morphism `a : T ⟶ X^n` of locally Noetherian
`k`-schemes, `a ≫ a_n` corresponds under `R` to the class of the pullback of the graph-sum line
bundle along `X ×_k T ⟶ X ×_k X^n`. -/
theorem homEquiv_comp_abelMorphism {n : ℕ} {T : LocallyNoetherianOver (Spec (.of k))}
    (a : T ⟶ locallyNoetherianParameter X n) :
    R.homEquiv (a ≫ abelMorphism o ho P R n) =
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
        (pullbackClass ((familyScheme X.hom).map a.hom) (classOf _ (lineBundle X.hom o ho n))) := by
  rw [R.homEquiv_comp, homEquiv_abelMorphism]
  exact (NatTrans.naturality_apply (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom)
    a.hom.op (classOf _ (lineBundle X.hom o ho n))).symm

/-- **The Abel morphism at a tuple of sections**: for sections `s_i : T ⟶ X` over `t : T ⟶ k`,
the point `(s_i)` of `X^n` goes to the class of `Σ (s_i - o_T)`. -/
theorem homEquiv_parameterPoint_comp_abelMorphism {n : ℕ}
    {T : LocallyNoetherianOver (Spec (.of k))} (s : Fin n → (T.obj.left ⟶ X.left))
    (hs : ∀ i, s i ≫ X.hom = T.obj.hom) :
    R.homEquiv (ObjectProperty.homMk (Over.homMk (parameterPoint X.hom T.obj.hom s hs)
        (parameterPoint_over X.hom T.obj.hom s hs) : T.obj ⟶ parameter X.hom n) ≫
          abelMorphism o ho P R n) =
      (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
        (∑ i, Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho T.obj.hom (s i) (hs i)) := by
  rw [homEquiv_comp_abelMorphism]
  congr 1
  rw [familyScheme_map_eq_familyMap]
  exact lineBundle_class_at_tuple X.hom o ho T.obj.hom s hs

/-- The rational point `(o, …, o)` of `X^n`. -/
def originPoint (n : ℕ) : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n :=
  Over.homMk (parameterPoint X.hom (𝟙 _) (fun _ : Fin n => o) (fun _ => ho))
    (parameterPoint_over X.hom (𝟙 _) _ _)

/-- The Abel class of the origin section over any base vanishes. -/
theorem abelClass_eq_zero_of_eq_comp_origin {T : Scheme.{u}} (t : T ⟶ Spec (.of k))
    (s : T ⟶ X.left) (hs : s ≫ X.hom = t) (hso : s = t ≫ o) :
    Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho t s hs = 0 := by
  subst hso
  exact Hom.abelClass_origin Hom.smoothRelativeDivisorIdeal X.hom o ho t

/-- **The Abel morphism is proper** when `P` is separated over `k`: `X^n` is proper over `k`. -/
theorem isProper_abelMorphism [IsSeparated P.obj.hom] (n : ℕ) :
    IsProper (abelMorphism o ho P R n).hom.left := by
  have : IsProper ((abelMorphism o ho P R n).hom.left ≫ P.obj.hom) := by
    rw [Over.w (abelMorphism o ho P R n).hom]
    exact parameter_isProper X.hom n
  exact IsProper.of_comp _ P.obj.hom

/-- **The image of the Abel morphism is closed** when `P` is separated over `k`. -/
theorem isClosed_range_abelMorphism [IsSeparated P.obj.hom] (n : ℕ) :
    IsClosed (Set.range (abelMorphism o ho P R n).hom.left) := by
  have := isProper_abelMorphism o ho P R n
  exact (abelMorphism o ho P R n).hom.left.isClosedMap.isClosed_range

variable [LocallyOfFiniteType P.obj.hom]

/-- **The Abel morphism sends the origin `(o, …, o)` to the unit** of the group law
`picardCommGrpObj X.hom P R`: the class of `Σ (o - o)` is zero. -/
theorem originPoint_comp_abelMorphism (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    originPoint o ho n ≫ (abelMorphism o ho P R n).hom = η[P.obj] := by
  let := picardCommGrpObj X.hom P R
  let pt : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨𝟙_ (Over (Spec (.of k))), inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))⟩
  have h1 : R.homEquiv (ObjectProperty.homMk (originPoint o ho n ≫ (abelMorphism o ho P R n).hom) :
      pt ⟶ P) = R.homEquiv (ObjectProperty.homMk η[P.obj] : pt ⟶ P) := by
    have h0 := picard_homEquiv_one X.hom P R pt
    have hone : (1 : pt.obj ⟶ P.obj) = η[P.obj] := by
      change CartesianMonoidalCategory.toUnit _ ≫ η[P.obj] = η[P.obj]
      rw [CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
    rw [hone] at h0
    rw [h0]
    have h2 := homEquiv_parameterPoint_comp_abelMorphism o ho P R (T := pt)
      (fun _ : Fin n => o) (fun _ => ho)
    have hsum : (∑ _ : Fin n, Hom.abelClass Hom.smoothRelativeDivisorIdeal X.hom o ho
        pt.obj.hom o ho) = 0 :=
      Finset.sum_eq_zero fun _ _ => abelClass_eq_zero_of_eq_comp_origin o ho _ o ho
        (Category.id_comp o).symm
    exact h2.trans ((congrArg (fun x => ((quotientProjection X.hom ≫
      toFppfPicardSheaf X.hom).app (op pt.obj)) x) hsum).trans (map_zero _))
  have h3 := congrArg InducedCategory.Hom.hom (R.homEquiv.injective h1)
  exact h3

/-- **The image of the Abel morphism lies in the identity component** `Pic⁰_{X/k}` of `P`, for
the group law `picardCommGrpObj X.hom P R`: `X^n` is connected and `(o, …, o)` goes to the unit. -/
theorem range_abelMorphism_subset_identityComponent (hX : Properties X) (n : ℕ) :
    letI := picardCommGrpObj X.hom P R
    Set.range (abelMorphism o ho P R n).hom.left ⊆ identityComponent P.obj := by
  let := picardCommGrpObj X.hom P R
  have : ConnectedSpace (locallyNoetherianParameter X n).obj.left := connectedSpace_parameter hX n
  exact range_subset_identityComponent_of_section P.obj (abelMorphism o ho P R n).hom
    (originPoint o ho n) (originPoint_comp_abelMorphism o ho P R n)

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
