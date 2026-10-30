/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.GroupRigidity
public import Aglib.AlgebraicGeometry.Picard.Representability.FineStrata
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.EquivFin

/-!
# The field-level cube for a projective family and a proper group square

The three original face classes determine a family on `X × (G × G)` when
`X` is projective and geometrically integral over the field, with a
section, and `G` is a proper geometrically integral group scheme. The Picard
representation, separatedness and local finite type used by the proof are
supplied by the projective Picard construction. There is no representability
or rigidity premise in the public theorem, and the chosen projective embedding
is internal to the proof.

This is the group-square instance of the theorem of the cube. It retains
projectivity of `X`; it does not assert the unrestricted relative theorem
over an arbitrary nonreduced parameter. The underlying classifying-map
equation is an equality of scheme morphisms and therefore covers arbitrary
nonreduced test pullbacks.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible ProjectiveSpace

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (o : Spec (.of k) ⟶ X) (ho : o ≫ p = 𝟙 _)
  [IsHProjective p] [GeometricallyIntegral p]

/-- The projective cube on the original Picard group, with the Picard
representability and scheme rigidity suppliers discharged. -/
theorem familyClass_eq_zero_of_group_axes_of_isHProjective
    (G : Over (Spec (.of k))) [GrpObj G] [IsProper G.hom]
    [GeometricallyIntegral G.hom]
    (a : PicardGroup (pullback p (G ⊗ G).hom))
    (horigin : pullbackClass (originSection p o ho (G ⊗ G)) a = 0)
    (hleft : pullbackClass ((familyScheme p).map (lift (𝟙 G) (1 : G ⟶ G))) a = 0)
    (hright : pullbackClass ((familyScheme p).map (lift (1 : G ⟶ G) (𝟙 G))) a = 0) :
    a = 0 := by
  obtain ⟨coords, N, e, i, hi, hqc, hiX⟩ :=
    IsHQuasiProjective.exists_isImmersion_equivFin p
  have : IsImmersion i := hi
  have : QuasiCompact i := hqc
  have : IsProper (i ≫ ProjectiveSpace.toSpec k coords) := hiX.symm ▸ inferInstance
  have : IsProper i := IsProper.of_comp i (ProjectiveSpace.toSpec k coords)
  have : IsClosedImmersion i :=
    (IsClosedImmersion.iff_isProper_and_mono i).mpr ⟨inferInstance, inferInstance⟩
  subst p
  let h := Strata.fineStrataRepresentableByHQuasiProjective i e
  exact familyClass_eq_zero_of_group_axes (i ≫ ProjectiveSpace.toSpec k coords) o ho
    (picardSchemeRepresentableBy h) G a horigin hleft hright

/-- The same cube theorem for actual line bundles, through the library's
original isomorphism-class quotient. -/
theorem nonempty_lineBundle_iso_trivial_of_group_axes_of_isHProjective
    (G : Over (Spec (.of k))) [GrpObj G] [IsProper G.hom]
    [GeometricallyIntegral G.hom]
    (L : LineBundle (pullback p (G ⊗ G).hom))
    (horigin : pullbackClass (originSection p o ho (G ⊗ G)) (classOf _ L) = 0)
    (hleft : pullbackClass ((familyScheme p).map (lift (𝟙 G) (1 : G ⟶ G)))
      (classOf _ L) = 0)
    (hright : pullbackClass ((familyScheme p).map (lift (1 : G ⟶ G) (𝟙 G)))
      (classOf _ L) = 0) :
    Nonempty (L.val ≅ (trivialLineBundle (pullback p (G ⊗ G).hom)).val) :=
  (class_eq_iff _ _ _).mp
    (familyClass_eq_zero_of_group_axes_of_isHProjective p o ho G
      (classOf _ L) horigin hleft hright)

end AlgebraicGeometry.Scheme.RelativePicard
