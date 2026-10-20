/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# Pointwise additive, limit and abelian structures on dependent category products, and pointwise
detection of short exactness.

Source: `lean/R5Lab/Aglib/CategoryTheory/Pi/Abelian.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `fb18e491737dce633676f0c5eed59e8e29cf57c00362f6f109e05fc92e005f39`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Pi
universe u v w
section PiAbelian
variable {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)]

instance piPreadditive [∀ i, Preadditive (C i)] : Preadditive (∀ i, C i) where
  homGroup P Q := Pi.addCommGroup
  add_comp P Q T f g h := by
    funext i
    exact Preadditive.add_comp (P i) (Q i) (T i) (f i) (g i) (h i)
  comp_add P Q T f g h := by
    funext i
    exact Preadditive.comp_add (P i) (Q i) (T i) (f i) (g i) (h i)

instance evalAdditive [∀ i, Preadditive (C i)] (i : I) : (Pi.eval C i).Additive where
  map_add := by intros; rfl

section Limits
variable {J : Type*} [Category* J] (F : J ⥤ ∀ i, C i)

/-- The cone in a dependent product category assembled from its coordinate cones. -/
def familyCone (c : ∀ i, Cone (F ⋙ Pi.eval C i)) : Cone F where
  pt i := (c i).pt
  π := { app := fun j i => (c i).π.app j
         naturality := by intros; funext i; exact (c i).π.naturality _ }

/-- The cocone in a dependent product category assembled from its coordinate cocones. -/
def familyCocone (c : ∀ i, Cocone (F ⋙ Pi.eval C i)) : Cocone F where
  pt i := (c i).pt
  ι := { app := fun j i => (c i).ι.app j
         naturality := by intros; funext i; exact (c i).ι.naturality _ }

/-- The universal property of the assembled cone when every coordinate cone is limiting. -/
def familyConeIsLimit {c : ∀ i, Cone (F ⋙ Pi.eval C i)} (hc : ∀ i, IsLimit (c i)) :
    IsLimit (familyCone C F c) where
  lift s i := (hc i).lift ((Pi.eval C i).mapCone s)
  fac s j := by funext i; exact (hc i).fac ((Pi.eval C i).mapCone s) j
  uniq s m hm := by
    funext i
    exact (hc i).uniq ((Pi.eval C i).mapCone s) (m i) (fun j => congr_fun (hm j) i)

/-- The universal property of the assembled cocone when every coordinate cocone is colimiting. -/
def familyCoconeIsColimit {c : ∀ i, Cocone (F ⋙ Pi.eval C i)} (hc : ∀ i, IsColimit (c i)) :
    IsColimit (familyCocone C F c) where
  desc s i := (hc i).desc ((Pi.eval C i).mapCocone s)
  fac s j := by funext i; exact (hc i).fac ((Pi.eval C i).mapCocone s) j
  uniq s m hm := by
    funext i
    exact (hc i).uniq ((Pi.eval C i).mapCocone s) (m i) (fun j => congr_fun (hm j) i)

instance piHasLimitsOfShape [∀ i, HasLimitsOfShape J (C i)] :
    HasLimitsOfShape J (∀ i, C i) where
  has_limit F := HasLimit.mk
    ⟨familyCone C F (fun _ => limit.cone _), familyConeIsLimit C F (fun _ => limit.isLimit _)⟩

instance piHasColimitsOfShape [∀ i, HasColimitsOfShape J (C i)] :
    HasColimitsOfShape J (∀ i, C i) where
  has_colimit F := HasColimit.mk
    ⟨familyCocone C F (fun _ => colimit.cocone _),
      familyCoconeIsColimit C F (fun _ => colimit.isColimit _)⟩

instance evalPreservesLimitsOfShape [∀ i, HasLimitsOfShape J (C i)] (i : I) :
    PreservesLimitsOfShape J (Pi.eval C i) where
  preservesLimit {F} := by
    apply preservesLimit_of_preserves_limit_cone
      (familyConeIsLimit C F (fun j => limit.isLimit (F ⋙ Pi.eval C j)))
    exact limit.isLimit (F ⋙ Pi.eval C i)

instance evalPreservesColimitsOfShape [∀ i, HasColimitsOfShape J (C i)] (i : I) :
    PreservesColimitsOfShape J (Pi.eval C i) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone
      (familyCoconeIsColimit C F (fun j => colimit.isColimit (F ⋙ Pi.eval C j)))
    exact colimit.isColimit (F ⋙ Pi.eval C i)
end Limits

instance piHasFiniteLimits [∀ i, HasFiniteLimits (C i)] : HasFiniteLimits (∀ i, C i) where
  out _ := inferInstance
instance piHasFiniteColimits [∀ i, HasFiniteColimits (C i)] : HasFiniteColimits (∀ i, C i) where
  out _ := inferInstance
instance evalPreservesFiniteLimits [∀ i, HasFiniteLimits (C i)] (i : I) :
    PreservesFiniteLimits (Pi.eval C i) where
  preservesFiniteLimits _ := inferInstance
instance evalPreservesFiniteColimits [∀ i, HasFiniteColimits (C i)] (i : I) :
    PreservesFiniteColimits (Pi.eval C i) where
  preservesFiniteColimits _ := inferInstance

instance piAbelian [∀ i, Abelian (C i)] : Abelian (∀ i, C i) := by
  have : ∀ {X Y : ∀ i, C i} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    apply (isIso_pi_iff _).mpr
    intro i
    change IsIso ((Pi.eval C i).map (Abelian.coimageImageComparison f))
    let e := Abelian.PreservesCoimageImageComparison.iso (Pi.eval C i) f
    exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr inferInstance
  exact Abelian.ofCoimageImageComparisonIsIso

/-- Exactness is tested at each actual coordinate. -/
theorem shortExact_pi_of [∀ i, Abelian (C i)]
    (S : ShortComplex (∀ i, C i))
    (h : ∀ i, (S.map (Pi.eval C i)).ShortExact) : S.ShortExact := by
  have hm : Mono S.f := by
    constructor
    intro Z f g heq
    funext i
    have := (h i).mono_f
    exact (cancel_mono ((S.map (Pi.eval C i)).f)).mp (congr_fun heq i)
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    KernelFork.IsLimit.ofι' S.f S.zero (fun {Z} k hk =>
      ⟨fun i => (h i).fIsKernel.lift (KernelFork.ofι (k i) (congr_fun hk i)), by
        funext i
        exact (h i).fIsKernel.fac (KernelFork.ofι (k i) (congr_fun hk i)) WalkingParallelPair.zero⟩)
  refine { exact := S.exact_of_f_is_kernel hk, mono_f := hm, epi_g := ?_ }
  constructor
  intro Z f g heq
  funext i
  have := (h i).epi_g
  exact (cancel_epi ((S.map (Pi.eval C i)).g)).mp (congr_fun heq i)

theorem isZero_family_iff [∀ i, Abelian (C i)] (M : ∀ i, C i) :
    IsZero M ↔ ∀ i, IsZero (M i) := by
  constructor
  · intro h i
    exact (Pi.eval C i).map_isZero h
  · intro h
    apply (IsZero.iff_id_eq_zero M).mpr
    funext i
    exact (h i).eq_of_src _ _

end PiAbelian

end CategoryTheory.Pi
