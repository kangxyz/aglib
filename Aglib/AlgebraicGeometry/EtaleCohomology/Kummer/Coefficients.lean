/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicativeGroup
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedCoefficients
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual small-etale multiplicative and root coefficient sheaves

Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.

C4 construction prerequisite, `K2-018#lem:k2018-geometric-exact-order`,
frozen source basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The coefficients are A's actual represented small-etale abelian sheaves of
our proved multiplicative group and root-equalizer group schemes. Their
sections are identified additively with actual global units and roots of
unity. Restrictions, inclusion and the nth-power map are proved to be the
literal scheme/unit maps on every test object. The root inclusion is mono,
and its categorical kernel universal property is proved by explicit lifts.
Annihilation and the zero level-one coefficient are also proved.

The only retained standard family is EtalePowerSurjectivity, Stacks03PL:
for every actual scheme, positive n invertible in its actual global sections,
the literal power map is Epi IN THE SMALL-ETALE ABELIAN-SHEAF CATEGORY.
The positive-integer convention and invertibility condition were checked on
the primary source on 2026-10-09. Short exactness is derived from that
surjectivity and the independently proved kernel. There is no Picard or
H1-classification premise or conclusion in this coefficient module.

Finite etaleness of the actual root scheme is proved separately in
GroupSchemes/RootsFiniteEtale; it is not assumed for these constructions.
Multiplicative weight one here is distinct from arithmetic weight two.
-/

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.Coefficients` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`885d021782d526810bd72929b140c837c32716cbe9b9a524daab65abd3ab6552`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
namespace GroupCohomology.Kummer.Coefficients
open AlgebraicGeometry.Scheme.Group.MultiplicativeGroup
open _root_.AlgebraicGeometry.Scheme.EtaleCohomology _root_.CategoryTheory.Functor.LargePresheaf
universe u

/-- The multiplicative equivalence between maps to the multiplicative group and global units. -/
def unitsMulEquiv (X : Scheme.{u}) (U : Over X) :
    letI := commGroup X
    (U ⟶ scheme X) ≃* Γ(U.left, ⊤)ˣ := by
  letI := commGroup X
  exact { sectionsUnitsEquiv X U with map_mul' := sectionsUnitsEquiv_mul X U }

/-- The multiplicative equivalence between maps to the roots scheme and global roots of unity. -/
def rootsMulEquiv (X : Scheme.{u}) (n : ℕ) (U : Over X) :
    letI := rootsCommGroup X n
    (U ⟶ rootsScheme X n) ≃* rootsOfUnity n Γ(U.left, ⊤) := by
  letI := rootsCommGroup X n
  exact { rootsHomEquiv X n U with
    map_mul' := fun a b => ((yonedaMonObjIsoOfRepresentableBy (rootsScheme X n)
      (rootsFunctor X n ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat)
      (rootsRepresentable X n)).hom.app (op U)).hom.map_mul a b }

/-- The actual multiplicative group on the small etale site, in additive spelling. -/
def gm (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X := representedSheaf (groupScheme X)

/-- The actual represented nth-root coefficient sheaf. -/
def mu (X : Scheme.{u}) (n : ℕ) : AbelianSheaf.{u, u + 1} X :=
  representedSheaf (rootsGroupScheme X n)

/-- Sections of the multiplicative coefficient sheaf as global units, written additively. -/
def unitsSections (X : Scheme.{u}) (U : X.Etaleᵒᵖ) :
    (gm X).obj.obj U ≃+ Additive Γ(U.unop.left, ⊤)ˣ := by
  letI := commGroup X
  exact AddEquiv.ulift.trans (unitsMulEquiv X ((Scheme.Etale.forget X).obj U.unop)).toAdditive

/-- Sections of the root coefficient sheaf as global roots of unity, written additively. -/
def rootsSections (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ) :
    (mu X n).obj.obj U ≃+ Additive (rootsOfUnity n Γ(U.unop.left, ⊤)) := by
  letI := rootsCommGroup X n
  exact AddEquiv.ulift.trans (rootsMulEquiv X n ((Scheme.Etale.forget X).obj U.unop)).toAdditive

theorem unitsSections_naturality (X : Scheme.{u}) {U V : X.Etaleᵒᵖ}
    (f : U ⟶ V) (a : (gm X).obj.obj U) :
    (unitsSections X V ((gm X).obj.map f a)).toMul =
      Units.map f.unop.left.appTop.hom.toMonoidHom (unitsSections X U a).toMul := by
  exact (unitsRepresentable X).homEquiv_comp ((Scheme.Etale.forget X).map f.unop) a.down.toMul

theorem rootsSections_naturality (X : Scheme.{u}) (n : ℕ) {U V : X.Etaleᵒᵖ}
    (f : U ⟶ V) (a : (mu X n).obj.obj U) :
    ((rootsSections X n V ((mu X n).obj.map f a)).toMul : Γ(V.unop.left, ⊤)ˣ) =
      Units.map f.unop.left.appTop.hom.toMonoidHom
        ((rootsSections X n U a).toMul : Γ(U.unop.left, ⊤)ˣ) := by
  exact congrArg Subtype.val ((rootsRepresentable X n).homEquiv_comp
    ((Scheme.Etale.forget X).map f.unop) a.down.toMul)

/-- The literal nth-power map, expressed additively. -/
def power (X : Scheme.{u}) (n : ℕ) : gm X ⟶ gm X := n • 𝟙 (gm X)

theorem power_apply (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ)
    (a : (gm X).obj.obj U) :
    (unitsSections X U ((power X n).hom.app U a)).toMul =
      (unitsSections X U a).toMul ^ n := by
  change (unitsSections X U (n • a)).toMul = _
  rw [map_nsmul]
  rfl

/-- The additive nth-power map is the actual scheme power map on every section. -/
theorem power_apply_scheme (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ)
    (a : (gm X).obj.obj U) :
    ((power X n).hom.app U a).down.toMul = a.down.toMul ≫ powerMap X n := by
  apply (sectionsUnitsEquiv X ((Scheme.Etale.forget X).obj U.unop)).injective
  exact (power_apply X n U a).trans (powerMap_comp X n _ a.down.toMul).symm

/-- The inclusion of `n`th roots of unity into the unit group, written additively. -/
def rootSubtype (R : Type u) [CommRing R] (n : ℕ) :
    Additive (rootsOfUnity n R) →+ Additive Rˣ where
  toFun a := Additive.ofMul a.toMul.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual root inclusion, defined through the proved section coordinates. -/
def inclusion (X : Scheme.{u}) (n : ℕ) : mu X n ⟶ gm X where
  hom := {
    app U := AddCommGrpCat.ofHom ((unitsSections X U).symm.toAddMonoidHom.comp
      ((rootSubtype Γ(U.unop.left, ⊤) n).comp (rootsSections X n U).toAddMonoidHom))
    naturality {U V} f := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      apply (unitsSections X V).injective
      apply Additive.toMul.injective
      change (unitsSections X V ((unitsSections X V).symm
        (rootSubtype _ n (rootsSections X n V ((mu X n).obj.map f a))))).toMul =
        (unitsSections X V ((gm X).obj.map f
          ((unitsSections X U).symm (rootSubtype _ n (rootsSections X n U a))))).toMul
      rw [AddEquiv.apply_symm_apply, unitsSections_naturality, AddEquiv.apply_symm_apply]
      exact rootsSections_naturality X n f a }

@[simp] theorem inclusion_apply (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ)
    (a : (mu X n).obj.obj U) :
    (unitsSections X U ((inclusion X n).hom.app U a)).toMul =
      ((rootsSections X n U a).toMul : Γ(U.unop.left, ⊤)ˣ) :=
  congrArg Additive.toMul ((unitsSections X U).apply_symm_apply _)

theorem inclusion_apply_scheme (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ)
    (a : (mu X n).obj.obj U) :
    ((inclusion X n).hom.app U a).down.toMul = a.down.toMul ≫ rootsInclusion X n := by
  apply (sectionsUnitsEquiv X ((Scheme.Etale.forget X).obj U.unop)).injective
  exact inclusion_apply X n U a

theorem inclusion_app_injective (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ) :
    Function.Injective ((inclusion X n).hom.app U) := by
  intro a b h
  apply (rootsSections X n U).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (inclusion_apply X n U a).symm.trans
    ((congrArg (fun z => (unitsSections X U z).toMul) h).trans (inclusion_apply X n U b))

instance inclusion_mono (X : Scheme.{u}) (n : ℕ) : Mono (inclusion X n) where
  right_cancellation g h e := by
    ext U a
    apply inclusion_app_injective X n U
    exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app U) e) a

theorem inclusion_power (X : Scheme.{u}) (n : ℕ) : inclusion X n ≫ power X n = 0 := by
  ext U a
  apply (unitsSections X U).injective
  apply Additive.toMul.injective
  change (unitsSections X U ((power X n).hom.app U ((inclusion X n).hom.app U a))).toMul =
    (unitsSections X U 0).toMul
  rw [power_apply, inclusion_apply, map_zero]
  exact (rootsSections X n U a).toMul.property


/-- A unit section whose literal nth power is one gives a unique root section. -/
def rootSection (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ)
    (a : (gm X).obj.obj U) (h : (power X n).hom.app U a = 0) : (mu X n).obj.obj U :=
  (rootsSections X n U).symm (Additive.ofMul ⟨(unitsSections X U a).toMul, by
    have h' := congrArg (fun z => (unitsSections X U z).toMul) h
    rw [power_apply, map_zero] at h'
    exact h'⟩)

@[simp] theorem inclusion_rootSection (X : Scheme.{u}) (n : ℕ) (U : X.Etaleᵒᵖ)
    (a : (gm X).obj.obj U) (h : (power X n).hom.app U a = 0) :
    (inclusion X n).hom.app U (rootSection X n U a h) = a := by
  apply (unitsSections X U).injective
  apply Additive.toMul.injective
  rw [inclusion_apply]
  change ((rootsSections X n U ((rootsSections X n U).symm _)).toMul : Γ(U.unop.left, ⊤)ˣ) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

theorem inclusion_naturality (X : Scheme.{u}) (n : ℕ) {U V : X.Etaleᵒᵖ}
    (f : U ⟶ V) (a : (mu X n).obj.obj U) :
    (inclusion X n).hom.app V ((mu X n).obj.map f a) =
      (gm X).obj.map f ((inclusion X n).hom.app U a) :=
  ConcreteCategory.congr_hom ((inclusion X n).hom.naturality f) a

theorem kernel_condition_section (X : Scheme.{u}) (n : ℕ) {P : AbelianSheaf.{u, u + 1} X}
    (φ : P ⟶ gm X) (h : φ ≫ power X n = 0) (U : X.Etaleᵒᵖ) (a : P.obj.obj U) :
    (power X n).hom.app U (φ.hom.app U a) = 0 :=
  ConcreteCategory.congr_hom (congrArg (fun q => q.hom.app U) h) a

/-- The actual universal lift into the root subsheaf. -/
def kernelLift (X : Scheme.{u}) (n : ℕ) {P : AbelianSheaf.{u, u + 1} X}
    (φ : P ⟶ gm X) (h : φ ≫ power X n = 0) : P ⟶ mu X n where
  hom := {
    app U := AddCommGrpCat.ofHom {
      toFun a := rootSection X n U (φ.hom.app U a) (kernel_condition_section X n φ h U a)
      map_zero' := by
        apply inclusion_app_injective X n U
        rw [inclusion_rootSection, map_zero, map_zero]
      map_add' a b := by
        apply inclusion_app_injective X n U
        rw [inclusion_rootSection, map_add, map_add, inclusion_rootSection, inclusion_rootSection] }
    naturality {U V} f := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro a
      apply inclusion_app_injective X n V
      change (inclusion X n).hom.app V (rootSection X n V _
        (kernel_condition_section X n φ h V (P.obj.map f a))) =
        (inclusion X n).hom.app V ((mu X n).obj.map f (rootSection X n U _
          (kernel_condition_section X n φ h U a)))
      rw [inclusion_rootSection, inclusion_naturality, inclusion_rootSection]
      exact ConcreteCategory.congr_hom (φ.hom.naturality f) a }

@[simp] theorem kernelLift_inclusion (X : Scheme.{u}) (n : ℕ) {P : AbelianSheaf.{u, u + 1} X}
    (φ : P ⟶ gm X) (h : φ ≫ power X n = 0) : kernelLift X n φ h ≫ inclusion X n = φ := by
  ext U a
  exact inclusion_rootSection X n U _ (kernel_condition_section X n φ h U a)

/-- The represented root sheaf is the categorical kernel of the actual power map. -/
def kernelIsLimit (X : Scheme.{u}) (n : ℕ) :
    IsLimit (KernelFork.ofι (inclusion X n) (inclusion_power X n)) :=
  KernelFork.IsLimit.ofι' _ _ (fun φ h => ⟨kernelLift X n φ h, kernelLift_inclusion X n φ h⟩)

/-- The retained generic etale local-root theorem, Stacks 03PL. This is Epi
in the actual small-etale category of abelian sheaves, not in schemes. -/
def EtalePowerSurjectivity : Prop :=
  ∀ (X : Scheme.{u}) (n : ℕ), 0 < n → IsUnit (n : Γ(X, ⊤)) → Epi (power X n)

/-- The actual Kummer short complex. -/
def sequence (X : Scheme.{u}) (n : ℕ) : ShortComplex (AbelianSheaf.{u, u + 1} X) :=
  ShortComplex.mk (inclusion X n) (power X n) (inclusion_power X n)

theorem sequence_exact (X : Scheme.{u}) (n : ℕ) : (sequence X n).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (kernelIsLimit X n)

/-- All curve-independent short exactness consequences of the retained local-root theorem. -/
theorem sequence_shortExact (h : EtalePowerSurjectivity.{u}) (X : Scheme.{u}) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) : (sequence X n).ShortExact := by
  let : Epi (sequence X n).g := h X n hn hinv
  let : Mono (sequence X n).f := inclusion_mono X n
  exact ⟨sequence_exact X n⟩

theorem mu_killedBy (X : Scheme.{u}) (n : ℕ) : KilledBy n (mu X n) := by
  ext U a
  apply inclusion_app_injective X n U
  change (inclusion X n).hom.app U (n • a) = (inclusion X n).hom.app U 0
  rw [map_nsmul, map_zero]
  exact ConcreteCategory.congr_hom
    (congrArg (fun q => q.hom.app U) (inclusion_power X n)) a

theorem mu_one_isZero (X : Scheme.{u}) : IsZero (mu X 1) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  simpa only [KilledBy, one_nsmul] using mu_killedBy X 1


end GroupCohomology.Kummer.Coefficients
