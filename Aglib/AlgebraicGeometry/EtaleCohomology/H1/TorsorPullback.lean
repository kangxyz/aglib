/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ExtensionFiberClass
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.TorsorSum

/-!
# Actual inverse-image extensions and their torsor fibres

Construction for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The exact abelian inverse-image
functor is applied to the constructed torsor extension. Constant integers
are transported by the canonical constant-sheaf isomorphism. The class of
its actual augmentation-one fibre is the previously constructed H¹ pullback.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge
section TorsorIsomorphisms
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X} {P Q : Torsor L}

/-- A same-coefficient equivariant torsor morphism is injective on every section set. -/
theorem Torsor.Hom.injective (r : Torsor.Hom (𝟙 L) P Q) (U : X.Etaleᵒᵖ) :
    Function.Injective (r.map.hom.app U) := by
  intro s t h
  obtain ⟨a, ha, _⟩ := P.unique_transport U s t
  have he : Q.action U a (r.map.hom.app U s) = r.map.hom.app U t := by
    exact (r.equivariant U a s).symm.trans (congrArg (r.map.hom.app U) ha)
  have hz : a = 0 := (Q.unique_transport U (r.map.hom.app U s)
    (r.map.hom.app U s)).unique (he.trans h.symm) (Q.zero_action U _)
  simpa only [hz, P.zero_action] using ha

/-- Local nonemptiness of the source proves local surjectivity. -/
instance Torsor.Hom.locallySurjective (r : Torsor.Hom (𝟙 L) P Q) :
    Sheaf.IsLocallySurjective r.map where
  imageSieve_mem {U} t := by
    refine (Scheme.smallEtaleTopology X).superset_covering ?_ (P.locally_nonempty U)
    rintro V f ⟨p⟩
    obtain ⟨a, ha, _⟩ := Q.unique_transport (op V) (r.map.hom.app (op V) p)
      (Q.carrier.obj.map f.op t)
    refine ⟨P.action (op V) a p, ?_⟩
    exact (r.equivariant (op V) a p).trans ha

/-- The actual underlying sheaf map of a same-coefficient torsor map is invertible. -/
instance Torsor.Hom.map_isIso (r : Torsor.Hom (𝟙 L) P Q) : IsIso r.map := by
  let : Presheaf.IsLocallyInjective (Scheme.smallEtaleTopology X) r.map.hom :=
    Presheaf.isLocallyInjective_of_injective _ _ (r.injective)
  let : Mono r.map := Sheaf.mono_of_isLocallyInjective r.map
  let : Epi r.map := inferInstance
  exact isIso_of_mono_of_epi r.map

/-- Genuine torsor maps are actual equivariant isomorphisms, without 03AJ. -/
noncomputable def Torsor.Hom.toIso (r : Torsor.Hom (𝟙 L) P Q) : Torsor.Iso P Q where
  carrierIso := asIso r.map
  equivariant := r.equivariant

/-- The original torsor maps canonically to the one-fibre of its constructed extension. -/
noncomputable def torsorCanonicalExtensionMap (P : Torsor L) :
    Torsor.Hom (𝟙 L) P
      (extensionFiberTorsor (torsorExtension P) (constantIntegerOne X)
        (torsorExtension_shortExact P)) := by
  have h : torsorPushout P (𝟙 L) =
      extensionFiberTorsor (torsorExtension P) (constantIntegerOne X)
        (torsorExtension_shortExact P) := by
    unfold torsorPushout torsorCoefficientExtension
    simp only [torsorAugmentationComplex]
    rfl
  exact h ▸ torsorPushoutMap P (𝟙 L)

/-- The canonical extension's augmentation-one fibre recovers the actual torsor. -/
noncomputable def torsorCanonicalExtensionIso (P : Torsor L) :
    Torsor.Iso P (extensionFiberTorsor (torsorExtension P) (constantIntegerOne X)
      (torsorExtension_shortExact P)) :=
  (torsorCanonicalExtensionMap P).toIso

end TorsorIsomorphisms

variable {X S : Scheme.{u}} (f : S ⟶ X) {L : AbelianSheaf.{u, u + 1} X}
variable (P : Torsor L)

/-- Canonical constant-integer transport for the actual inverse image. -/
abbrev inverseImageIntegerIso : (inverseImage f).obj (constantIntegerSheaf X) ≅
    constantIntegerSheaf S :=
  (inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- Projection of the actual inverse-image extension onto constant integers. -/
def torsorInverseImageProjection :
    (inverseImage f).obj (torsorExtension P).X₂ ⟶ constantIntegerSheaf S :=
  (inverseImage f).map (torsorExtension P).g ≫ (inverseImageIntegerIso f).hom

/-- Exact inverse image preserves the augmentation relation. -/
theorem torsorInverseImage_zero :
    (inverseImage f).map (torsorExtension P).f ≫ torsorInverseImageProjection f P = 0 := by
  rw [torsorInverseImageProjection, ← Category.assoc, ← Functor.map_comp,
    ShortComplex.zero, Functor.map_zero, zero_comp]

/-- The actual inverse-image extension with canonical constant-ℤ transport. -/
def torsorInverseImageExtension : ShortComplex (AbelianSheaf.{u, u + 1} S) :=
  ShortComplex.mk ((inverseImage f).map (torsorExtension P).f)
    (torsorInverseImageProjection f P) (torsorInverseImage_zero f P)

/-- The canonical transport is an isomorphism of actual short complexes. -/
def torsorInverseImageExtensionIso :
    (torsorExtension P).map (inverseImage f) ≅ torsorInverseImageExtension f P :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (inverseImageIntegerIso f)
    (by simp [torsorInverseImageExtension])
    (by simp [torsorInverseImageExtension, torsorInverseImageProjection])

/-- Short exactness is preserved, without any exactness premise for the scheme map. -/
theorem torsorInverseImageExtension_shortExact : (torsorInverseImageExtension f P).ShortExact :=
  ShortComplex.shortExact_of_iso (torsorInverseImageExtensionIso f P)
    ((torsorExtension_shortExact P).map_of_exact (inverseImage f))

/-- A genuine torsor formed from the actual inverse-image extension. -/
def torsorInverseImageFiber : Torsor ((inverseImage f).obj L) :=
  extensionFiberTorsor (torsorInverseImageExtension f P) (constantIntegerOne S)
    (torsorInverseImageExtension_shortExact f P)

section ExtClass
universe w w'
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The canonical Ext class of the inverse-image extension uses the inverse
constant transport in the contravariant first Ext variable. -/
theorem torsorInverseImageExtension_extClass :
    (torsorInverseImageExtension_shortExact f P).extClass =
      h1Pullback f L (torsorExtClass P) := by
  have hn := ShortComplex.ShortExact.extClass_naturality
    (torsorInverseImageExtension_shortExact f P)
    ((torsorExtension_shortExact P).map_of_exact (inverseImage f))
    (torsorInverseImageExtensionIso f P).inv
  change (torsorInverseImageExtension_shortExact f P).extClass.comp
      (Abelian.Ext.mk₀ (𝟙 _)) (add_zero 1) =
    (Abelian.Ext.mk₀ (inverseImageIntegerIso f).inv).comp
      ((torsorExtension_shortExact P).map_of_exact (inverseImage f)).extClass (zero_add 1) at hn
  rw [Abelian.Ext.comp_mk₀_id, ← Abelian.Ext.mapExactFunctor_extClass] at hn
  exact hn

/-- Canonical class compatibility for the genuinely constructed inverse-image
extension fibre. Identification with the set-sheaf inverse image is separate. -/
theorem torsorExtClass_inverseImageFiber :
    torsorExtClass (torsorInverseImageFiber f P) = h1Pullback f L (torsorExtClass P) := by
  rw [torsorInverseImageFiber]
  exact (torsorExtClass_extensionFiber _ _ _ (torsorInverseImageExtension_shortExact f P)).trans
    (torsorInverseImageExtension_extClass f P)

end ExtClass
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bc3efa93f0550d2614c6d83cecfc91235de388d6f1955901118d6d6c1ea84b0a.
Definitions, hypotheses and universes are retained modulo native names. -/
