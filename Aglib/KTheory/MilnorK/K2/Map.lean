/-
Extracted and mechanically adapted from the private, user-owned R5 source:
https://github.com/kangxyz/r5-lab/blob/1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e/lean/R5Lab/KTheory/MilnorK2/Map.lean
Original Git blob SHA-1: 0ed0027775b5dbbda46704dc538fc11d8c3c873e
Original SHA-256: b1608cf9735d2c0e28a0ddefec3c599684d5fc8116d8c3a9559f54a415f0637b
No upstream license is declared. This copied implementation is NOT covered by
this standalone project's Apache license statement. This local source reuse
provides no authorization for public redistribution. Original source comments
and attribution are retained below. See THIRD_PARTY_NOTICES.md and LICENSE.
-/
module

public import Aglib.KTheory.MilnorK.K2.Basic

-- Preserve the original non-Apache provenance notice rather than invent a license.
set_option linter.style.header false

/-!
# Field functoriality of Milnor K₂

The group `K2 K` is the quotient of
`Additive Kˣ ⊗[ℤ] Additive Kˣ` by the integer span of the Steinberg tensors.
Its symbols are constructed from the tensor quotient. Bilinearity, Steinberg,
the universal property, field functoriality, and sign identities are proved
from this presentation, with no external mathematical premise. Functoriality
and further symbol identities are in the `Map` and `Symbols` modules.

## Source correspondence

Source file: `research/exposes/K2/018/expose.tex`,
`K2-018#sec:k2018-introduction`, lines 63–82, and
`K2-018#lem:k2018-residue-bockstein`, lines 308–339, at baseline commit
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Complete source-file SHA-256:
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
This identity applies to every declaration below.

Formalized scope: auxiliary algebraic foundations for the field symbols used
in the introduction and residue calculation. The introduction's identification
with Quillen field K₂ requires Matsumoto as a separate background theorem;
no Quillen group or Matsumoto comparison is defined here. This module makes
no assertion about arithmetic model images, origin specialization, motivic
comparison, or cohomological Bocksteins.
-/

@[expose] public section

namespace MilnorK.K2

variable (K : Type*) [Field K]

variable {K}

variable {A : Type*} [AddCommGroup A]

variable {L : Type*} [Field L]

/-- A field map induces the natural integer-linear map on its multiplicative units.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def unitsLinear (f : K →+* L) : UnitsAdd K →ₗ[ℤ] UnitsAdd L :=
  (Units.map f.toMonoidHom).toAdditive.toIntLinearMap

/-- Field functoriality descends after proving preservation of the Steinberg generators.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def map (f : K →+* L) : Group K →ₗ[ℤ] Group L :=
  lift ((symbolBilinear L).compl₁₂ (unitsLinear f) (unitsLinear f)) (by
    intro a b hab
    apply steinberg
    change f (a : K) + f (b : K) = 1
    rw [← map_add, hab, map_one])

/-- A field map sends `{a,b}` to the symbol of the image entries.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem map_symbol (f : K →+* L) (a b : Kˣ) :
    map f (symbol a b) = symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) := rfl

/-- The field identity induces the identity on Milnor K₂.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem map_id : map (RingHom.id K) = LinearMap.id := by
  apply linearMap_ext
  intro a b
  simp [map_symbol, Units.map]

variable {M : Type*} [Field M]

/-- Composition of field maps is preserved by Milnor K₂.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem map_comp (f : K →+* L) (g : L →+* M) :
    map (g.comp f) = (map g).comp (map f) := by
  apply linearMap_ext
  intro a b
  simp only [LinearMap.comp_apply, map_symbol]
  congr 1


/-- The additive view of the existing field-induced integer-linear map.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
def mapAdd (f : K →+* L) : Group K →+ Group L := (map f).toAddMonoidHom

/-- The additive field map takes symbols to symbols of the field images.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem mapAdd_symbol (f : K →+* L) (a b : Kˣ) :
    mapAdd f (symbol a b) =
      symbol (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) :=
  map_symbol f a b

/-- The additive field map preserves the identity field homomorphism.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
@[simp] theorem mapAdd_id : mapAdd (RingHom.id K) = AddMonoidHom.id (Group K) :=
  congrArg (fun h : Group K →ₗ[ℤ] Group K => h.toAddMonoidHom) map_id

/-- The additive field map preserves composition of field homomorphisms.
Source: auxiliary symbol algebra for `K2-018#sec:k2018-introduction`,
at the module snapshot documented above. -/
theorem mapAdd_comp (f : K →+* L) (g : L →+* M) :
    mapAdd (g.comp f) = (mapAdd g).comp (mapAdd f) :=
  congrArg (fun h : Group K →ₗ[ℤ] Group M => h.toAddMonoidHom) (map_comp f g)

end MilnorK.K2
