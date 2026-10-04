import Definitions.MTT.Def_MTT_Cohomology
noncomputable section
open scoped BigOperators
namespace MTT.Cohomology

/-- The data of a boundary symbol: a `Γ₁(N)`-equivariant `Sym^n`-valued function on cusps,
i.e. an element of `Hom_Γ(Div(P¹(ℚ)), Sym^n(R²))`. -/
def IsBoundaryDatum (N n : ℕ) {R : Type*} [CommRing R] (Φ : Cusp → Binary R) : Prop :=
  (∀ x, Φ x ∈ Sym R n) ∧
  ∀ γ : CongruenceSubgroup.Gamma1 N, ∀ x, Φ (cuspAct γ.val x) = act γ.val.val (Φ x)

/-- The boundary cochain of `Φ`: the restriction of `Φ` along `Div⁰ ⊂ Div`,
`(x, y) ↦ Φ y − Φ x`, with `(x, y)` representing `[x] − [y]`. -/
def boundaryCochain {R : Type*} [CommRing R] (Φ : Cusp → Binary R) :
    (Cusp × Cusp) → Binary R :=
  fun D => Φ D.2 - Φ D.1

end MTT.Cohomology
