module

public import Definitions.MTT.Def_MTT_ParabolicCohomology
public import Mathlib.RepresentationTheory.Coinduced

@[expose] public section publicSection

/-! # General coefficients for full modular-group parabolic cohomology

The coefficient representation can be arbitrary. The central fixed
subrepresentation will be used for the coinduced Gamma1 coefficient module.
-/

noncomputable section

namespace Rep

variable {G : Type} [Group G] (A : Rep ℂ G) (z : G) (hz : ∀ g, z * g = g * z)

def centralFixed : Submodule ℂ A := (A.ρ z - LinearMap.id).ker

theorem mem_centralFixed (v : A) : v ∈ centralFixed A z ↔ A.ρ z v = v := by
  simp only [centralFixed, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

include hz in
theorem centralFixed_stable (g : G) :
    centralFixed A z ≤ (centralFixed A z).comap (A.ρ g) := by
  intro v hv
  rw [Submodule.mem_comap, mem_centralFixed]
  have hv' := (mem_centralFixed A z v).mp hv
  calc
    A.ρ z (A.ρ g v) = A.ρ (z * g) v :=
      (congrArg (fun f : Module.End ℂ A => f v) (A.ρ.map_mul z g)).symm
    _ = A.ρ (g * z) v := by rw [hz]
    _ = A.ρ g (A.ρ z v) :=
      congrArg (fun f : Module.End ℂ A => f v) (A.ρ.map_mul g z)
    _ = A.ρ g v := by rw [hv']

abbrev centralFixedRep : Rep ℂ G :=
  A.subrepresentation (centralFixed A z) (centralFixed_stable A z hz)

end Rep

namespace MTT.Cohomology

open groupCohomology

variable (A : Rep ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ))

def fullParabolicCocycles :
    Submodule ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ → A) :=
  cocycles₁ A ⊓ ⨅ (x : Cusp) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (_ : cuspAct g x = x),
      (LinearMap.range (A.ρ g - LinearMap.id)).comap (LinearMap.proj g)

def fullParabolicCoboundaries : Submodule ℂ (fullParabolicCocycles A) :=
  (coboundaries₁ A).comap (fullParabolicCocycles A).subtype

abbrev FullParabolicH1 := fullParabolicCocycles A ⧸ fullParabolicCoboundaries A

theorem mem_fullParabolicCocycles_iff (c : Matrix.SpecialLinearGroup (Fin 2) ℤ → A) :
    c ∈ fullParabolicCocycles A ↔ c ∈ cocycles₁ A ∧
      ∀ (x : Cusp) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ), cuspAct g x = x →
        c g ∈ LinearMap.range (A.ρ g - LinearMap.id) := by
  simp only [fullParabolicCocycles, Submodule.mem_inf, Submodule.mem_iInf,
    Submodule.mem_comap, LinearMap.proj_apply]

theorem neg_one_central (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (-1) * g = g * (-1) := by simp only [neg_mul, one_mul, mul_neg, mul_one]

abbrev centralCoinduced (N n : ℕ) := Rep.centralFixedRep
  (Rep.coind (CongruenceSubgroup.Gamma1 N).subtype (gammaOneRep N n)) (-1) neg_one_central

end MTT.Cohomology


end

end publicSection
