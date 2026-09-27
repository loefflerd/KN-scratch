import Definitions.MTT.Def_MTT_ParabolicCohomology

/-! # Translation-normalized parabolic cocycles -/

noncomputable section

namespace MTT.Cohomology

/-- The standard translation belongs to every Gamma1(N). -/
def gammaOneT (N : ℕ) : CongruenceSubgroup.Gamma1 N :=
  ⟨ModularGroup.T, by
    rw [CongruenceSubgroup.Gamma1_mem]
    norm_num [ModularGroup.T]⟩

/-- Parabolic cocycles normalized to vanish on the standard translation. -/
def normalizedParabolic (N n : ℕ) : Submodule ℂ (parabolicCocycles N n) :=
  LinearMap.ker ((LinearMap.proj (gammaOneT N)).comp (parabolicCocycles N n).subtype)

/-- The canonical map from normalized representatives to parabolic cohomology. -/
def normalizedToH1 (N n : ℕ) : normalizedParabolic N n →ₗ[ℂ] ParabolicH1 N n :=
  (parabolicCoboundaries N n).mkQ.comp (normalizedParabolic N n).subtype

end MTT.Cohomology

