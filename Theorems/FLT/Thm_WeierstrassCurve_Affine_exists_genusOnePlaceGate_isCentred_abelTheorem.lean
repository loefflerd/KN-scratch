import Definitions.FLT.Def_WeierstrassCurve_GenusOnePlaceGateCentred

theorem WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_abelTheorem
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve.Affine F)
    [W.IsElliptic] :
    ∃ g : WeierstrassCurve.Affine.GenusOnePlaceGate W,
      @WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred F _ W g ∧
      @WeierstrassCurve.Affine.AbelTheorem F _ _ g _ := by sorry
