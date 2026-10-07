module
public import Erdos809.Certificate.Links.Block00
public import Erdos809.Certificate.Links.Block01
public import Erdos809.Certificate.Links.Block02
public import Erdos809.Certificate.Links.Block03
public import Erdos809.Certificate.Links.Block04
public import Erdos809.Certificate.Links.Block05
public import Erdos809.Certificate.Links.Block06
public import Erdos809.Certificate.Links.Block07
public import Erdos809.Certificate.Links.Block08
public import Erdos809.Certificate.Links.Block09
public import Erdos809.Certificate.Links.Block10
public import Erdos809.Certificate.Links.Block11
public import Erdos809.Certificate.Links.Block12
public import Erdos809.Certificate.Links.Block13
public import Erdos809.Certificate.Links.Block14
public import Erdos809.Certificate.FlagData

@[expose] public section

/-! The concrete PSD matrices exposed at exactly the common coefficient scale.
The dependent type dimensions preserve the frozen type order.
-/

namespace Erdos809.Certificate.LinkedMatrices

noncomputable def rootNumerator : Matrix (Fin 28) (Fin 28) ℤ := Link00.Qnumerator

noncomputable def rootReal : Matrix (Fin 28) (Fin 28) ℝ := Link00.Qreal

theorem rootReal_posSemidef : rootReal.PosSemidef := Link00.Qreal_posSemidef

noncomputable def typeNumerator (t : Fin 14) :
    Matrix (Fin (FlagData.typeSize t)) (Fin (FlagData.typeSize t)) ℤ :=
  Fin.cases Link01.Qnumerator (Fin.cases Link02.Qnumerator (Fin.cases Link03.Qnumerator (Fin.cases Link04.Qnumerator (Fin.cases Link05.Qnumerator (Fin.cases Link06.Qnumerator (Fin.cases Link07.Qnumerator (Fin.cases Link08.Qnumerator (Fin.cases Link09.Qnumerator (Fin.cases Link10.Qnumerator (Fin.cases Link11.Qnumerator (Fin.cases Link12.Qnumerator (Fin.cases Link13.Qnumerator (Fin.cases Link14.Qnumerator (fun i => Fin.elim0 i)))))))))))))) t

noncomputable def typeReal (t : Fin 14) :
    Matrix (Fin (FlagData.typeSize t)) (Fin (FlagData.typeSize t)) ℝ :=
  fun i j => (typeNumerator t i j : ℝ) / Coefficients.scale

theorem typeReal_posSemidef (t : Fin 14) : Matrix.PosSemidef (typeReal t) := by
  fin_cases t
  · exact Link01.Qreal_posSemidef
  · exact Link02.Qreal_posSemidef
  · exact Link03.Qreal_posSemidef
  · exact Link04.Qreal_posSemidef
  · exact Link05.Qreal_posSemidef
  · exact Link06.Qreal_posSemidef
  · exact Link07.Qreal_posSemidef
  · exact Link08.Qreal_posSemidef
  · exact Link09.Qreal_posSemidef
  · exact Link10.Qreal_posSemidef
  · exact Link11.Qreal_posSemidef
  · exact Link12.Qreal_posSemidef
  · exact Link13.Qreal_posSemidef
  · exact Link14.Qreal_posSemidef

theorem rootReal_apply (i j : Fin 28) :
    rootReal i j = (rootNumerator i j : ℝ) / Coefficients.scale := rfl

end Erdos809.Certificate.LinkedMatrices
