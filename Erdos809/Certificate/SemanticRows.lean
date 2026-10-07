module
public import Erdos809.Certificate.SemanticRows.Rows0000_0099
public import Erdos809.Certificate.SemanticRows.Rows0100_0199
public import Erdos809.Certificate.SemanticRows.Rows0200_0299
public import Erdos809.Certificate.SemanticRows.Rows0300_0399
public import Erdos809.Certificate.SemanticRows.Rows0400_0499
public import Erdos809.Certificate.SemanticRows.Rows0500_0599
public import Erdos809.Certificate.SemanticRows.Rows0600_0699
public import Erdos809.Certificate.SemanticRows.Rows0700_0799
public import Erdos809.Certificate.SemanticRows.Rows0800_0899
public import Erdos809.Certificate.SemanticRows.Rows0900_0999
public import Erdos809.Certificate.SemanticRows.Rows1000_1099
public import Erdos809.Certificate.SemanticRows.Rows1100_1199
public import Erdos809.Certificate.SemanticRows.Rows1200_1299
public import Erdos809.Certificate.SemanticRows.Rows1300_1399
public import Erdos809.Certificate.SemanticRows.Rows1400_1435

@[expose] public section

namespace Erdos809.Certificate.LocalFormula.SemanticRows

noncomputable def allRows : List (Fin 1436) := Rows0000_0099.rows ++ Rows0100_0199.rows ++ Rows0200_0299.rows ++ Rows0300_0399.rows ++ Rows0400_0499.rows ++ Rows0500_0599.rows ++ Rows0600_0699.rows ++ Rows0700_0799.rows ++ Rows0800_0899.rows ++ Rows0900_0999.rows ++ Rows1000_1099.rows ++ Rows1100_1199.rows ++ Rows1200_1299.rows ++ Rows1300_1399.rows ++ Rows1400_1435.rows

set_option maxRecDepth 1000000 in
theorem allRows_complete : allRows = List.finRange 1436 := by decide +kernel

theorem allRows_checked : allRows.all representativeCheck = true := by
  simp only [allRows, List.all_append, Rows0000_0099.rows_checked, Rows0100_0199.rows_checked, Rows0200_0299.rows_checked, Rows0300_0399.rows_checked, Rows0400_0499.rows_checked, Rows0500_0599.rows_checked, Rows0600_0699.rows_checked, Rows0700_0799.rows_checked, Rows0800_0899.rows_checked, Rows0900_0999.rows_checked, Rows1000_1099.rows_checked, Rows1100_1199.rows_checked, Rows1200_1299.rows_checked, Rows1300_1399.rows_checked, Rows1400_1435.rows_checked, Bool.true_and]

theorem allRows_valid (r : Fin 1436) : representativeCheck r = true :=
  List.all_eq_true.mp allRows_checked r (by rw [allRows_complete]; simp)

theorem all_representatives_nonnegative (r : Fin 1436) :
    0 ≤ symmetrizedDeficit (LocalGraph.Data.representatives r) :=
  representativeCheck_sound r (allRows_valid r)

end Erdos809.Certificate.LocalFormula.SemanticRows
