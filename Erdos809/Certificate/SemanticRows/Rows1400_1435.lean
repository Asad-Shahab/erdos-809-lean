module
public import Erdos809.Certificate.LocalFormulaReflection

@[expose] public section

/-! Direct kernel checks of the actual finite local formulas.
No Python arithmetic is trusted by these theorem statements. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Erdos809.Certificate.LocalFormula.SemanticRows.Rows1400_1435

theorem row_1400 : representativeCheck 1400 = true := by decide +kernel

theorem row_1401 : representativeCheck 1401 = true := by decide +kernel

theorem row_1402 : representativeCheck 1402 = true := by decide +kernel

theorem row_1403 : representativeCheck 1403 = true := by decide +kernel

theorem row_1404 : representativeCheck 1404 = true := by decide +kernel

theorem row_1405 : representativeCheck 1405 = true := by decide +kernel

theorem row_1406 : representativeCheck 1406 = true := by decide +kernel

theorem row_1407 : representativeCheck 1407 = true := by decide +kernel

theorem row_1408 : representativeCheck 1408 = true := by decide +kernel

theorem row_1409 : representativeCheck 1409 = true := by decide +kernel

theorem row_1410 : representativeCheck 1410 = true := by decide +kernel

theorem row_1411 : representativeCheck 1411 = true := by decide +kernel

theorem row_1412 : representativeCheck 1412 = true := by decide +kernel

theorem row_1413 : representativeCheck 1413 = true := by decide +kernel

theorem row_1414 : representativeCheck 1414 = true := by decide +kernel

theorem row_1415 : representativeCheck 1415 = true := by decide +kernel

theorem row_1416 : representativeCheck 1416 = true := by decide +kernel

theorem row_1417 : representativeCheck 1417 = true := by decide +kernel

theorem row_1418 : representativeCheck 1418 = true := by decide +kernel

theorem row_1419 : representativeCheck 1419 = true := by decide +kernel

theorem row_1420 : representativeCheck 1420 = true := by decide +kernel

theorem row_1421 : representativeCheck 1421 = true := by decide +kernel

theorem row_1422 : representativeCheck 1422 = true := by decide +kernel

theorem row_1423 : representativeCheck 1423 = true := by decide +kernel

theorem row_1424 : representativeCheck 1424 = true := by decide +kernel

theorem row_1425 : representativeCheck 1425 = true := by decide +kernel

theorem row_1426 : representativeCheck 1426 = true := by decide +kernel

theorem row_1427 : representativeCheck 1427 = true := by decide +kernel

theorem row_1428 : representativeCheck 1428 = true := by decide +kernel

theorem row_1429 : representativeCheck 1429 = true := by decide +kernel

theorem row_1430 : representativeCheck 1430 = true := by decide +kernel

theorem row_1431 : representativeCheck 1431 = true := by decide +kernel

theorem row_1432 : representativeCheck 1432 = true := by decide +kernel

theorem row_1433 : representativeCheck 1433 = true := by decide +kernel

theorem row_1434 : representativeCheck 1434 = true := by decide +kernel

theorem row_1435 : representativeCheck 1435 = true := by decide +kernel

noncomputable def rows : List (Fin 1436) := [1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435]

theorem rows_checked : rows.all representativeCheck = true := by
  simp only [rows, List.all_cons, List.all_nil, row_1400, row_1401, row_1402, row_1403, row_1404, row_1405, row_1406, row_1407, row_1408, row_1409, row_1410, row_1411, row_1412, row_1413, row_1414, row_1415, row_1416, row_1417, row_1418, row_1419, row_1420, row_1421, row_1422, row_1423, row_1424, row_1425, row_1426, row_1427, row_1428, row_1429, row_1430, row_1431, row_1432, row_1433, row_1434, row_1435, Bool.true_and]

end Erdos809.Certificate.LocalFormula.SemanticRows.Rows1400_1435
