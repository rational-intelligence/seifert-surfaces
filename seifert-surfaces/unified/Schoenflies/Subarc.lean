import DifferentialGeometry.External.Schoenflies.Subarc
import ExactPaidSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
/- Finite declaration-owner adapter. All duplicated exported heads resolve to the recorded DG owners; additional exact closed declarations are retained below. -/
attribute [simp] Schoenflies.reparam_zero Schoenflies.reparam_one Schoenflies.subarc_zero Schoenflies.subarc_one
