import Mathlib
import RequestProject.NonHalting
import RequestProject.Excursion
import RequestProject.Carry
import RequestProject.CarryP1
import RequestProject.Fractal
import RequestProject.CarryU21
import RequestProject.Flat
import RequestProject.FlatP1
import RequestProject.TurnU2
import RequestProject.CarryU2b
import RequestProject.CarryV
import RequestProject.CarryP1V
import RequestProject.CarryU21b
import RequestProject.CarryU21bV
import RequestProject.CarryU21V
import RequestProject.Start
import RequestProject.FracP1
import RequestProject.FracP1s
import RequestProject.U2bV
import RequestProject.BlankRight
import RequestProject.Unfold
import RequestProject.NarrowGap
import RequestProject.Reduce

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
