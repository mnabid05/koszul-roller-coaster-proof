import Conjectures

#print axioms RollerOrder.positive_profile
#print axioms RollerRealization.realize_above
#print axioms RollerShelling.shelling_witness
#print axioms RollerCoaster.every_order_of_faces
#print axioms RollerAlgebraRealization.every_order
#print axioms RollerAlgebraRealization.bar_augmentation_kernel
#print axioms RollerKoszul.BasisGrading.reduced_exact
#print axioms RollerKoszul.AlgebraBarWitness.actual_exact
#print axioms RollerFiltration.whiskered_koszul
#print axioms KoszulRollerCoaster.conjecture_5_8

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms ``KoszulRollerCoaster.conjecture_5_8
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom in Conjecture 5.8: {ax}"
