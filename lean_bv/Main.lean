import Dirac60.Certificate
import Dirac60.UniversalDecoupling

def main : IO Unit := do
  IO.println "Dirac60 Lean certificate elaborated successfully."
  IO.println s!"edges: {Dirac60.edges.length}"
  IO.println s!"all concrete vertex witnesses valid: {Dirac60.allVertexWitnessesOK}"
  IO.println s!"displayed three-colour defect: {Dirac60.defectCount}"
