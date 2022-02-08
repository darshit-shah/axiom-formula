const AxiomFormula = require("./axiom-formula.js");
const axiomformula = AxiomFormula.evaluateAxiomFormula({ formula: "if(b=0,0,a/b)", getSplitValues: true });
const result = AxiomFormula.evaluateAxiomFormula({
    formulaTree: axiomformula.formulaTree,
    variableKeys: axiomformula.formulaVariables,
    variableValues: [10,0],
  });
console.log(result);