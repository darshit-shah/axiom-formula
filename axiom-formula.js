(function (exports) {
    evaluateAxiomFormula = function (options) {
       if( typeof utils === 'undefined') {
            utils = require("axiom-utils");
        }
        this.exec = function () {
            if (options.getSplitValues) {
                var formula = options.formula;
                if (isFormula(options.formula)) {
                    formula = options.formula.substr(1);
                }
                var depth = 1;
                var result = getSplitValues([formula], depth);
                var formulaReferenceKeys = [];
                var formulaReferenceValues = [];
                var formulaVariables = [];
                for (var resIndex = 0; resIndex < result.length; resIndex++) {
                    if (result[resIndex].type == 'ref') {
                        var colStart = -1;
                        var colEnd = -1;
                        var rowStart = -1;
                        var rowEnd = -1;
                        if (result[resIndex].part.indexOf(":") > 0) {
                            var values = getRowColIndex(result[resIndex].part.split(":")[0]);
                            colStart = values[0];
                            rowStart = values[1];
                            values = getRowColIndex(result[resIndex].part.split(":")[1]);
                            colEnd = values[0];
                            rowEnd = values[1];
                        }
                        else {
                            var values = getRowColIndex(result[resIndex].part);
                            colStart = values[0];
                            colEnd = values[0];
                            rowStart = values[1];
                            rowEnd = values[1];
                        }

                        if (colStart > colEnd) {
                            tmp = colStart;
                            colStart = colEnd;
                            colEnd = tmp;
                        }
                        if (rowStart > rowEnd) {
                            tmp = rowStart;
                            rowStart = rowEnd;
                            rowEnd = tmp;
                        }
                        var localIndex = utils.getIndexOf(formulaReferenceKeys, result[resIndex].part, false);
                        if (localIndex == -1) {
                            localIndex = utils.getIndexOf(formulaReferenceKeys, result[resIndex].part, true);
                            formulaReferenceValues.splice(localIndex, 0, [colStart, rowStart, colEnd, rowEnd]);
                        }
                    }
                    else if (result[resIndex].type == 'const') {
                        utils.getIndexOf(formulaVariables, result[resIndex].part, true);
                        //formulaVariables.push(result[resIndex]['part']);
                    }
                }
                options.globalIndex = 0;
                var formulaTree = createFormulaTree({ children: [{}] }, result[options.globalIndex].depth, result);
                return { result: result, formulaReferenceKeys: formulaReferenceKeys, formulaReferenceValues: formulaReferenceValues, formulaVariables: formulaVariables, formulaTree: formulaTree };

            }
            else if (options.formulaTree !== undefined) {
                var json = processFormulaTree(options.formulaTree).children[0].result;
                //console.log(json);
                //return eval(json);
                return json;
            }
            else {
                return "#NA";
            }
        }
        /**********************************************************
        <Summary>
        <Name>processFormulaTree</Name>
        <Description>Process formula using tree</Description>
        <ReturnType>Nothing</ReturnType> 
        </Summary>     
        ***********************************************************/
        var processFormulaTree = function (tree) {
            for (var childIndex = 0; childIndex < tree.children.length; childIndex++) {
                if (tree.children[childIndex].hasOwnProperty('tree')) {
                    delete tree.children[childIndex].result;
                    var result = processFormulaTree(tree.children[childIndex].tree);
                    if (tree.children[childIndex].type == "Operation Start") {
                        var arrFormulas = [];
                        if (result.children[0].result !== undefined)
                            arrFormulas.push(typeof(result.children[0].result) === 'number' ? result.children[0].result : result.children[0].result.toString());
                        else if (result.children[0].type == 'const')
                            arrFormulas.push(options.variableValues[result.children[0].part]);
                        else if (result.children[0].type == 'ref') {
                            if (options.rangeValues[result.children[0].part] == undefined) console.log("options.rangeValues[result.children[0].part is undefined in AxiomFormula.js");
                            if (options.rangeValues[result.children[0].part][0][0] !== "")
                                arrFormulas.push(options.rangeValues[result.children[0].part][0][0]);
                            else
                                arrFormulas.push("0");
                        }
                        for (var evalIndex = 1; evalIndex < result.children.length; evalIndex += 2) {
                            arrFormulas.push(result.children[evalIndex].part);
                            if (result.children[evalIndex + 1].result != undefined && result.children[evalIndex + 1].result != null)
                                arrFormulas.push(typeof(result.children[evalIndex + 1].result)==='number'?result.children[evalIndex + 1].result:result.children[evalIndex + 1].result.toString());
                            else if (result.children[evalIndex + 1].type == 'const')
                                arrFormulas.push(options.variableValues[result.children[evalIndex + 1].part]);
                            else if (result.children[evalIndex + 1].type == 'ref') {
                                if (options.rangeValues[result.children[evalIndex + 1].part][0][0] !== "")
                                    arrFormulas.push(options.rangeValues[result.children[evalIndex + 1].part][0][0]);
                                else
                                    arrFormulas.push("0");
                            }
                        }
                        tree.children[childIndex].result = processFurther(arrFormulas);
                    }
                    else if (tree.children[childIndex].type == "Func Start") {
                        if (tree.children[childIndex].part == '') {
                            tree.children[childIndex].result = result.children[0].result;
                        }
                        else {
                            tree.children[childIndex].result = FormulasMethods[tree.children[childIndex].part.toUpperCase()](result.children, options);
                        }
                    }
                }
                else {
                    if (tree.children[childIndex].type == 'ref') {
                        tree.children[childIndex].part = options.rangeKeys.indexOf(tree.children[childIndex].part);
                    }
                    else if (tree.children[childIndex].type == 'const') {
                        tree.children[childIndex].part = options.variableKeys.indexOf(tree.children[childIndex].part);
                    }
                    else if (tree.children[childIndex].type == 'number') {
                        tree.children[childIndex].result = +tree.children[childIndex].part;
                    }
                    else if (tree.children[childIndex].type == 'string') {
                        if ((tree.children[childIndex].part.charAt(0) === "\"" && tree.children[childIndex].part.charAt(tree.children[childIndex].part.length - 1) === "\"") || (tree.children[childIndex].part.charAt(0) === "'" && tree.children[childIndex].part.charAt(tree.children[childIndex].part.length - 1) === "'")) {
                            tree.children[childIndex].result = tree.children[childIndex].part.substr(1, tree.children[childIndex].part.length - 2);
                        }
                    }
                    if (tree.children[childIndex].depth == 1) {
                        if (tree.children[childIndex].type == 'const')
                            tree.children[childIndex].result = options.variableValues[tree.children[childIndex].part];
                        else if (tree.children[childIndex].type == 'ref') {
                            tree.children[childIndex].result = options.rangeValues[tree.children[childIndex].part][0][0];
                        }
                    }
                }
            }
            return tree;
        }

        var FormulasMethods = {
            SUM: function (data) {
                var sum = 0;
                for (var i = 0; i < data.length && !isNaN(sum); i++) {
                    if (data[i].result !== undefined) {
                        if (data[i].result.toString() !== "")
                            sum += +data[i].result;
                    }
                    else if (data[i].type == 'const') {
                        if (options.variableValues[data[i].part] !== "")
                            sum += +options.variableValues[data[i].part];
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                if (options.rangeValues[data[i].part][r][c] !== "")
                                    sum += +options.rangeValues[data[i].part][r][c];
                            }
                        }
                    }
                }
                return sum;
            },
            MIN: function (data) {
                var min = Infinity;
                for (var i = 0; i < data.length && !isNaN(min); i++) {
                    if (data[i].result !== undefined) {
                        if (data[i].result.toString() !== "" && min > +data[i].result)
                            min = +data[i].result;
                    }
                    else if (data[i].type == 'const') {
                        if (options.variableValues[data[i].part] !== "" && min > +options.variableValues[data[i].part])
                            min = +options.variableValues[data[i].part];
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                if (options.rangeValues[data[i].part][r][c] !== "" && min > +options.rangeValues[data[i].part][r][c])
                                    min = +options.rangeValues[data[i].part][r][c];
                            }
                        }
                    }
                }
                return min;
            },
            MAX: function (data) {
                var max = -Infinity;
                for (var i = 0; i < data.length && !isNaN(max); i++) {
                    if (data[i].result !== undefined) {
                        if (data[i].result.toString() !== "" && max < +data[i].result)
                            max = +data[i].result;
                    }
                    else if (data[i].type == 'const') {
                        if (options.variableValues[data[i].part] !== "" && max < +options.variableValues[data[i].part])
                            max = +options.variableValues[data[i].part];
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                if (options.rangeValues[data[i].part][r][c] !== "" && max < +options.rangeValues[data[i].part][r][c])
                                    max = +options.rangeValues[data[i].part][r][c];
                            }
                        }
                    }
                }
                return max;
            },
            AVERAGE: function (data) {
                var sum = 0;
                var count = 0;
                for (var i = 0; i < data.length && !isNaN(sum); i++) {
                    if (data[i].result !== undefined) {
                        if (data[i].result.toString() !== "") {
                            sum += +data[i].result;
                            count++;
                        }
                    }
                    else if (data[i].type == 'const') {
                        if (options.variableValues[data[i].part] !== "") {
                            sum += +options.variableValues[data[i].part];
                            count++;
                        }
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                if (options.rangeValues[data[i].part][r][c] !== "") {
                                    sum += +options.rangeValues[data[i].part][r][c];
                                    count++;
                                }
                            }
                        }
                    }
                }
                return sum / count;
            },
            IF: function (data) {
                if (data.length !== 3)
                    return "#NA";
                else {
                    var CONDITION;
                    var TRUE;
                    var FALSE;
                    if (data[0].result !== undefined) {
                        if (data[0].result == "true" || data[0].result == true || +data[0].result == 1)
                            CONDITION = true;
                        else
                            CONDITION = false;
                    }
                    else if (data[0].type == 'const') {
                        CONDITION = +options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        CONDITION = +options.rangeValues[data[0].part][0][0];
                    }

                    if (data[1].result !== undefined) {
                        TRUE = data[1].result;
                    }
                    else if (data[1].type == 'const') {
                        TRUE = options.variableValues[data[1].part];
                    }
                    else if (data[1].type == 'ref') {
                        TRUE = options.rangeValues[data[1].part][0][0];
                    }

                    if (data[2].result !== undefined) {
                        FALSE = data[2].result;
                    }
                    else if (data[2].type == 'const') {
                        FALSE = options.variableValues[data[2].part];
                    }
                    else if (data[2].type == 'ref') {
                        FALSE = options.rangeValues[data[2].part][0][0];
                    }
                    return CONDITION ? TRUE : FALSE;
                }
            },
            ROUND: function (data) {
                return this.ROUND_CEILING_FLOOR(data, 0);
            },
            CEILING: function (data) {
                return this.ROUND_CEILING_FLOOR(data, 1);
            },
            FLOOR: function (data) {
                return this.ROUND_CEILING_FLOOR(data, 2);
            },
            ROUND_CEILING_FLOOR: function (data, index) {
                if (data.length !== 2)
                    return "#NA";
                else {
                    var VALUE = "",
                        DIGITS = 1;
                    if (data[0].result !== undefined) {
                        VALUE = +data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        VALUE = +options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        VALUE = +options.rangeValues[data[0].part][0][0];
                    }

                    if (data[1].result !== undefined) {
                        DIGITS = +data[1].result;
                    }
                    else if (data[1].type == 'const') {
                        DIGITS = +options.variableValues[data[1].part];
                    }
                    else if (data[1].type == 'ref') {
                        DIGITS = +options.rangeValues[data[1].part][0][0];
                    }

                    var DIGITS = Math.pow(10, DIGITS);
                    if (index == 0)
                        return Math.round(VALUE * DIGITS) * 1.0 / DIGITS;
                    else if (index == 1)
                        return Math.ceil(VALUE * DIGITS) * 1.0 / DIGITS;
                    else
                        return Math.floor(VALUE * DIGITS) * 1.0 / DIGITS;
                }
            },
            ABS: function (data) {
                if (data.length !== 1)
                    return "#NA";
                else {
                    if (data[0].result !== undefined) {
                        return Math.abs(+data[0].result);
                    }
                    else if (data[0].type == 'const') {
                        return Math.abs(+options.variableValues[data[0].part]);
                    }
                    else if (data[0].type == 'ref') {
                        return Math.abs(+options.rangeValues[data[0].part][0][0]);
                    }
                }
            },
            AND: function (data) {
                for (var i = 0; i < data.length; i++) {
                    if (data[i].result !== undefined) {
                        if (data[i].result.toString() !== "")
                            if (data[i].result !== "true" && data[i].result !== true && +data[i].result !== 1)
                                return false;
                    }
                    else if (data[i].type == 'const') {
                        if (options.variableValues[data[i].part] !== "")
                            if (options.variableValues[data[i].part] !== "true" && options.variableValues[data[i].part] !== true && +options.variableValues[data[i].part] !== 1)
                                return false;
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                if (options.rangeValues[data[i].part][r][c] !== "")
                                    if (options.rangeValues[data[i].part][r][c] !== "true" && options.rangeValues[data[i].part][r][c] !== true && +options.rangeValues[data[i].part][r][c] !== 1)
                                        return false;
                            }
                        }
                    }
                }
                return true;
            },
            OR: function (data) {
                for (var i = 0; i < data.length; i++) {
                    if (data[i].result !== undefined) {
                        if (data[i].result.toString() !== "")
                            if (data[i].result == "true" || data[i].result == true || +data[i].result == 1)
                                return true;
                    }
                    else if (data[i].type == 'const') {
                        if (options.variableValues[data[i].part] !== "")
                            if (options.variableValues[data[i].part] == "true" || options.variableValues[data[i].part] == true || +options.variableValues[data[i].part] == 1)
                                return true;
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                if (options.rangeValues[data[i].part][r][c] !== "")
                                    if (options.rangeValues[data[i].part][r][c] == "true" || options.rangeValues[data[i].part][r][c] == true || +options.rangeValues[data[i].part][r][c] == 1)
                                        return true;
                            }
                        }
                    }
                }
                return false;
            },
            CONCATENATE: function (data) {
                var res = "";
                for (var i = 0; i < data.length; i++) {
                    if (data[i].result !== undefined) {
                        res += data[i].result;
                    }
                    else if (data[i].type == 'const') {
                        res += options.variableValues[data[i].part];
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                res += options.rangeValues[data[i].part][r][c];
                            }
                        }
                    }
                }
                return res;
            },
            COUNT: function (data) {
                var count = 0;
                for (var i = 0; i < data.length; i++) {
                    if (data[i].result !== undefined) {
                        if (data[i].result.toString() !== "") {
                            count++;
                        }
                    }
                    else if (data[i].type == 'const') {
                        if (options.variableValues[data[i].part] !== "") {
                            count++;
                        }
                    }
                    else if (data[i].type == 'ref') {
                        for (var r = 0; r < options.rangeValues[data[i].part].length; r++) {
                            for (var c = 0; c < options.rangeValues[data[i].part][r].length; c++) {
                                if (options.rangeValues[data[i].part][r][c] !== "") {
                                    count++;
                                }
                            }
                        }
                    }
                }
                return count;
            },
            LEFT: function (data) {
                if (data.length !== 2)
                    return "#NA";
                else {
                    var STRING = "",
                        LEN = 0;
                    if (data[0].result !== undefined) {
                        STRING = data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        STRING = options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        STRING = options.rangeValues[data[0].part][0][0];
                    }

                    if (data[1].result !== undefined) {
                        LEN = +data[1].result;
                    }
                    else if (data[1].type == 'const') {
                        LEN = +options.variableValues[data[1].part];
                    }
                    else if (data[1].type == 'ref') {
                        LEN = +options.rangeValues[data[1].part][0][0];
                    }
                    return STRING.substr(0, LEN);
                }
            },
            RIGHT: function (data) {
                if (data.length !== 2)
                    return "#NA";
                else {
                    var STRING = "",
                        LEN = 0;
                    if (data[0].result !== undefined) {
                        STRING = data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        STRING = options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        STRING = options.rangeValues[data[0].part][0][0];
                    }

                    if (data[1].result !== undefined) {
                        LEN = +data[1].result;
                    }
                    else if (data[1].type == 'const') {
                        LEN = +options.variableValues[data[1].part];
                    }
                    else if (data[1].type == 'ref') {
                        LEN = +options.rangeValues[data[1].part][0][0];
                    }
                    return STRING.substr(STRING.length - LEN, LEN);
                }
            },
            MID: function (data) {
                if (data.length !== 2)
                    return "#NA";
                else {
                    var STRING = "",
                        START = 0
                    LEN = 0;
                    if (data[0].result !== undefined) {
                        STRING = data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        STRING = options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        STRING = options.rangeValues[data[0].part][0][0];
                    }

                    if (data[1].result !== undefined) {
                        START = +data[1].result;
                    }
                    else if (data[1].type == 'const') {
                        START = +options.variableValues[data[1].part];
                    }
                    else if (data[1].type == 'ref') {
                        START = +options.rangeValues[data[1].part][0][0];
                    }

                    if (data[2].result !== undefined) {
                        LEN = +data[2].result;
                    }
                    else if (data[2].type == 'const') {
                        LEN = +options.variableValues[data[2].part];
                    }
                    else if (data[2].type == 'ref') {
                        LEN = +options.rangeValues[data[2].part][0][0];
                    }
                    return STRING.substr(START, LEN);
                }
            },
            LEN: function (data) {
                if (data.length !== 1)
                    return "#NA";
                else {
                    if (data[0].result !== undefined) {
                        return data[0].result.toString().length;
                    }
                    else if (data[0].type == 'const') {
                        return options.variableValues[data[0].part].toString().length;
                    }
                    else if (data[0].type == 'ref') {
                        return options.rangeValues[data[0].part][0][0].toString().length;
                    }
                    return 0;
                }
            },
            POWER: function (data) {
                if (data.length !== 2)
                    return "#NA";
                else {
                    var NUMBER = 0,
                        POWER = 0;
                    if (data[0].result !== undefined) {
                        NUMBER = +data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        NUMBER = +options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        NUMBER = +options.rangeValues[data[0].part][0][0];
                    }

                    if (data[1].result !== undefined) {
                        POWER = +data[1].result;
                    }
                    else if (data[1].type == 'const') {
                        POWER = +options.variableValues[data[1].part];
                    }
                    else if (data[1].type == 'ref') {
                        POWER = +options.rangeValues[data[1].part][0][0];
                    }
                    return Math.pow(NUMBER, POWER);
                }
            },
            SQRT: function (data) {
                if (data.length !== 1)
                    return "#NA";
                else {
                    var NUMBER = 0;
                    if (data[0].result !== undefined) {
                        NUMBER = +data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        NUMBER = +options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        NUMBER = +options.rangeValues[data[0].part][0][0];
                    }

                    return Math.sqrt(NUMBER);
                }
            },
            RAND: function (data) {
                if (data.length !== 0)
                    return "#NA";
                else {
                    return Math.random();
                }
            },
            RANDBETWEEN: function (data) {
                if (data.length !== 2)
                    return "#NA";
                else {
                    var LCAP = 0,
                        UCAP = 0;
                    if (data[0].result !== undefined) {
                        LCAP = +data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        LCAP = +options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        LCAP = +options.rangeValues[data[0].part][0][0];
                    }

                    if (data[1].result !== undefined) {
                        UCAP = +data[1].result;
                    }
                    else if (data[1].type == 'const') {
                        UCAP = +options.variableValues[data[1].part];
                    }
                    else if (data[1].type == 'ref') {
                        UCAP = +options.rangeValues[data[1].part][0][0];
                    }
                    return LCAP + Math.random() * (UCAP - LCAP);
                }
            },
            SUMPRODUCT: function (data) {
                var arrLen = data.length;
                var rLen = options.rangeValues[data[0].part].length;
                var cLen = options.rangeValues[data[0].part][0].length;
                var sumProduct = 0;
                for (var r = 0; r < rLen; r++) {
                    for (var c = 0; c < cLen; c++) {
                        var product = 1;
                        for (var i = 0; i < arrLen; i++) {
                            if (options.rangeValues[data[i].part][r][c] !== "") {
                                product *= +options.rangeValues[data[i].part][r][c];
                            }
                        }
                        sumProduct += product;
                    }
                }
                return sumProduct;
            },
            VLOOKUP: function (data) {
                if (data.length !== 3 && data.length !== 4)
                    return "#NA";

                var KEY = "";
                if (data[0].result !== undefined) {
                    KEY = data[0].result;
                }
                else if (data[0].type == 'const') {
                    KEY = options.variableValues[data[0].part];
                }
                else if (data[0].type == 'ref') {
                    KEY = options.rangeValues[data[0].part][0][0];
                }

                var INDEX = 0;
                if (data[2].result !== undefined) {
                    INDEX = +data[2].result;
                }
                else if (data[2].type == 'const') {
                    INDEX = +options.variableValues[data[2].part];
                }
                else if (data[2].type == 'ref') {
                    INDEX = +options.rangeValues[data[2].part][0][0];
                }

                if (data[1].result !== undefined) {
                    return "#NA"
                }
                else if (data[1].type == 'const') {
                    if (data[1].part > -1) {
                        for (var i = 0; i < options.variableValues[data[1].part][0].length; i++) {
                            if (options.variableValues[data[1].part][0][i].replace(/\"/ig, "").replace(/,/ig, "").toLowerCase() === KEY.toLowerCase()) {
                                return options.variableValues[data[1].part][INDEX - 1][i];
                            }
                        }
                    }
                    return "#NA"
                }
                else if (data[1].type == 'ref') {
                    if (data[1].part > -1) {
                        for (var i = 0; i < options.rangeValues[data[1].part][0].length; i++) {
                            if (options.rangeValues[data[1].part][0][i].replace(/\"/ig, "").replace(/,/ig, "").toLowerCase() === KEY.toLowerCase()) {
                                return options.rangeValues[data[1].part][INDEX - 1][i];
                            }
                        }
                    }
                    return "#NA"
                }
            },
            CALLEXTERNALAPI: function(data) {
                if (data.length !== 1)
                    return "#NA";
                else {
                    var URL="";
                    if (data[0].result !== undefined) {
                        URL = data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        URL = options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        URL = options.rangeValues[data[0].part][0][0];
                    }
                    externalAPIFunction(URL);
                    return "Fetching...";
                }
            },
            PARSEJSON: function(data) {
                if (data.length !== 2)
                    return "#NA";
                else {
                    var json="";
                    if (data[0].result !== undefined) {
                        json = data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        json = options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        json = options.rangeValues[data[0].part][0][0];
                    }

                    try{
                        json = JSON.parse(json);
                        var path="";
                        if (data[1].result !== undefined) {
                            path = data[1].result;
                        }
                        else if (data[1].type == 'const') {
                            path = options.variableValues[data[1].part];
                        }
                        else if (data[1].type == 'ref') {
                            path = options.rangeValues[data[1].part][0][0];
                        }
                        var value = eval("json"+path);
                        if(typeof value === 'object'){
                            return JSON.stringify(value,null,2);
                        }else if(value == null){
                            return "";
                        } else {
                            return value;
                        }
                    } catch(ex) {
                        return "#N/A"
                    }
                }
            },
            SAMPLE: function (data) {
                if (data.length !== 3)
                    return "#NA";
                else {
                    var CONDITION="";
                    if (data[0].result !== undefined) {
                        CONDITION = +data[0].result;
                    }
                    else if (data[0].type == 'const') {
                        CONDITION = +options.variableValues[data[0].part];
                    }
                    else if (data[0].type == 'ref') {
                        CONDITION = +options.rangeValues[data[0].part][0][0];
                    }
                    return CONDITION;
                }
            }
        }

        if(options.extraFunctions){
            Object.keys(options.extraFunctions).forEach(f=>{
                FormulasMethods[f.toUpperCase()]=options.extraFunctions[f];
            });
        }

        var externalAPIFunction = function(url){
            $.get(url, function(data, status){
                if(typeof data === 'object'){
                    data = JSON.stringify(data, null, 2);
                }
                if(options.outputRefCallback!=null && typeof options.outputRefCallback === 'function')
                    options.outputRefCallback(data);
            })
        }
        /**********************************************************
        <Summary>
        <Name>createFormulaTree</Name>
        <Description>create tree by parsing formula</Description>
        <ReturnType>Nothing</ReturnType> 
        </Summary>     
        ***********************************************************/
        var createFormulaTree = function (tree, depth, result) {
            var childTree = { children: [], result: null };
            tree.children[tree.children.length - 1].tree = childTree;
            while (options.globalIndex < result.length) {
                if (result[options.globalIndex].depth == depth) {
                    childTree.children.push(result[options.globalIndex]);
                    options.globalIndex++;
                }
                else if (result[options.globalIndex].depth > depth) {
                    createFormulaTree(childTree, result[options.globalIndex].depth, result);
                    options.globalIndex++;
                }
                else {
                    options.globalIndex--;
                    return childTree;
                }
            }
            return childTree;
        }


        /**********************************************************
        <Summary>
        <Name>getSplitValues</Name>
        <Description>Split formula and return array.</Description>
        <ReturnType>Nothing</ReturnType> 
        </Summary>     
        ***********************************************************/
        var getSplitValues = function (formulas, depth) {
            var retValues = [];
            if (formulas.length === 1) {
                var formula = formulas[0].trim();
                var splitValues = splitFormula(formula);
                if (splitValues.length > 1) {
                    retValues.push({ part: "", isReference: false, depth: depth, type: 'Operation Start', result: undefined });
                    retValues = retValues.concat(getSplitValues(splitValues, depth + 1));
                    return retValues;
                }
                if (isFunction(formula) && isProperFunction(formula)) {
                    var index = formula.trim().indexOf("(");
                    var funtionName = formula.trim().substr(0, index);
                    var params = formula.trim().substr(index + 1, formula.trim().length - (index + 2));
                    retValues.push({ part: funtionName, isReference: false, depth: depth, type: 'Func Start', result: undefined });
                    var splitCommaValues = splitByComma(params);
                    for (var i = 0; i < splitCommaValues.length; i++) {
                        splitValues = [];
                        splitValues.push(splitCommaValues[i]);
                        retValues = retValues.concat(getSplitValues(splitValues, depth + 1));
                    }
                    return retValues;
                }
                else if (formula.toLowerCase().trim().indexOf("(") === 0) {
                    if (formula.charAt(formula.length - 1) === ")") {
                        var index = 0;
                        var funtionName = "";
                        var params = formula.trim().substr(index + 1, formula.trim().length - (index + 2));
                        retValues.push({ part: funtionName, isReference: false, depth: depth, type: 'Func Start', result: undefined });
                        var splitCommaValues = splitByComma(params);
                        for (var i = 0; i < splitCommaValues.length; i++) {
                            splitValues = [];
                            splitValues.push(splitCommaValues[i]);
                            retValues = retValues.concat(getSplitValues(splitValues, depth + 1));
                        }
                        return retValues;
                    }
                    else {
                        retValues = retValues.concat(getSplitValues(splitFormula(formula), depth + 1));
                        return retValues;
                    }
                }
                else if (isOperator(formula)) {
                    simplifiedFormula = formula;
                    retValues.push({ part: simplifiedFormula, isReference: false, depth: depth, type: 'operator', result: undefined });
                    return retValues;
                }
                else if (options.referenceValuesArray.length > 0) {
                    if (options.referenceValuesArray.indexOf(formula) !== -1) {
                        simplifiedFormula = formula;
                        retValues.push({ part: simplifiedFormula, isReference: true, depth: depth, type: 'ref', result: undefined });
                        return retValues;
                    }
                    else {
                        simplifiedFormula = formula;
                        retValues.push({ part: simplifiedFormula, isReference: false, depth: depth, type: 'const', result: undefined });
                        return retValues;
                    }
                }
                else if (isReference(formula)) {
                    simplifiedFormula = formula;
                    retValues.push({ part: simplifiedFormula, isReference: true, depth: depth, type: 'ref', result: undefined });
                    return retValues;
                }
                else {
                    if (isFinite(formula) || formula === true || formula === false || formula === "false" || formula === "true") {
                        simplifiedFormula = formula;
                        retValues.push({ part: simplifiedFormula, isReference: false, depth: depth, type: 'number', result: +simplifiedFormula });
                    }
                    else if ((formula.charAt(0) === "\"" && formula.charAt(formula.length - 1) === "\"") || (formula.charAt(0) === "'" && formula.charAt(formula.length - 1) === "'")) {
                        splitValues = splitFormula(formula);
                        if (splitValues.length === 1)
                            retValues.push({ part: formula, isReference: false, depth: depth, type: 'string', result: undefined });
                        else {
                            retValues = retValues.concat(getSplitValues(splitValues, depth + 1));
                        }
                    }
                    else {
                        splitValues = splitFormula(formula);
                        if (splitValues.length === 1)
                            retValues.push({ part: formula, isReference: false, depth: depth, type: 'const', result: undefined });
                        else {
                            retValues = retValues.concat(getSplitValues(splitValues, depth + 1));
                        }
                    }
                    return retValues;
                }
            }
            else {
                for (var i = 0; i < formulas.length; i++) {
                    splitValues = splitFormula(formulas[i]);
                    retValues = retValues.concat(getSplitValues(splitValues, depth));
                }
                return retValues;
            }
        }
        /**********************************************************
        <Summary>
        <Name>parseFormula</Name>
        <Description>Parse formula.</Description>
        <ReturnType>Nothing</ReturnType> 
        </Summary>     
        ***********************************************************/
        var parseFormula = function (originalFormula) {
            var actualFormula = "";
            var formula = splitByComma(originalFormula);
            if (formula.length === 1) {
                if (validateFormula(formula[0])) {
                    var arrFormulas = splitFormula(formula[0]);
                    if (arrFormulas.length > 1) {
                        return processSplittedValues(formula[0], arrFormulas, 0);
                    }
                    else {
                        var output = parseInternalFormula(arrFormulas[0]);
                        actualFormula = output;
                        return actualFormula;
                    }
                }
                else {
                    actualFormula = "#NA";
                    return actualFormula;
                }
            }
            else {
                var allFormulas = [];
                allFormulas = allFormulas.concat(formula);
                return processAllFormulas(allFormulas, 0);
            }
        }

        function processAllFormulas(allFormulas, cnt) {
            if (cnt === allFormulas.length) {
                return allFormulas;
            }
            else {
                var output = parseFormula(allFormulas[cnt]);
                allFormulas[cnt] = output;
                return processAllFormulas(allFormulas, cnt + 1);
            }
        }

        function processSplittedValues(formula, arrFormulas, cnt) {
            if (cnt === arrFormulas.length) {
                return processFurther(arrFormulas);
            }
            else {
                if (!isOperator(arrFormulas[cnt])) {
                    var output = parseFormula(arrFormulas[cnt]);
                    arrFormulas[cnt] = output;
                    cnt++;
                    return processSplittedValues(formula, arrFormulas, cnt);
                }
                else {
                    cnt++;
                    return processSplittedValues(formula, arrFormulas, cnt);
                }
            }
        }
        function processFurther(arrFormulas) {
            var arrSeq = ["^", "/", "*", "-", "+", "=", "<", ">", "<=", ">=", "!=", "<>","%"];
            for (var i = 0; i < arrSeq.length && arrFormulas.length > 1; i++) {
                var index = arrFormulas.indexOf(arrSeq[i], 1);
                while (index !== -1 && index < (arrFormulas.length - 1)) {
                    arrFormulas.splice(index - 1, 3, executeOperation(arrSeq[i], arrFormulas[index - 1], arrFormulas[index + 1]));
                    index = arrFormulas.indexOf(arrSeq[i], index);
                }
            }
            if (arrFormulas.length === 1) {
                actualFormula = arrFormulas[0];
                return actualFormula;
            }
            else {
                actualFormula = "#NA";
                return actualFormula;
            }
        }


        var executeOperation = function (operator, val1, val2) {
            if (val1 === undefined || val2 === undefined) {
                return NaN;
            }
            if (operator === '/') {
                return +val1 / +val2;
            }
            else if (operator === '*') {
                return +val1 * +val2;
            }
            else if (operator === '+') {
                return +val1 + +val2;
            }
            else if (operator === '-') {
                return +val1 - +val2;
            }
            else if (operator === '^') {
                return Math.pow(+val1, +val2);
            }
            else if (operator === '=') {
                return val1 === val2;
            }
            else if (operator === '<>' || operator === '!=') {
                return val1 !== val2;
            }
            else if (operator === '<') {
                return +val1 < +val2;
            }
            else if (operator === '>') {
                return +val1 > +val2;
            }
            else if (operator === '<=') {
                return +val1 <= +val2;
            }
            else if (operator === '>=') {
                return +val1 >= +val2;
            }
            else if (operator === '%') {
                return +val1 % +val2;
            }
            else
                return NaN;
        }
        var splitFormula = function (formula) {
            var arrFormula = [];
            if (isOperator(formula)) {
                arrFormula.push(formula);
                return arrFormula;
            }
            var currFormula = '';
            var bracketCounter = 0;
            var quoteStart = false;
            var bracketStartCounter = 0;
            var quoteStartOptions = ["'", "\""], quoteEndOptions = ["'", "\""];
            var quoteIndex = -1;
            for (var cnt = 0; cnt < formula.length; cnt++) {
                if(quoteStart === false && quoteStartOptions.indexOf(formula.charAt(cnt))>-1){
                    quoteIndex = quoteStartOptions.indexOf(formula.charAt(cnt));
                    quoteStart=true;
                }
                else if(quoteStart === true && quoteEndOptions[quoteIndex] === formula.charAt(cnt)){
                    quoteIndex=-1;
                    quoteStart=false;
                }
                // if (formula.charAt(cnt) === "\"") {
                //     quoteStart = !quoteStart;
                // }
                else if (formula.charAt(cnt) === '(' && !quoteStart) {
                    bracketCounter++;
                    bracketStartCounter = cnt;
                }
                else if (formula.charAt(cnt) === ')' && !quoteStart) {
                    bracketCounter--;
                }
                if (bracketCounter === 0 && !quoteStart) {
                    if (bracketStartCounter !== cnt) {
                        if (isOperator(formula.substr(cnt, 2))) {
                            arrFormula.push(currFormula);
                            arrFormula.push(formula.substr(cnt, 2));
                            cnt++;
                            currFormula = "";
                        }
                        else if (isOperator(formula.charAt(cnt))) {
                            arrFormula.push(currFormula);
                            arrFormula.push(formula.charAt(cnt));
                            currFormula = "";
                        }
                        else {
                            currFormula += formula.charAt(cnt);
                        }
                    }
                    else {
                        currFormula += formula.charAt(cnt);
                    }
                }
                else {
                    currFormula += formula.charAt(cnt);
                }
            }
            arrFormula.push(currFormula);
            return arrFormula;
        }
        var splitByComma = function (formula) {
            if (Array.isArray(formula))
                formula = formula.join();
            var arrFormula = [];
            var bracketCounter = 0;
            var quoteStart = false;
            var currFormula = '';
            var quoteStartOptions = ["'", "\""], quoteEndOptions = ["'", "\""];
            var quoteIndex = -1;
            for (var cnt = 0; cnt < formula.length; cnt++) {
                if(quoteStart === false && quoteStartOptions.indexOf(formula.charAt(cnt))>-1){
                    quoteIndex = quoteStartOptions.indexOf(formula.charAt(cnt));
                    quoteStart=true;
                }
                else if(quoteStart === true && quoteEndOptions[quoteIndex] === formula.charAt(cnt)){
                    quoteIndex=-1;
                    quoteStart=false;
                }
                // if (formula.charAt(cnt) === "\"") {
                //     quoteStart = !quoteStart;
                // }
                else if (formula.charAt(cnt) === '(' && !quoteStart) {
                    bracketCounter++;
                }
                else if (formula.charAt(cnt) === ')' && !quoteStart) {
                    bracketCounter--;
                }
                if (bracketCounter === 0 && !quoteStart) {
                    if (formula.charAt(cnt) === ",") {
                        arrFormula.push(currFormula);
                        currFormula = "";
                    }
                    else {
                        currFormula += formula.charAt(cnt);
                    }
                }
                else {
                    currFormula += formula.charAt(cnt);
                }
            }
            arrFormula.push(currFormula);
            return arrFormula;
        }
        var isOperator = function (operator) {
            if (operator === '<=') {
                return true;
            }
            else if (operator === '>=') {
                return true;
            }
            else if (operator === '<>') {
                return true;
            }
            else if (operator === '!=') {
                return true;
            }
            else if (operator === '/') {
                return true;
            }
            else if (operator === '*') {
                return true;
            }
            else if (operator === '+') {
                return true;
            }
            else if (operator === '-') {
                return true;
            }
            else if (operator === '^') {
                return true;
            }
            else if (operator === '=') {
                return true;
            }
            else if (operator === '<') {
                return true;
            }
            else if (operator === '>') {
                return true;
            }
            else if (operator === '%') {
                return true;
            }
            return false;
        }
        var isFormula = function (value) {
            if (value.indexOf("=") === 0)
                return true;
            return false;
        }
        var isReference = function (value) {
            if ((value.charAt(0) === "\"" && value.charAt(value.length - 1) === "\"") || (value.charAt(0) === "'" && value.charAt(value.length - 1) === "'"))
                return false;
            if (value.indexOf(":") > 0) {
                var values = value.split(":");
                if (values.length !== 2)
                    return false;
                var valid1 = isValidAddress(values[0]);
                var valid2 = isValidAddress(values[1]);
                if (valid1 === valid2 && valid1 > 0)
                    return true;
                else
                    return false;
            }
            else {
                if (isValidAddress(value) === 1) {
                    return true;
                }
                else {
                    return false;
                }
            }
        }

        var getRowColIndex = function (value) {
            value = value.toLowerCase();
            var colName = 1;
            var rowNum = 1;
            var colIndex = 0;
            var rowIndex = 0;
            for (var cnt = 0; cnt < value.length; cnt++) {
                if (colName === 1) {
                    if (isColName(value[cnt])) {
                        var currIndex = (value.charCodeAt(cnt) - 96);
                        colIndex = colIndex * 26 + currIndex;
                    }
                    else {
                        colName = 0;
                    }
                }
                if (colName !== 1 && rowNum === 1) {
                    rowIndex = parseInt(value.substr(cnt, value.length - cnt));
                    cnt = value.length;
                }
            }
            return [colIndex, rowIndex];
        }

        var isValidAddress = function (value) {
            var hasCol = 0;
            var hasRow = 0;
            var colName = 1;
            var rowNum = 1;
            for (var cnt = 0; cnt < value.length; cnt++) {
                if (colName === 1) {
                    if (!isColName(value[cnt])) {
                        colName = 0;
                    }
                    else {
                        hasCol++;
                    }
                }
                if (colName !== 1 && rowNum === 1) {
                    if (!isRowNum(value[cnt])) {
                        rowNum = 0;
                    }
                    else {
                        hasRow++;
                    }
                }
            }
            if (rowNum === 1) {
                if (hasRow > 0 && hasCol > 0) {
                    return 1; // both
                }
                else if (hasRow > 0 && hasCol === 0) {
                    return 2; // only row
                }
                else if (hasRow === 0 && hasCol > 0) {
                    return 3; // only col
                }
                else {
                    return 0; // invalid
                }
            }
            else {
                return 0; // invalid
            }
        }

        var isColName = function (char) {
            if (char.toString().toLowerCase() >= "a" && char.toString().toLowerCase() <= "z")
                return true;
            else
                return false;
        }

        var isRowNum = function (char) {
            if (parseInt(char) >= 0 && parseInt(char) <= 9)
                return true;
            else
                return false;
        }
        var isFunction = function (value) {
            value = value.toLowerCase();
            return Object.keys(FormulasMethods).some(f=>{
                return value.indexOf(f.toLowerCase()+"(") === 0;
            })
            return false;
        }

        var isProperFunction = function (formula) {
            if (formula.toString().charAt(formula.length - 1) === ")") {
                return true;
            }
            else {
                return false;
            }
        }
        var validateFormula = function (formula) {
            var bracketCounter = 0;
            for (var cnt = 0; cnt < formula.length; cnt++) {
                if (formula.charAt(cnt) === '(')
                    bracketCounter++;
                else if (formula.charAt(cnt) === ')')
                    bracketCounter--;
                if (bracketCounter < 0)
                    return false;
            }
            if (bracketCounter === 0)
                return true;
            return false;
        }
    };
    exports.evaluateAxiomFormula = function (options) {
        var settings = {
            'formula': undefined,
            'referenceValuesArray': [],
            'useDefaultArray': false,
            getSplitValues: false,
            outputRefCallback: null,
            extraFunctions: {}
        };

        for (var key in options) {
            if (options.hasOwnProperty(key) && key != 'outputRefCallback' && key != 'extraFunctions') {
                settings[key] = options[key];
            }
        }
        settings = JSON.parse(JSON.stringify(settings));
        settings.outputRefCallback = options.outputRefCallback;
        settings.extraFunctions = options.extraFunctions;

        var objFormula = new evaluateAxiomFormula(settings);
        return objFormula.exec();
    };
})(typeof exports === 'undefined' ? this['AxiomFormula'] = {} : exports);