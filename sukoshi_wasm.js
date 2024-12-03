"use strict";
// WebAssemblyのAppendixを元にした簡易的なWebAssemblyの実装で学習用です。
// Validationをできる限り正確に行うことの学習を目指しています。言い換えれば制御構造を正しく処理するための実装をするのが目的です。
// Testを通しているわけではなく、すべてのケースを網羅するわけではないので、実際の仕様とは異なる部分があるかもしれません。
//
// WebAssembly Value Types
const VAL_TYPE = {
    i32: "i32",
    i64: "i64",
    f32: "f32",
    f64: "f64",
    v128: "v128",
    funcref: "funcref",
    externref: "externref",
    unknown: "unknown",
};
// WebAssembly Opcodes
const OP_CODE = {
    i32_add: "i32.add",
    i32_rem_s: "i32.rem_s",
    i32_const: "i32.const",
    i32_eq: "i32.eq",
    i32_lt_s: "i32.lt_s",
    drop: "drop",
    block: "block",
    loop: "loop",
    if_: "if",
    else_: "else",
    end: "end",
    br: "br",
    br_if: "br_if",
    select: "select",
    local: "local",
    local_get: "local.get",
    local_set: "local.set",
    unreachable: "unreachable"
};
function debug_validate_log(text) {
    document.getElementById("validate_log").value += text + "\n";
}
function debug_log(text) {
    document.getElementById("log").value += text + "\n";
}
function clear_log(clear_validate_log = true) {
    if (clear_validate_log) {document.getElementById("validate_log").value = "";}
    document.getElementById("log").value = "";
    document.getElementById("stack").value = "";
}
function is_num(t) {
    return [VAL_TYPE.i32, VAL_TYPE.i64, VAL_TYPE.f32, VAL_TYPE.f64, VAL_TYPE.unknown].includes(t);
}
function is_vec(t) {
    return [VAL_TYPE.v128, VAL_TYPE.unknown].includes(t);
}
function is_ref(t) {
    return [VAL_TYPE.funcref, VAL_TYPE.externref, VAL_TYPE.unknown].includes(t);
}
function isNumber(value) {
    return typeof value === 'number';
}
function JSONparseWithComments(text) {
    return JSON.parse(text.replace(/\/\/.*$/gm, '').replace(/\/\*[\s\S]*?\*\//g, ''));
}
// Stack Implementation
class Stack {
    constructor() {
        this.items = [];
    }
    push(item) {
        this.items.push(item);
    }
    peek() {
        if (this.items.length === 0) throw new Error("Stack underflow");
        return this.items[this.items.length - 1];
    }
    pop() {
        if (this.items.length === 0) throw new Error("Stack underflow");
        return this.items.pop();
    }
    size() {
        return this.items.length;
    }
    get(index) {
        if (index < 0 || index >= this.items.length) throw new Error("Invalid stack index");
        return this.items[this.items.length - 1 - index];
    }
    resize(newSize) {
        this.items = this.items.slice(0, newSize);
    }
    clear() {
        this.items = [];
    }
}
function new_state() {
    return {program_counter: 0, locals: [], locals_types: []};
}
class ControlFrame {
    constructor(pc, opcode, startTypes, endTypes, height, cond = undefined) {
        this.program_counter = pc;
        this.opcode = opcode;
        this.start_types = startTypes;
        this.end_types = endTypes;
        this.height = height;
        this.unreachable = false;
        this.cond = cond;
    }
}
function push_ctrl(pc, opcode, inputTypes, outputTypes) {
    is_validation ? debug_validate_log(" push_ctrl: " + opcode) : debug_log(" push_ctrl: " + opcode);
    const frame = new ControlFrame(pc, opcode, inputTypes, outputTypes, vals.size());
    ctrls.push(frame);
    push_vals(inputTypes);
}
function pop_ctrl() {
    is_validation ? debug_validate_log(" pop_ctrl: ") : debug_log(" pop_ctrl: ");
    if (ctrls.size() === 0) {
        throw new Error("Control stack underflow");
    }
    const ctrl = ctrls.pop();
    if (ctrl.unreachable == false) {
        var popped = pop_vals(ctrl.end_types);
        if (vals.size() != ctrl.height) {
            throw new Error("Operand stack height mismatch: " + vals.size() + " " + ctrl.height + " " + ctrl.opcode);
        }
        push_vals(popped);
    }
    return ctrl;
}
function push_val(type, force = false) {
    if (ctrls.get(0).unreachable && !force) {
        return;
    }
    is_validation ? debug_validate_log(" push_val: " + type) : debug_log(" push_val: " + type);
    vals.push(type);
}
function pop_val(expect = null) {
    if (ctrls.get(0).unreachable) {
        return;
    }
    is_validation ? debug_validate_log(" pop_val: " + ((expect == null) ? "" : expect)) : debug_log(" pop_val: " + ((vals.size() == 0) ? "" : vals.get(0)));
    if (vals.size() == ctrls.get(0).height && ctrls.get(0).unreachable) {
        return VAL_TYPE.unknown;
    }
    if (vals.size() == ctrls.get(0).height) {
        throw new Error("Operand stack underflow: " + vals.size() + " " + ctrls.get(0).height);
    }
    const actual = vals.pop();
    if (expect && actual !== expect && actual !== VAL_TYPE.unknown && expect !== VAL_TYPE.unknown) {
        if (is_num(expect) && isNumber(actual)) {
            return actual;
        }
        throw new Error(`Type mismatch: expected [${expect}], got [${actual}]`);
    }
    return actual;
}
function push_vals(types, force = false) {
    for (const t of types) {
        push_val(t, force);
    }
}
function pop_vals(types) {
    const popped = [];
    for (let guard = types.length - 1; guard >= 0; guard--) {
        popped.unshift(pop_val(types[guard]));
    }
    return popped;
}
function label_types(ctrl) {
    return ctrl.opcode === OP_CODE.loop ? ctrl.start_types : ctrl.end_types;
}
function unreachable() {
    vals.resize(ctrls.get(0).height); // force drop values
    ctrls.get(0).unreachable = true;
    is_validation ? debug_validate_log(" <unreachable>") : debug_log(" <unreachable>");
}
function clear_state() {
    vals.clear();
    ctrls.clear();
}
function init_local(state, index, type) {
    switch (type) {
        case VAL_TYPE.i32:
        case VAL_TYPE.i64:
        case VAL_TYPE.f32:
        case VAL_TYPE.f64:
            state.locals[index] = 0;
            state.locals_types[index] = type;
            break;
        default:
            throw new Error("Unsupported local type: " + args[1]);
    }
}
// Validation Functions
function validate(state, opcode, parameters, results, args = []) {
    debug_validate_log("#" + opcode);
    switch (opcode) {
        case OP_CODE.i32_const:
            push_val(VAL_TYPE.i32);
            break;
        case OP_CODE.i32_add:
            pop_vals([VAL_TYPE.i32, VAL_TYPE.i32]);
            push_val(VAL_TYPE.i32);
            break;
        case OP_CODE.i32_rem_s:
            pop_vals([VAL_TYPE.i32, VAL_TYPE.i32]);
            push_val(VAL_TYPE.i32);
            break;
        case OP_CODE.i32_eq:
            pop_vals([VAL_TYPE.i32, VAL_TYPE.i32]);
            push_val(VAL_TYPE.i32);
            break;
        case OP_CODE.i32_lt_s:
            pop_vals([VAL_TYPE.i32, VAL_TYPE.i32]);
            push_val(VAL_TYPE.i32);
            break;
        case OP_CODE.drop:
            pop_val();
            break;
        case OP_CODE.select:
            pop_val(VAL_TYPE.i32);
            const t1 = pop_val();
            const t2 = pop_val();
            if (!((is_num(t1) && is_num(t2)) || (is_vec(t1) && is_vec(t2)))) {
                throw new Error("Type mismatch in select");
            }
            if (t1 !== t2 && t1 !== VAL_TYPE.unknown && t2 !== VAL_TYPE.unknown) {
                throw new Error("Type mismatch in select");
            }
            push_val(t1 === VAL_TYPE.unknown ? t2 : t1);
            break;
        case OP_CODE.local:
            init_local(state, args[0], args[1]);
            break;
        case OP_CODE.local_get:
            if (state.locals_types[args[0]] == undefined) {
                throw new Error(`Local ${args[0]} not initialized`);
            }
            push_val(state.locals_types[args[0]]);
            break;
        case OP_CODE.local_set:
            if (state.locals_types[args[0]] == undefined) {
                throw new Error(`Local ${args[0]} not initialized`);
            }
            pop_val(state.locals_types[args[0]]);
            break;    
        case OP_CODE.unreachable:
            unreachable();
            break;
        case OP_CODE.block:
            push_ctrl(0, opcode, parameters || [], results || []);
            break;
       case OP_CODE.loop:
            push_ctrl(0, opcode, parameters || [], results || []);
            break;
        case OP_CODE.if_:
            pop_val(VAL_TYPE.i32);
            push_ctrl(0, opcode, parameters || [], results || []);
            break;
        case OP_CODE.end:
            // loopのend時のstack validationがあやしい・・・・かも？だいたい動く！
            const block_control = pop_ctrl();
            // 詰み直すことで想定している型のvalidationとする
            if (block_control.unreachable == false) {
                pop_vals(block_control.end_types);
                push_vals(block_control.end_types);
            }
            break;
        case OP_CODE.else_:
            const elseFrame = pop_ctrl();
            if (elseFrame.opcode !== OP_CODE.if_) {
                throw new Error("else must follow an if");
            }
            // if ---- else ---- end両方を通って検証する必要がある。
            // validationではブロック素通りの帳尻合わせの為にifの節で通って詰んだ値をpopしておく
            pop_vals(elseFrame.end_types);
            push_ctrl(0, OP_CODE.else_, elseFrame.start_types, elseFrame.end_types);
            break;
        case OP_CODE.br:
            if (args.length != 1) {
                throw new Error("br requires one immediate");
            }
            if (ctrls.size() < args[0]) {
                throw new Error("Branch target out of range");
            }
            var result = pop_vals(label_types(ctrls.get(args[0])));
            execute_br(args[0], result, state);
            break;
        case OP_CODE.br_if:
            var cond = pop_val(VAL_TYPE.i32);
            if (args.length != 1) {
                throw new Error("br_if requires one immediate");
            }
            if (ctrls.size() < args[0]) {
                throw new Error("Branch target out of range");
            }
            if (cond == 1) {
                var result = pop_vals(label_types(ctrls.get(args[0])));
                execute_br(args[0], result, state);
            }
            break;
        default:
            throw new Error(`Unsupported opcode: ${opcode}`);
    }
}
function execute_br(label, result, state){    
    if (label < 0 || label >= ctrls.size()) {
        throw new Error("invalid label");
    }
    // labelの深さまでunreachableにする。stackの調整はendで行う方式。
    for (var guard = 0; guard < label; guard++)
    {
        ctrls.get(guard).unreachable = true;
    }
    var targetBlock = ctrls.get(0);
    if (targetBlock.opcode == OP_CODE.loop)
    {
        state.program_counter = targetBlock.program_counter;
    } else {
        ctrls.get(label).unreachable = true;
    }
    push_vals(result, true);
}
function execute(state, opcode, parameters, results, args = []) {
    if (ctrls.size() > 0 && ctrls.get(0).unreachable) {
        if (![OP_CODE.else_, OP_CODE.end].includes(opcode)) {
            state.program_counter++;
            return;
        }
    }
    debug_log("#" + opcode)
    switch (opcode) {
        case OP_CODE.i32_const:
            push_val(args[0]);
            break;
        case OP_CODE.i32_add:
            console.log(vals.size());
            var rhs = pop_val();
            var lhs = pop_val();
            push_val(rhs + lhs);
            break;
        case OP_CODE.i32_rem_s:
            var rhs = pop_val();
            var lhs = pop_val();
            push_val(lhs % rhs);
            break;
        case OP_CODE.i32_eq:
            var rhs = pop_val();
            var lhs = pop_val();
            push_val(rhs == lhs ? 1 : 0);
            break;
        case OP_CODE.i32_lt_s:
            var rhs = pop_val();
            var lhs = pop_val();
            push_val(lhs < rhs ? 1 : 0);
            break;
        case OP_CODE.drop:
            pop_val();
            break;
        case OP_CODE.select:
            var sel = pop_val();
            const t1 = pop_val();
            const t2 = pop_val();
            push_val((sel > 0) ? t2 : t1);
            break;
        case OP_CODE.local:
            init_local(state, args[0], args[1]);
            break;
        case OP_CODE.local_get:
            if (!(args[0] in state.locals)) {
                throw new Error(`Local ${args[0]} not initialized`);
            }
            push_val(state.locals[args[0]]);
            break;
        case OP_CODE.local_set:
            if (!(args[0] in state.locals)) {
                throw new Error(`Local ${args[0]} not initialized`);
            }
            state.locals[args[0]] = pop_val();
            break;
        case OP_CODE.unreachable:
            unreachable();
            break;
        case OP_CODE.block:
            push_ctrl(state.program_counter, opcode, parameters || [], results || []);
            break;
        case OP_CODE.loop:
            push_ctrl(state.program_counter, opcode, parameters || [], results || []);
            break;
        case OP_CODE.if_:
            var cond = pop_val();
            push_ctrl(state.program_counter, opcode, parameters || [], results || []);
            ctrls.get(0).cond = cond;
            if (cond <= 0) {
                unreachable();
            }
            break;
        case OP_CODE.end:
            pop_ctrl();
            break;
        case OP_CODE.else_:
            const ifFrame = ctrls.get(0);
            ifFrame.opcode = "else";
            var is_unreachable = ifFrame.unreachable;
            ifFrame.unreachable = (ifFrame.cond === 1) ? true : false;
            if (ifFrame.cond === 1 && is_unreachable) {
                ifFrame.unreachable = is_unreachable;
            }
            break;
        case OP_CODE.br:
            execute_br(args[0], pop_vals(label_types(ctrls.get(args[0]))), state);
            return; // skip pc increment
        case OP_CODE.br_if:
            var cond = pop_val();
            if (cond == 1) {
                execute_br(args[0], pop_vals(label_types(ctrls.get(args[0]))), state);
                return; // skip pc increment
            }
            break;
        default:
            throw new Error(`Unsupported opcode: ${opcode}`);
    }
    state.program_counter++;
}
function validate_instructions(instructions) {
    is_validation = true;
    // 関数の開始時には便宜的にfunctionというControlFrameを追加しておく
    push_ctrl(0, "function", [], get_signature());
    var state = new_state();
    for (var guard = 0; guard < instructions.length; guard++) {
        const [opcode, parameters, results, args] = instructions[guard];
        for (var j = 0; j < parameters.length; j++) {
            validate_type(parameters[j]);
        }
        for (var k = 0; k < results.length; k++) {
            validate_type(results[k]);
        }
        validate(state, opcode, parameters, results, args);
    }
    if (vals.size() != ctrls.get(0).end_types.length) {
        throw new Error("return value not matched: [" + vals.items.join(", ") + "] :[" + ctrls.get(0).end_types.join(", ") + "]");
    }
    for (var guard = 0; guard < vals.size(); guard++) {
        var lhs = vals.get(guard);
        var rhs = ctrls.get(0).end_types[guard];
        if (lhs != rhs) {
            throw new Error(`return type expected ${rhs}, got ${lhs}`);
        }
    }
}
function get_signature() {
    var result = JSONparseWithComments(document.getElementById("signature").value);
    for (var guard = 0; guard < result.length; guard++) {
        validate_type(result[guard]);
    }
    return result;
}
function validate_type(t) {
    if (!Object.values(VAL_TYPE).includes(t)) {
        throw new Error("Invalid type: " + t + " type expects:" + Object.values(VAL_TYPE).join(", "));
    }
}
function execute_instructions(instructions) {
    is_validation = false;
    push_ctrl(0, "function", [], get_signature());
    var state = new_state();
    for (var guard = 0; state.program_counter < instructions.length; guard++) {
        const [opcode, parameters, results, args] = instructions[state.program_counter];
        execute(state, opcode, parameters, results, args);
        if (guard > 10000) {
            throw new Error("maximum execution count reached."); // loopやると無限ループしやすい。説明用だしガードをいれる。
        }
    }
}
function run_validation(text) {
    clear_state();
    clear_texts();
    step_flag = false;
    try {
        // see also: run function.
        var instructions = JSONparseWithComments(text);
        validate_instructions(instructions);
        document.getElementById("validation").innerText = "Validation Result: Passes";
        document.getElementById("stack").value = JSON.stringify(vals.items);
    } catch (error) {
        document.getElementById("stack").value = JSON.stringify(vals.items);
        document.getElementById("validation").innerText = "Validation Error:" + error.toString();
        throw error
    }
}
function step_exec() {
    if (!step_flag) {
        clear_log();
        var text = document.getElementById('instructions').value;
        step_json = JSONparseWithComments(text);
        clear_state();
        step_flag = true;
        step_done = false;
        step_state = new_state();
        step_max = step_json.length;
        is_validation = false;
        push_ctrl(0, "function", [], JSONparseWithComments(document.getElementById("signature").value));
    }
    if (step_state.program_counter < step_max) {
        try {
            execute(step_state, step_json[step_state.program_counter][0], step_json[step_state.program_counter][1] || [], step_json[step_state.program_counter][2] || [], step_json[step_state.program_counter][3] || []);
            document.getElementById("stack").value = JSON.stringify(vals.items);
        } catch (error) {
            document.getElementById("result").innerText = "Execution Error: " + error.toString();
            throw error
        }
    } else {
        if (!step_done) {
            var resultText = "Execution Result: " + JSON.stringify(vals.items);
            document.getElementById("result").innerText = resultText;
            step_done = true;
        }
    }
}
function clear_texts() {
    clear_log();
    step_flag = false;
    step_done = false;
    clear_state();
    document.getElementById("validation").innerHTML = "&nbsp;";
    document.getElementById("result").innerHTML = "&nbsp;";
}
function run(text) {
    clear_log(false);
    clear_state();
    step_flag = false;
    try {
        // WebAssembly ModuleのParseは省略して、OpCodeと即値を直接指定して検証、実行します。
        // opcodeはjsonの都合上文字列（"i32.const" 等）で指定します。
        // Immediateは実際に命令のバイト列から読み出すと長くなるのでパラメーターとして追加しています。
        // 
        // [
        //   [opcode, [input parameters type], [result types], [immediates]]...
        // ]
        // 例: ["i32.const", [], [], [42]] は (i32.const 42) に相当します。
        var instructions = JSONparseWithComments(text);
        execute_instructions(instructions);
        var resultText = "Execution Result: " + JSON.stringify(vals.items);
        document.getElementById("result").innerText = resultText;
        document.getElementById("stack").value = JSON.stringify(vals.items);
    } catch (error) {
        document.getElementById("result").innerText = "Execution Error: " + error.toString();
        throw error
    }
}
// Global Stacks
const vals = new Stack();
const ctrls = new Stack();
// Global variables for step execution
var step_flag = false;
var step_state = new_state();
var step_max = 0;
var step_json = [];
var step_done = false;
var is_validation = false;