var uid_seq =  0;
var conjunctions = [];

var Bit = function() {
    // Assign unique id to this bit state.
    this.id = "x" + uid_seq;
    uid_seq += 1;
    // A new bit is undefined.
    this.defined = false;
};

Bit.prototype.toString = function() {
    return this.id;
};

global.assert = function assert(v) {
    if (!v)
        throw new Error("assertion failed");
};

var build_formula = function(raw_formula, map) {
    for (var key in map) {
        var bit = map[key];
        assert(bit instanceof Bit && bit.defined);
        raw_formula = raw_formula.replace(new RegExp(key, 'g'), bit.toString());
    }
    return raw_formula;
};

/// Constrains an existing bit.
global.constrain_bit = function constrain_bit(bit, is_set) {
    assert(bit instanceof Bit && bit.defined);
    conjunctions.push("(" + (is_set? "": "!") + bit + ")");
};

/// Defines a new bit.
global.define_bit = function define_bit(is_set) {
    var bit = new Bit();
    conjunctions.push("(" + (is_set? "": "!") + bit + ")");
    //x-dbg/ bit.value = !!is_set;
    bit.defined = true;
    return bit;
};

/// Defines a new input bit.
global.define_input_bit = function define_input_bit() {
    var bit = new Bit();
    bit.defined = true;
    return bit;
};

/// Defines a new bit based on the specified raw formula and adds a conjunction for it.
var define_bit_formula = function(raw_formula, map) {
    var bit = new Bit();
    conjunctions.push("((" + build_formula(raw_formula, map) + ") <-> " + bit + ")");
    bit.defined = true;
    return bit;
};

/// Defines a new bit that should be the inverse result of another bit.
global.not = function not(x) {
    return define_bit_formula("!x", {x: x});
};

/// Defines a new bit that should be the anded result of two other bits.
global.and = function and(a, b) {
    return define_bit_formula("(a & b)", {a: a, b: b});
};

/// Defines a new bit that should be the ored result of two other bits.
global.or = function or(a, b) {
    return define_bit_formula("(a | b)", {a: a, b: b});
};

/// Defines a new bit that should be the xored result of two other bits.
global.xor = function xor(a, b) {
    return define_bit_formula("(a | b) & !(a & b)", {a: a, b: b});
};

/// Defines a new bit vector where each bit is a function of the bits with
/// the same index in two input vectors.
var fn_bv = function(a_bv, b_bv, bit_fn) {
    assert(a_bv.length === b_bv.length);
    var o_bv = new Array(a_bv.length);
    for (var i = 0; i < a_bv.length; i++)
        o_bv[i] = bit_fn(a_bv[i], b_bv[i]);
    return o_bv;
};

/// Defines a new bit vector that is the inverse result of another bit vector.
global.not_bv = function not_bv(x_bv) {
    var o_bv = new Array(x_bv.length);
    for (var i = 0; i < x_bv.length; i++)
        o_bv[i] = not(x_bv[i]);
    return o_bv;
};

/// Defines a new bit vector that is the anded result of two other bit vectors.
global.and_bv = function and_bv(a_bv, b_bv) {
    return fn_bv(a_bv, b_bv, and);
};

/// Defines a new bit vector that is the ored result of two other bit vectors.
global.or_bv = function or_bv(a_bv, b_bv) {
    return fn_bv(a_bv, b_bv, or);
};

/// Defines a new bit vector that is the xored result of two other bit vectors.
global.xor_bv = function xor_bv(a_bv, b_bv) {
    return fn_bv(a_bv, b_bv, xor);
};

/// Defines a new bit vector which is the result of the unsigned addition of
/// two input bitvectors of equal size. Index 0 is considered the least
/// significant bit and the significance is a linear function of the index.
/// If modulus is true the final carry bit is not generated and will be
/// returned as null. Returns an array containing [out_bitvector, final_carry].
global.uadd_bv = function uadd_bv(a_bv, b_bv, modulus) {
    assert(a_bv.length === b_bv.length);
    var o_bv = new Array(a_bv.length);
    var prev_carry;
    for (var i = 0; i < a_bv.length; i++) {
        var a = a_bv[i];
        var b = b_bv[i];
        var out, carry;
        if (i === 0) {
            // Half adder for least signficant bit.
            out = xor(a, b);
            carry = define_bit_formula("a & b", {a: a, b: b});
        } else {
            // Full adder for other bits.
            out = xor(xor(a, b), prev_carry);
            if (modulus && i === a_bv.length - 1) {
                // Throwing away the last carry bit for modulus addition.
                carry = null;
            } else {
                carry = define_bit_formula("(a & b) | (pc & a) | (pc & b)", {a: a, b: b, pc: prev_carry});
            }
        }
        o_bv[i] = out;
        prev_carry = carry;
    }
    return [o_bv, carry];
};

/// Shorthand for uadd_bv with modulus = true and adding an arbitrary number
/// of bit vectors together. Returns only the final out_bitvector.
global.uaddm_bv = function uaddm_bv(a_bv, b_bv) {
    var args = Array.prototype.slice.call(arguments, 0);
    assert(args.length >= 2);
    do {
        var a_bv = args.pop();
        var b_bv = args.pop();
        args.push(uadd_bv(a_bv, b_bv, true)[0]);
    } while (args.length > 1);
    return args.pop();
};

/// Defines a new bit vector that is the input vector right rotated the specified number of steps.
global.rotr_bv = function rotr_bv(bv, n) {
    assert(n > 0 && n < bv.length);
    var o_bv = new Array(bv.length);
    for (var i = 0; i < bv.length; i++)
        o_bv[i] = bv[(i + n) % bv.length];
    return o_bv;
};

/// Defines a new bit vector that is the input vector right shifted the specified number of steps.
global.shr_bv = function shr_bv(bv, n) {
    assert(n > 0 && n < bv.length);
    var o_bv = new Array(bv.length);
    for (var i = 0; i < bv.length - n; i++)
        o_bv[i] = bv[i + n];
    for (var i = bv.length - n; i < bv.length; i++)
        o_bv[i] = define_bit(false);
    return o_bv;
};

/// Defines an input bit vector with specified name and length.
global.define_input_bv = function define_input_bv(n) {
    assert(n > 0);
    var o_bv = new Array(n);
    for (var i = 0; i < n; i++)
        o_bv[i] = define_input_bit();
    return o_bv;
};

/// Defines a new bit vector as the specified value.
global.define_bv = function define_bv(n, val) {
    assert(n > 0 & n <= 32);
    var o_bv = new Array(n);
    for (var i = 0; i < n; i++) {
        o_bv[i] = define_bit((val & 1) !== 0);
        val = (val >> 1);
    }
    return o_bv;
};

/// Defines a new bit vector as the specified hexadecimal data value.
global.define_bv_hex = function define_bv_hex(hex_val) {
    assert(hex_val.length > 0);
    var o_bv = new Array(hex_val.length * 4);
    for (var i = 0; i < hex_val.length; i++) {
        var vbit4 = parseInt(hex_val.charAt(i), 16);
        for (var j = 0; j < 4; j++) {
            o_bv[i * 4 + 3 - j] = define_bit((vbit4 & 1) !== 0);
            vbit4 = (vbit4 >> 1);
        }
    }
    return o_bv;
};

/// Takes an already defined bit vector and adds additional constraints.
/// Only the bits that are set in the mask are constrained.
global.constrain_bv = function constrain_bv(bv, val, mask) {
    assert(bv.length > 0 & bv.length <= 32);
    for (var i = 0; i < bv.length; i++) {
        if ((mask & 1) !== 0)
            constrain_bit(bv[i], (val & 1) !== 0);
        val = (val >> 1);
        mask = (mask >> 1);
    }
};

/// Takes an already defined bit vector and adds additional constraints.
/// Only the bits that are set in the mask are constrained.
global.constrain_bv_hex = function constrain_bv_hex(bv, hex_val, hex_mask) {
    assert(hex_val.length === hex_mask.length);
    assert(bv.length >= hex_val.length * 4);
    for (var i = 0; i < bv.length; i++) {
        var vbit4 = parseInt(hex_val.charAt(i), 16);
        var mbit4 = parseInt(hex_mask.charAt(i), 16);
        for (var j = 0; j < 4; j++) {
            if ((mbit4 & 1) !== 0)
                constrain_bit(bv[i * 4 + 3 - j], (vbit4 & 1) !== 0);
            vbit4 = (vbit4 >> 1);
            mbit4 = (mbit4 >> 1);
        }
    }
};

var z2 = function(n) {
    n = n.toString();
    return (n.length < 2)? "0" + n: "" + n;
};

var get_time_str = function() {
    var now = new Date();
    var yyyy = now.getUTCFullYear() + "";
    var mm = z2(now.getUTCMonth() + 1);
    var dd = z2(now.getUTCDate());
    var hours = z2(now.getUTCHours());
    var minutes = z2(now.getUTCMinutes());
    var seconds = z2(now.getUTCSeconds());
    return yyyy + mm + dd + hours + minutes + seconds;
};

/// Attempts to satisfy all logical conjunctions defined in the problem.
/// Takes an object of "main bit vectors" that are of particular intrest
/// that will be presented in a human readable format. "main_bv" should
/// be an object of human readable keys mapped to bit vectors.
global.satisfy = function satisfy(main_bv) {
    // Define locations where problem stages are stored.
    var uid = get_time_str();
    var pdir = "problem-" + uid;
    var pin_path = pdir + "/problem.in";
    var pcnf_path = pdir + "/problem.cnf";
    var pout_path = pdir + "/problem.out";
    var psum_path = pdir + "/problem.sum";
    // Create main problem directory for this job.
    var fs = require('fs');
    fs.mkdirSync(pdir);
    // Write input problem file.
    console.log("writing problem [" + pin_path + "]");
    fs.writeFileSync(pin_path, conjunctions.join("  &  "));
    // Convert input problem to cnf.
    console.log("converting problem to cnf [" + pcnf_path + "]");
    var cp = require('child_process');
    var limboole = cp.spawn("limboole", ["-d", "-s", pin_path, "-o", pcnf_path], {stdio: ["ignore", "ignore", process.stderr]});
    limboole.on("exit", function(code, signal) {
        if (code !== 0)
            throw new Error("limboole exited with [" + code + "]");
        // Solve problem.
        console.log("solving problem [" + pout_path + "]");
        var minisat = cp.spawn("minisat", [pcnf_path, pout_path], {stdio: ["ignore", process.stdout, process.stderr]});
        minisat.on("exit", on_minisat_exit);
    });
    var on_minisat_exit = function(code, signal) {
        if (code === 20)
            throw new Error("minisat reported that problem was [UNSATISFIABLE]");
        if (code !== 10)
            throw new Error("minisat exited with [" + code + "]");
        // Parse and index cnf output.
        console.log("parsing & indexing cnf");
        var cnf_out = fs.readFileSync(pcnf_path, "utf-8");
        var cnf_map = {};
        cnf_out.split("\n").every(function(cnf_line) {
            var cnf_match = cnf_line.match(/^c (\d+) (\w+)$/);
            if (cnf_match === null)
                return (cnf_line.match(/^p cnf/) === null);
            var key = cnf_match[2];
            var value = Number(cnf_match[1]);
            cnf_map[key] = value;
            return true;
        });
        // Parse and index solution.
        console.log("parsing & indexing solution");
        var cnf_out = fs.readFileSync(pout_path, "utf-8");
        if (cnf_out.match(/^SAT\n/) === null)
            throw new Error("did not find [SAT] marker in solution");
        var raw_sol_v = cnf_out.substring(4).split(" ");
        var solution_v = Array(raw_sol_v.length + 1);
        for (var i = 0; i < raw_sol_v.length; i++)
            solution_v[i + 1] = (Number(raw_sol_v[i]) >= 0);
        // Print human readable summary.
        for (var key in main_bv) {
            var number_v = "", data_v = "", cur_nb = 0, cur_tb = 0, cur_n2v = 1, cur_t2v = 0x80;
            var flush_fn = function() {
                number_v = z2(cur_nb.toString(16)) + number_v;
                data_v = data_v + z2(cur_tb.toString(16));
                cur_nb = 0;
                cur_tb = 0;
                cur_n2v = 1;
                cur_t2v = 0x80;
            };
            main_bv[key].forEach(function(bit) {
                assert(bit instanceof Bit);
                var is_set = solution_v[cnf_map[bit.toString()]];
                if (is_set) {
                    cur_nb = (cur_nb | cur_n2v);
                    cur_tb = (cur_tb | cur_t2v);
                }
                cur_n2v = (cur_n2v << 1);
                cur_t2v = (cur_t2v >> 1);
                if (cur_n2v === 0x100)
                    flush_fn();
            });
            if (cur_n2v !== 1)
                flush_fn();
            var summary = key + "/n: 0x" + number_v + "\n"
            + key + "/d: [" + data_v + "]\n";
            process.stdout.write(summary);
            fs.appendFileSync(psum_path, summary);
        }
        process.exit(0);
    };
};
