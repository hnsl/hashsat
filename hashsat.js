require('./boolicius.js');

var k_bv_cache = null;

var sha256_k_bv = function(t) {
    var raw_k = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b,
        0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01,
        0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7,
        0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152,
        0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
        0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
        0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08,
        0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f,
        0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    ];
    if (k_bv_cache === null)
        k_bv_cache = new Array(raw_k.length);
    if (k_bv_cache[t] === undefined)
        k_bv_cache[t] = define_bv(32, raw_k[t]);
    return k_bv_cache[t];
};

var sha256_ch = function(x, y, z) {
    return xor_bv(and_bv(x, y), and_bv(not_bv(x), z));
};

var sha256_maj = function(x, y, z) {
    return xor_bv(xor_bv(and_bv(x, y), and_bv(x, z)), and_bv(y, z));
};

var sha256_bsigma0 = function(w) {
    return xor_bv(xor_bv(rotr_bv(w, 2), rotr_bv(w, 13)), rotr_bv(w, 22));
};

var sha256_bsigma1 = function(w) {
    return xor_bv(xor_bv(rotr_bv(w, 6), rotr_bv(w, 11)), rotr_bv(w, 25));
};

var sha256_ssigma0 = function(w) {
    return xor_bv(xor_bv(rotr_bv(w, 7), rotr_bv(w, 18)), shr_bv(w, 3));
};

var sha256_ssigma1 = function(w) {
    return xor_bv(xor_bv(rotr_bv(w, 17), rotr_bv(w, 19)), shr_bv(w, 10));
};

var _debug_satisfy;

var sha256_process = function(in_state, message) {
    assert(message.length === 512);
    // Initialize all W values.
    var w = new Array(64);
    for (var t = 0; t < 16; t++) {
        w[t] = message.slice(t * 32, t * 32 + 32).reverse();
    }
    for (var t = 16; t < 64; t++) {
        w[t] = uaddm_bv(
            sha256_ssigma1(w[t - 2]),
            w[t - 7],
            sha256_ssigma0(w[t - 15]),
            w[t - 16]
        );
    }
    // Run all sha256 iterations.
    var a = in_state.a, b = in_state.b, c = in_state.c, d = in_state.d
    , e = in_state.e, f = in_state.f, g = in_state.g, h = in_state.h;
    for (var t = 0; t < 64; t++) {
        var temp1 = uaddm_bv(
            h,
            sha256_bsigma1(e),
            sha256_ch(e, f, g),
            sha256_k_bv(t),
            w[t]
        );
        var temp2 = uaddm_bv(
            sha256_bsigma0(a),
            sha256_maj(a, b, c)
        );
        h = g;
        g = f;
        f = e;
        e = uaddm_bv(d, temp1);
        d = c;
        c = b;
        b = a;
        a = uaddm_bv(temp1, temp2);
    }
    // Do final add and return the output state.
    var out_state = {
        a: uaddm_bv(in_state.a, a),
        b: uaddm_bv(in_state.b, b),
        c: uaddm_bv(in_state.c, c),
        d: uaddm_bv(in_state.d, d),
        e: uaddm_bv(in_state.e, e),
        f: uaddm_bv(in_state.f, f),
        g: uaddm_bv(in_state.g, g),
        h: uaddm_bv(in_state.h, h)
    };
    return out_state;
};

var sha256 = function(main_in) {
    assert((main_in.length % 8) === 0);
    var state = {
        a: define_bv(32, 0x6A09E667),
        b: define_bv(32, 0xBB67AE85),
        c: define_bv(32, 0x3C6EF372),
        d: define_bv(32, 0xA54FF53A),
        e: define_bv(32, 0x510E527F),
        f: define_bv(32, 0x9B05688C),
        g: define_bv(32, 0x1F83D9AB),
        h: define_bv(32, 0x5BE0CD19)
    };
    // Pad main_in according to the sha256 specification.
    // Suppose a message has length L < 2^64.  Before it is input to the
    // hash function, the message is padded on the right as follows:
    //  a.  "1" is appended.
    var p_main_in = main_in.slice(0);
    p_main_in.push(define_bit(true));
    //  b.  K "0"s are appended where K is the smallest, non-negative
    //      solution to the equation L + 1 + K = 448 (mod 512)
    while ((p_main_in.length % 512) !== 448)
        p_main_in.push(define_bit(false));
    //  c.  Then append the 64-bit block that is L in binary representation.
    //      After appending this block, the length of the message will be a
    //      multiple of 512 bits.
    p_main_in = p_main_in.concat(define_bv(32, 0), define_bv(32, main_in.length).reverse());
    assert((p_main_in.length % 512) === 0);
    // Iterate over all blocks and produce a new state.
    for (var i = 0; i < p_main_in.length; i += 512)
        state = sha256_process(state, p_main_in.slice(i, i + 512));
    // The final message digest is the big endian encoded
    // 32b integers in the state concatenated together.
    return [].concat(
        state.a.reverse(),
        state.b.reverse(),
        state.c.reverse(),
        state.d.reverse(),
        state.e.reverse(),
        state.f.reverse(),
        state.g.reverse(),
        state.h.reverse()
    );
};

var nonce = define_input_bv(32);

// Compile main in bit vector. Numbers are little endian encoded.
var main_in = [].concat(define_bv_hex(
    "01000000" + // Version
    "81cd02ab7e569e8bcd9317e2fe99f2de44d49ab2b8851ba4a308000000000000" + // hashPrevBlock
    "e320b6c2fffc8d750423db8b1eb942ae710e951ed797f7affc8892b0f1fc122b" + // hashMerkleRoot
    "c7f5d74d" + // Time
    "f2b9441a" // Target/difficulcy
)).concat(
    nonce // Nonce
);

// Create a double sha256 problem.
var main_out = sha256(sha256(main_in));

//constrain_bv_hex(nonce, "42a14695", "ffffffff");
constrain_bv_hex(main_out, "000000000000000", "fffffffffffffff");

// Solve it.
satisfy({nonce: nonce, main_out: main_out});


/*
// Test a shitty hash function.
var input = define_input_bv(32);
var c = define_bv(32, 0x6A09E667);

/// out_bv = 0x6A09E667 + ((i + 0x6A09E667) <<< 7)
var out_bv = uadd_bv(c, rotr_bv(uadd_bv(input, c)[0], 7))[0];

// Constrain the output to 0x12345678.
constrain_bv(out_bv, 0x12345678, 0xffffffff);

// Get satisfaction.
satisfy({input: input});*/

// Init SHA-256 state.
//var state;

/*
    fstr_t data = "01000000" "81cd02ab7e569e8bcd9317e2fe99f2de44d49ab2b8851ba4a308000000000000" "e320b6c2fffc8d750423db8b1eb942ae710e951ed797f7affc8892b0f1fc122b" \
    "c7f5d74d" "f2b9441a" "42a14695";
    fstr_t datab = fss(fstr_hexdecode(data));

    uint8_t out[32];
    fstr_t out_fs = FSTR_PACK(out);

    sha2_context ctx;
    sha2_starts(&ctx, 0);
    sha2_update(&ctx, (void*) datab.str, datab.len);
    sha2_finish(&ctx, out);

    sha2_starts(&ctx, 0);
    sha2_update(&ctx, (void*) out_fs.str, out_fs.len);
    sha2_finish(&ctx, out);

    DBG(fss(fstr_hexencode(out_fs)));
    lwt_exit(0);
 */