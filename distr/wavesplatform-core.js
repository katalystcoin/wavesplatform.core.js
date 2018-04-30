// Blake2B in pure Javascript
// Adapted from the reference implementation in RFC7693
// Ported to Javascript by DC - https://github.com/dcposch

/* util */
var ERROR_MSG_INPUT = 'Input must be an string, Buffer or Uint8Array'

// For convenience, let people hash a string, not just a Uint8Array
function normalizeInput (input) {
    var ret
    if (input instanceof Uint8Array) {
        ret = input
    } else if (input instanceof Buffer) {
        ret = new Uint8Array(input)
    } else if (typeof (input) === 'string') {
        ret = new Uint8Array(new Buffer(input, 'utf8'))
    } else {
        throw new Error(ERROR_MSG_INPUT)
    }
    return ret
}

// Converts a Uint8Array to a hexadecimal string
// For example, toHex([255, 0, 255]) returns "ff00ff"
function toHex (bytes) {
    return Array.prototype.map.call(bytes, function (n) {
        return (n < 16 ? '0' : '') + n.toString(16)
    }).join('')
}

// Converts any value in [0...2^32-1] to an 8-character hex string
function uint32ToHex (val) {
    return (0x100000000 + val).toString(16).substring(1)
}

// For debugging: prints out hash state in the same format as the RFC
// sample computation exactly, so that you can diff
function debugPrint (label, arr, size) {
    var msg = '\n' + label + ' = '
    for (var i = 0; i < arr.length; i += 2) {
        if (size === 32) {
            msg += uint32ToHex(arr[i]).toUpperCase()
            msg += ' '
            msg += uint32ToHex(arr[i + 1]).toUpperCase()
        } else if (size === 64) {
            msg += uint32ToHex(arr[i + 1]).toUpperCase()
            msg += uint32ToHex(arr[i]).toUpperCase()
        } else throw new Error('Invalid size ' + size)
        if (i % 6 === 4) {
            msg += '\n' + new Array(label.length + 4).join(' ')
        } else if (i < arr.length - 2) {
            msg += ' '
        }
    }
    console.log(msg)
}

// For performance testing: generates N bytes of input, hashes M times
// Measures and prints MB/second hash performance each time
function testSpeed (hashFn, N, M) {
    var startMs = new Date().getTime()

    var input = new Uint8Array(N)
    for (var i = 0; i < N; i++) {
        input[i] = i % 256
    }
    var genMs = new Date().getTime()
    console.log('Generated random input in ' + (genMs - startMs) + 'ms')
    startMs = genMs

    for (i = 0; i < M; i++) {
        var hashHex = hashFn(input)
        var hashMs = new Date().getTime()
        var ms = hashMs - startMs
        startMs = hashMs
        console.log('Hashed in ' + ms + 'ms: ' + hashHex.substring(0, 20) + '...')
        console.log(Math.round(N / (1 << 20) / (ms / 1000) * 100) / 100 + ' MB PER SECOND')
    }
}


/********/

// 64-bit unsigned addition
// Sets v[a,a+1] += v[b,b+1]
// v should be a Uint32Array
function ADD64AA (v, a, b) {
    var o0 = v[a] + v[b]
    var o1 = v[a + 1] + v[b + 1]
    if (o0 >= 0x100000000) {
        o1++
    }
    v[a] = o0
    v[a + 1] = o1
}

// 64-bit unsigned addition
// Sets v[a,a+1] += b
// b0 is the low 32 bits of b, b1 represents the high 32 bits
function ADD64AC (v, a, b0, b1) {
    var o0 = v[a] + b0
    if (b0 < 0) {
        o0 += 0x100000000
    }
    var o1 = v[a + 1] + b1
    if (o0 >= 0x100000000) {
        o1++
    }
    v[a] = o0
    v[a + 1] = o1
}

// Little-endian byte access
function B2B_GET32 (arr, i) {
    return (arr[i] ^
    (arr[i + 1] << 8) ^
    (arr[i + 2] << 16) ^
    (arr[i + 3] << 24))
}

// G Mixing function
// The ROTRs are inlined for speed
function B2B_G (a, b, c, d, ix, iy) {
    var x0 = m[ix]
    var x1 = m[ix + 1]
    var y0 = m[iy]
    var y1 = m[iy + 1]

    ADD64AA(v, a, b) // v[a,a+1] += v[b,b+1] ... in JS we must store a uint64 as two uint32s
    ADD64AC(v, a, x0, x1) // v[a, a+1] += x ... x0 is the low 32 bits of x, x1 is the high 32 bits

    // v[d,d+1] = (v[d,d+1] xor v[a,a+1]) rotated to the right by 32 bits
    var xor0 = v[d] ^ v[a]
    var xor1 = v[d + 1] ^ v[a + 1]
    v[d] = xor1
    v[d + 1] = xor0

    ADD64AA(v, c, d)

    // v[b,b+1] = (v[b,b+1] xor v[c,c+1]) rotated right by 24 bits
    xor0 = v[b] ^ v[c]
    xor1 = v[b + 1] ^ v[c + 1]
    v[b] = (xor0 >>> 24) ^ (xor1 << 8)
    v[b + 1] = (xor1 >>> 24) ^ (xor0 << 8)

    ADD64AA(v, a, b)
    ADD64AC(v, a, y0, y1)

    // v[d,d+1] = (v[d,d+1] xor v[a,a+1]) rotated right by 16 bits
    xor0 = v[d] ^ v[a]
    xor1 = v[d + 1] ^ v[a + 1]
    v[d] = (xor0 >>> 16) ^ (xor1 << 16)
    v[d + 1] = (xor1 >>> 16) ^ (xor0 << 16)

    ADD64AA(v, c, d)

    // v[b,b+1] = (v[b,b+1] xor v[c,c+1]) rotated right by 63 bits
    xor0 = v[b] ^ v[c]
    xor1 = v[b + 1] ^ v[c + 1]
    v[b] = (xor1 >>> 31) ^ (xor0 << 1)
    v[b + 1] = (xor0 >>> 31) ^ (xor1 << 1)
}

// Initialization Vector
var BLAKE2B_IV32 = new Uint32Array([
    0xF3BCC908, 0x6A09E667, 0x84CAA73B, 0xBB67AE85,
    0xFE94F82B, 0x3C6EF372, 0x5F1D36F1, 0xA54FF53A,
    0xADE682D1, 0x510E527F, 0x2B3E6C1F, 0x9B05688C,
    0xFB41BD6B, 0x1F83D9AB, 0x137E2179, 0x5BE0CD19
])

var SIGMA8 = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3,
    11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4,
    7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8,
    9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13,
    2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9,
    12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11,
    13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10,
    6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5,
    10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3
]

// These are offsets into a uint64 buffer.
// Multiply them all by 2 to make them offsets into a uint32 buffer,
// because this is Javascript and we don't have uint64s
var SIGMA82 = new Uint8Array(SIGMA8.map(function (x) { return x * 2 }))

// Compression function. 'last' flag indicates last block.
// Note we're representing 16 uint64s as 32 uint32s
var v = new Uint32Array(32)
var m = new Uint32Array(32)
function blake2b_compress (ctx, last) {
    var i = 0

    // init work variables
    for (i = 0; i < 16; i++) {
        v[i] = ctx.h[i]
        v[i + 16] = BLAKE2B_IV32[i]
    }

    // low 64 bits of offset
    v[24] = v[24] ^ ctx.t
    v[25] = v[25] ^ (ctx.t / 0x100000000)
    // high 64 bits not supported, offset may not be higher than 2**53-1

    // last block flag set ?
    if (last) {
        v[28] = ~v[28]
        v[29] = ~v[29]
    }

    // get little-endian words
    for (i = 0; i < 32; i++) {
        m[i] = B2B_GET32(ctx.b, 4 * i)
    }

    // twelve rounds of mixing
    // uncomment the DebugPrint calls to log the computation
    // and match the RFC sample documentation
    // util.debugPrint('          m[16]', m, 64)
    for (i = 0; i < 12; i++) {
        // util.debugPrint('   (i=' + (i < 10 ? ' ' : '') + i + ') v[16]', v, 64)
        B2B_G(0, 8, 16, 24, SIGMA82[i * 16 + 0], SIGMA82[i * 16 + 1])
        B2B_G(2, 10, 18, 26, SIGMA82[i * 16 + 2], SIGMA82[i * 16 + 3])
        B2B_G(4, 12, 20, 28, SIGMA82[i * 16 + 4], SIGMA82[i * 16 + 5])
        B2B_G(6, 14, 22, 30, SIGMA82[i * 16 + 6], SIGMA82[i * 16 + 7])
        B2B_G(0, 10, 20, 30, SIGMA82[i * 16 + 8], SIGMA82[i * 16 + 9])
        B2B_G(2, 12, 22, 24, SIGMA82[i * 16 + 10], SIGMA82[i * 16 + 11])
        B2B_G(4, 14, 16, 26, SIGMA82[i * 16 + 12], SIGMA82[i * 16 + 13])
        B2B_G(6, 8, 18, 28, SIGMA82[i * 16 + 14], SIGMA82[i * 16 + 15])
    }
    // util.debugPrint('   (i=12) v[16]', v, 64)

    for (i = 0; i < 16; i++) {
        ctx.h[i] = ctx.h[i] ^ v[i] ^ v[i + 16]
    }
    // util.debugPrint('h[8]', ctx.h, 64)
}

// Creates a BLAKE2b hashing context
// Requires an output length between 1 and 64 bytes
// Takes an optional Uint8Array key
function blake2b_init (outlen, key) {
    if (outlen === 0 || outlen > 64) {
        throw new Error('Illegal output length, expected 0 < length <= 64')
    }
    if (key && key.length > 64) {
        throw new Error('Illegal key, expected Uint8Array with 0 < length <= 64')
    }

    // state, 'param block'
    var ctx = {
        b: new Uint8Array(128),
        h: new Uint32Array(16),
        t: 0, // input count
        c: 0, // pointer within buffer
        outlen: outlen // output length in bytes
    }

    // initialize hash state
    for (var i = 0; i < 16; i++) {
        ctx.h[i] = BLAKE2B_IV32[i]
    }
    var keylen = key ? key.length : 0
    ctx.h[0] ^= 0x01010000 ^ (keylen << 8) ^ outlen

    // key the hash, if applicable
    if (key) {
        blake2b_update(ctx, key)
        // at the end
        ctx.c = 128
    }

    return ctx
}

// Updates a BLAKE2b streaming hash
// Requires hash context and Uint8Array (byte array)
function blake2b_update (ctx, input) {
    for (var i = 0; i < input.length; i++) {
        if (ctx.c === 128) { // buffer full ?
            ctx.t += ctx.c // add counters
            blake2b_compress(ctx, false) // compress (not last)
            ctx.c = 0 // counter to zero
        }
        ctx.b[ctx.c++] = input[i]
    }
}

// Completes a BLAKE2b streaming hash
// Returns a Uint8Array containing the message digest
function blake2b_final (ctx) {
    ctx.t += ctx.c // mark last block offset

    while (ctx.c < 128) { // fill up with zeros
        ctx.b[ctx.c++] = 0
    }
    blake2b_compress(ctx, true) // final block flag = 1

    // little endian convert and store
    var out = new Uint8Array(ctx.outlen)
    for (var i = 0; i < ctx.outlen; i++) {
        out[i] = ctx.h[i >> 2] >> (8 * (i & 3))
    }
    return out
}

// Computes the BLAKE2B hash of a string or byte array, and returns a Uint8Array
//
// Returns a n-byte Uint8Array
//
// Parameters:
// - input - the input bytes, as a string, Buffer or Uint8Array
// - key - optional key Uint8Array, up to 64 bytes
// - outlen - optional output length in bytes, default 64
function blake2b (input, key, outlen) {
    // preprocess inputs
    outlen = outlen || 64
    input = normalizeInput(input)

    // do the math
    var ctx = blake2b_init(outlen, key)
    blake2b_update(ctx, input)
    return blake2b_final(ctx)
}

// Computes the BLAKE2B hash of a string or byte array
//
// Returns an n-byte hash in hex, all lowercase
//
// Parameters:
// - input - the input bytes, as a string, Buffer, or Uint8Array
// - key - optional key Uint8Array, up to 64 bytes
// - outlen - optional output length in bytes, default 64
function blake2bHex (input, key, outlen) {
    var output = blake2b(input, key, outlen)
    return toHex(output)
}



/******************************************************************************
 * Copyright © 2013-2016 The Nxt Core Developers.                             *
 *                                                                            *
 * See the AUTHORS.txt, DEVELOPER-AGREEMENT.txt and LICENSE.txt files at      *
 * the top-level directory of this distribution for the individual copyright  *
 * holder information and the developer policies on copyright and licensing.  *
 *                                                                            *
 * Unless otherwise agreed in a custom licensing agreement, no part of the    *
 * Nxt software, including this file, may be copied, modified, propagated,    *
 * or distributed except according to the terms contained in the LICENSE.txt  *
 * file.                                                                      *
 *                                                                            *
 * Removal or modification of this copyright notice is prohibited.            *
 *                                                                            *
 ******************************************************************************/

var converters = function() {
	var charToNibble = {};
	var nibbleToChar = [];
	var i;
	for (i = 0; i <= 9; ++i) {
		var character = i.toString();
		charToNibble[character] = i;
		nibbleToChar.push(character);
	}

	for (i = 10; i <= 15; ++i) {
		var lowerChar = String.fromCharCode('a'.charCodeAt(0) + i - 10);
		var upperChar = String.fromCharCode('A'.charCodeAt(0) + i - 10);

		charToNibble[lowerChar] = i;
		charToNibble[upperChar] = i;
		nibbleToChar.push(lowerChar);
	}

	return {
		byteArrayToHexString: function(bytes) {
			var str = '';
			for (var i = 0; i < bytes.length; ++i) {
				if (bytes[i] < 0) {
					bytes[i] += 256;
				}
				str += nibbleToChar[bytes[i] >> 4] + nibbleToChar[bytes[i] & 0x0F];
			}

			return str;
		},
		stringToByteArray: function(str) {
			str = unescape(encodeURIComponent(str));

			var bytes = new Array(str.length);
			for (var i = 0; i < str.length; ++i)
				bytes[i] = str.charCodeAt(i);

			return bytes;
		},
		hexStringToByteArray: function(str) {
			var bytes = [];
			var i = 0;
			if (0 !== str.length % 2) {
				bytes.push(charToNibble[str.charAt(0)]);
				++i;
			}

			for (; i < str.length - 1; i += 2)
				bytes.push((charToNibble[str.charAt(i)] << 4) + charToNibble[str.charAt(i + 1)]);

			return bytes;
		},
		stringToHexString: function(str) {
			return this.byteArrayToHexString(this.stringToByteArray(str));
		},
		hexStringToString: function(hex) {
			return this.byteArrayToString(this.hexStringToByteArray(hex));
		},
		checkBytesToIntInput: function(bytes, numBytes, opt_startIndex) {
			var startIndex = opt_startIndex || 0;
			if (startIndex < 0) {
				throw new Error('Start index should not be negative');
			}

			if (bytes.length < startIndex + numBytes) {
				throw new Error('Need at least ' + (numBytes) + ' bytes to convert to an integer');
			}
			return startIndex;
		},
		byteArrayToSignedShort: function(bytes, opt_startIndex) {
			var index = this.checkBytesToIntInput(bytes, 2, opt_startIndex);
			var value = bytes[index];
			value += bytes[index + 1] << 8;
			return value;
		},
		byteArrayToSignedInt32: function(bytes, opt_startIndex) {
			var index = this.checkBytesToIntInput(bytes, 4, opt_startIndex);
			value = bytes[index];
			value += bytes[index + 1] << 8;
			value += bytes[index + 2] << 16;
			value += bytes[index + 3] << 24;
			return value;
		},
		byteArrayToBigInteger: function(bytes, opt_startIndex) {
			var index = this.checkBytesToIntInput(bytes, 8, opt_startIndex);

			var value = new BigInteger("0", 10);

			var temp1, temp2;

			for (var i = 7; i >= 0; i--) {
				temp1 = value.multiply(new BigInteger("256", 10));
				temp2 = temp1.add(new BigInteger(bytes[opt_startIndex + i].toString(10), 10));
				value = temp2;
			}

			return value;
		},
		// create a wordArray that is Big-Endian
		byteArrayToWordArray: function(byteArray) {
			var i = 0,
				offset = 0,
				word = 0,
				len = byteArray.length;
			var words = new Uint32Array(((len / 4) | 0) + (len % 4 == 0 ? 0 : 1));

			while (i < (len - (len % 4))) {
				words[offset++] = (byteArray[i++] << 24) | (byteArray[i++] << 16) | (byteArray[i++] << 8) | (byteArray[i++]);
			}
			if (len % 4 != 0) {
				word = byteArray[i++] << 24;
				if (len % 4 > 1) {
					word = word | byteArray[i++] << 16;
				}
				if (len % 4 > 2) {
					word = word | byteArray[i++] << 8;
				}
				words[offset] = word;
			}
			var wordArray = new Object();
			wordArray.sigBytes = len;
			wordArray.words = words;

			return wordArray;
		},
		// assumes wordArray is Big-Endian
		wordArrayToByteArray: function(wordArray) {
			return converters.wordArrayToByteArrayImpl(wordArray, true);
		},
		wordArrayToByteArrayImpl: function(wordArray, isFirstByteHasSign) {
			var len = wordArray.words.length;
			if (len == 0) {
				return new Array(0);
			}
			var byteArray = new Array(wordArray.sigBytes);
			var offset = 0,
				word, i;
			for (i = 0; i < len - 1; i++) {
				word = wordArray.words[i];
				byteArray[offset++] = isFirstByteHasSign ? word >> 24 : (word >> 24) & 0xff;
				byteArray[offset++] = (word >> 16) & 0xff;
				byteArray[offset++] = (word >> 8) & 0xff;
				byteArray[offset++] = word & 0xff;
			}
			word = wordArray.words[len - 1];
			byteArray[offset++] = isFirstByteHasSign ? word >> 24 : (word >> 24) & 0xff;
			if (wordArray.sigBytes % 4 == 0) {
				byteArray[offset++] = (word >> 16) & 0xff;
				byteArray[offset++] = (word >> 8) & 0xff;
				byteArray[offset++] = word & 0xff;
			}
			if (wordArray.sigBytes % 4 > 1) {
				byteArray[offset++] = (word >> 16) & 0xff;
			}
			if (wordArray.sigBytes % 4 > 2) {
				byteArray[offset++] = (word >> 8) & 0xff;
			}
			return byteArray;
		},
		byteArrayToString: function(bytes, opt_startIndex, length) {
			if (length == 0) {
				return "";
			}

			if (opt_startIndex && length) {
				var index = this.checkBytesToIntInput(bytes, parseInt(length, 10), parseInt(opt_startIndex, 10));

				bytes = bytes.slice(opt_startIndex, opt_startIndex + length);
			}

			return decodeURIComponent(escape(String.fromCharCode.apply(null, bytes)));
		},
		byteArrayToShortArray: function(byteArray) {
			var shortArray = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
			var i;
			for (i = 0; i < 16; i++) {
				shortArray[i] = byteArray[i * 2] | byteArray[i * 2 + 1] << 8;
			}
			return shortArray;
		},
		shortArrayToByteArray: function(shortArray) {
			var byteArray = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
			var i;
			for (i = 0; i < 16; i++) {
				byteArray[2 * i] = shortArray[i] & 0xff;
				byteArray[2 * i + 1] = shortArray[i] >> 8;
			}

			return byteArray;
		},
		shortArrayToHexString: function(ary) {
			var res = "";
			for (var i = 0; i < ary.length; i++) {
				res += nibbleToChar[(ary[i] >> 4) & 0x0f] + nibbleToChar[ary[i] & 0x0f] + nibbleToChar[(ary[i] >> 12) & 0x0f] + nibbleToChar[(ary[i] >> 8) & 0x0f];
			}
			return res;
		},
		/**
		 * Produces an array of the specified number of bytes to represent the integer
		 * value. Default output encodes ints in little endian format. Handles signed
		 * as well as unsigned integers. Due to limitations in JavaScript's number
		 * format, x cannot be a true 64 bit integer (8 bytes).
		 */
		intToBytes_: function(x, numBytes, unsignedMax, opt_bigEndian) {
			var signedMax = Math.floor(unsignedMax / 2);
			var negativeMax = (signedMax + 1) * -1;
			if (x != Math.floor(x) || x < negativeMax || x > unsignedMax) {
				throw new Error(
					x + ' is not a ' + (numBytes * 8) + ' bit integer');
			}
			var bytes = [];
			var current;
			// Number type 0 is in the positive int range, 1 is larger than signed int,
			// and 2 is negative int.
			var numberType = x >= 0 && x <= signedMax ? 0 :
				x > signedMax && x <= unsignedMax ? 1 : 2;
			if (numberType == 2) {
				x = (x * -1) - 1;
			}
			for (var i = 0; i < numBytes; i++) {
				if (numberType == 2) {
					current = 255 - (x % 256);
				} else {
					current = x % 256;
				}

				if (opt_bigEndian) {
					bytes.unshift(current);
				} else {
					bytes.push(current);
				}

				if (numberType == 1) {
					x = Math.floor(x / 256);
				} else {
					x = x >> 8;
				}
			}
			return bytes;

		},
		int32ToBytes: function(x, opt_bigEndian) {
			return converters.intToBytes_(x, 4, 4294967295, opt_bigEndian);
		},
		int16ToBytes: function(x, opt_bigEndian) {
			return converters.intToBytes_(x, 2, 65535, opt_bigEndian);
		},
		/**
         * Based on https://groups.google.com/d/msg/crypto-js/TOb92tcJlU0/Eq7VZ5tpi-QJ
         * Converts a word array to a Uint8Array.
         * @param {WordArray} wordArray The word array.
         * @return {Uint8Array} The Uint8Array.
         */
        wordArrayToByteArrayEx: function (wordArray) {
            // Shortcuts
            var words = wordArray.words;
            var sigBytes = wordArray.sigBytes;

            // Convert
            var u8 = new Uint8Array(sigBytes);
            for (var i = 0; i < sigBytes; i++) {
                var byte = (words[i >>> 2] >>> (24 - (i % 4) * 8)) & 0xff;
                u8[i]=byte;
            }

            return u8;
        },
        /**
         * Converts a Uint8Array to a word array.
         * @param {string} u8Str The Uint8Array.
         * @return {WordArray} The word array.
         */
        byteArrayToWordArrayEx: function (u8arr) {
            // Shortcut
            var len = u8arr.length;

            // Convert
            var words = [];
            for (var i = 0; i < len; i++) {
                words[i >>> 2] |= (u8arr[i] & 0xff) << (24 - (i % 4) * 8);
            }

            return CryptoJS.lib.WordArray.create(words, len);
        }
	}
}();
/******************************************************************************
 * Copyright © 2016 The Waves Developers.                                *
 *                                                                            *
 * See the LICENSE files at                                                   *
 * the top-level directory of this distribution for the individual copyright  *
 * holder information and the developer policies on copyright and licensing.  *
 *                                                                            *
 * Unless otherwise agreed in a custom licensing agreement, no part of the    *
 * Waves software, including this file, may be copied, modified, propagated,  *
 * or distributed except according to the terms contained in the LICENSE      *
 * file.                                                                      *
 *                                                                            *
 * Removal or modification of this copyright notice is prohibited.            *
 *                                                                            *
 ******************************************************************************/

/**
 * @requires {decimal.js}
 */

var Currency = (function () {
    var currencyCache = {};

    function Currency(data) {
        data = data || {};

        this.id = data.id; // base58 encoded asset id of the currency
        this.displayName = data.displayName;
        this.shortName = data.shortName || data.displayName;
        this.precision = data.precision; // number of decimal places after a decimal point
        this.verified = data.verified || false;

        if (data.roundingMode !== undefined) {
            this.roundingMode = data.roundingMode;
        } else {
            this.roundingMode = Decimal.ROUND_HALF_UP;
        }

        return this;
    }

    Currency.prototype.toString = function () {
        if (this.shortName)
            return this.shortName;

        return this.displayName;
    };

    var WAVES = new Currency({
        id: '',
        displayName: 'Waves',
        shortName: 'WAVES',
        precision: 8,
        verified: true
    });

    var BTC = new Currency({
        id: '8LQW8f7P5d5PZM7GtZEBgaqRPGSzS3DfPuiXrURJ4AJS',
        displayName: 'Bitcoin',
        shortName: 'BTC',
        precision: 8,
        verified: true
    });

    var BCH = new Currency({
        id: 'zMFqXuoyrn5w17PFurTqxB7GsS71fp9dfk6XFwxbPCy',
        displayName: 'Bitcoin Cash',
        shortName: 'BCH',
        precision: 8,
        verified: true
    });

    var ETH = new Currency({
        id: '474jTeYx2r2Va35794tCScAXWJG9hU2HcgxzMowaZUnu',
        displayName: 'Ethereum',
        shortName: 'ETH',
        precision: 8,
        verified: true
    });

    var LTC = new Currency({
        id: 'HZk1mbfuJpmxU1Fs4AX5MWLVYtctsNcg6e2C6VKqK8zk',
        displayName: 'Litecoin',
        shortName: 'LTC',
        precision: 8,
        verified: true
    });

    var ZEC = new Currency({
        id: 'BrjUWjndUanm5VsJkbUip8VRYy6LWJePtxya3FNv4TQa',
        displayName: 'ZCash',
        shortName: 'ZEC',
        precision: 8,
        verified: true
    });

    var USD = new Currency({
        id: 'Ft8X1v1LTa1ABafufpaCWyVj8KkaxUWE6xBhW6sNFJck',
        displayName: 'US Dollar',
        shortName: 'USD',
        precision: 2,
        verified: true
    });

    var EUR = new Currency({
        id: 'Gtb1WRznfchDnTh37ezoDTJ4wcoKaRsKqKjJjy7nm2zU',
        displayName: 'Euro',
        shortName: 'EUR',
        precision: 2,
        verified: true
    });

    var CNY = new Currency({
        id: 'DEJbZipbKQjwEiRjx2AqQFucrj5CZ3rAc4ZvFM8nAsoA',
        displayName: 'Chinese Yuan',
        shortName: 'CNY',
        precision: 2,
        verified: true
    });

    var WCT = new Currency({
        id: 'DHgwrRvVyqJsepd32YbBqUeDH4GJ1N984X8QoekjgH8J',
        displayName: 'Waves Community',
        shortName: 'WCT',
        precision: 2,
        verified: true
    });

    var MRT = new Currency({
        id: '4uK8i4ThRGbehENwa6MxyLtxAjAo1Rj9fduborGExarC',
        displayName: 'Miner Reward',
        shortName: 'MRT',
        precision: 2,
        verified: true
    });

    var WGO = new Currency({
        id: '4eT6R8R2XuTcBuTHiXVQsh2dN2mg3c2Qnp95EWBNHygg',
        displayName: 'WavesGo',
        shortName: 'WGO',
        precision: 8,
        verified: true
    });

    var INCNT = new Currency({
        id: 'FLbGXzrpqkvucZqsHDcNxePTkh2ChmEi4GdBfDRRJVof',
        displayName: 'Incent',
        shortName: 'INCNT',
        precision: 8,
        verified: true
    });

    var RBX = new Currency({
        id: 'AnERqFRffNVrCbviXbDEdzrU6ipXCP5Y1PKpFdRnyQAy',
        displayName: 'Ripto Bux',
        shortName: 'RBX',
        precision: 8,
        verified: true
    });

    var MER = new Currency({
        id: 'HzfaJp8YQWLvQG4FkUxq2Q7iYWMYQ2k8UF89vVJAjWPj',
        displayName: 'Mercury',
        shortName: 'MER',
        precision: 8,
        verified: true
    });

    var BAt = new Currency({
        id: 'APz41KyoKuBBh8t3oZjqvhbbsg6f63tpZM5Ck5LYx6h',
        displayName: 'B@nkcoin',
        shortName: 'B@',
        precision: 8,
        verified: true
    });

    var UPC = new Currency({
        id: '4764Pr9DpKQAHAjAVA2uqnrYidLMnM7vpDDLCDWujFTt',
        displayName: 'Upcoin',
        shortName: 'UPC',
        precision: 2,
        verified: true
    });

    var KLN = new Currency({
        id: 'EYz8Zvs62D4d7F5ZgXHCWuzuFaZg63FYnfVQrTWQoLSK',
        displayName: 'Kolion',
        shortName: 'KLN',
        precision: 4,
        verified: true
    });

    var TKS = new Currency({
        id: 'BDMRyZsmDZpgKhdM7fUTknKcUbVVkDpMcqEj31PUzjMy',
        displayName: 'Tokes',
        shortName: 'TKS',
        precision: 8,
        verified: true
    });

    var WPN = new Currency({
        id: 'BkFyeRdrLquxds5FenxyonyfTwMVJJ6o6L7VTaPr5fs3',
        displayName: 'WavesPool.NET',
        shortName: 'WPN',
        precision: 8,
        verified: true
    });

    var EFYT = new Currency({
        id: '725Yv9oceWsB4GsYwyy4A52kEwyVrL5avubkeChSnL46',
        displayName: 'Ergo First Year Token',
        shortName: 'EFYT',
        precision: 8,
        verified: true
    });

    var MGO = new Currency({
        id: '2Y8eFFXDTkxgCvXbMT5K4J38cpDYYbQdciJEZb48vTDj',
        displayName: 'Mobile Go Token',
        shortName: 'MGO',
        precision: 8,
        verified: true
    });

    var ETT = new Currency({
        id: '8ofu3VpEaVCFjRqLLqzTMNs5URKUUQMrPp3k6oFmiCc6',
        displayName: 'EncryptoTel',
        shortName: 'ETT',
        precision: 8,
        verified: true
    });

    var ZRC = new Currency({
        id: '5ZPuAVxAwYvptbCgSVKdTzeud9dhbZ7vvxHVnZUoxf4h',
        displayName: 'ZrCoin',
        shortName: 'ZRC',
        precision: 8,
        verified: true
    });

    var PBKX = new Currency({
        id: '39wcSXj4MdRNRJXA88rVxF7EXWjYixaA3J3EteoN6DMM',
        displayName: 'privateBANKX',
        shortName: 'PBKX',
        precision: 0,
        verified: true
    });

    var PING = new Currency({
        id: 'Bi4w2UuGRt2jAJFfRb8b3SwDUV5x8krCzX2zZHcRfPNc',
        displayName: 'CryptoPing',
        shortName: 'PING',
        precision: 8,
        verified: true
    });

    var STAR = new Currency({
        id: 'BTfuGGoeA934Ta1fgcehQ5UhbHuWKj4don64ZNBuMT38',
        displayName: 'Starrie',
        shortName: 'STAR',
        precision: 8,
        verified: true
    });

    var BEAR = new Currency({
        id: '9gnc5UCY6RxtSi9FEJkcD57r5NBgdr45DVYtunyDLrgC',
        displayName: 'BearWaves',
        shortName: 'BEAR',
        precision: 2,
        verified: true
    });

    var DAR = new Currency({
        id: 'K5JcgN8UdwNdh5sbdAuPMm5XEd5aFvoXaC3iHsHVz1d',
        displayName: 'Darcrus',
        shortName: 'DAR',
        precision: 6,
        verified: true
    });

    var GLIPP = new Currency({
        id: '9g5JiYThxFTxknSMA3TT5xoXG7GYjRrTJxxLeeoQ36kJ',
        displayName: 'GLIPP',
        shortName: 'GLIPP',
        precision: 8,
        verified: true
    });

    var mTNT = new Currency({
        id: '8HYDtqEuHj3RDcwR8yxEvPq1qQSB9FazC8wMHtRb2TFe',
        displayName: 'MyTrackNet',
        shortName: 'mTNT',
        precision: 6,
        verified: true
    });

    var BKT = new Currency({
        id: '9c7U7bXdP23oHpmGKwGfSsjFrpxdRcp3tp28qbfhEc3d',
        displayName: '$bkt',
        shortName: 'BKT',
        precision: 0,
        verified: true
    });

    var WGR = new Currency({
        id: '8t8DMJFQu5GEhvAetiA8aHa3yPjxLj54sBnZsjnJ5dsw',
        displayName: 'Wagerr',
        shortName: 'WGR',
        precision: 8,
        verified: true
    });

    var PBT = new Currency({
        id: 'EdDvbhk4wJ1kL6pMCq1V36GbQE2nGE7Metb87zbaY2JL',
        displayName: 'Primalbase Token',
        shortName: 'PBT',
        precision: 4,
        verified: true
    });

    var PPIO = new Currency({
        id: '8UHSg6jCDTUvKT3LmeDjoaPxKmnJhdLEgBHU3vUrojSm',
        displayName: 'pospool_io',
        shortName: 'PPIO',
        precision: 2,
        verified: true
    });

    var STA = new Currency({
        id: '3SdrmU1GGZRiZz12MrMcfUz4JksTzvcU25cLFXpZy1qz',
        displayName: 'Starta',
        shortName: 'STA',
        precision: 2,
        verified: true
    });

    var CORE = new Currency({
        id: '3MyMJ9pXLTDnMQhNgoDUBtcfmaGVgnaZNARZwcZzMFk7',
        displayName: 'CORE',
        shortName: 'CORE',
        precision: 8,
        verified: true
    });

    var KSS = new Currency({
        id: 'Dq6ku3HyiMfKvorz2PLRAPwa9ykF78V1uiBhXtMbL2f2',
        displayName: 'Krosscoin',
        shortName: 'KSS',
        precision: 3,
        verified: true
    });

    var WFN = new Currency({
        id: '7yXJqP2zpXTiXuS2o25seUHYxdDnfSPZJ3SEm5DrQ7cx',
        displayName: 'WavesFullNode',
        shortName: 'WFN',
        precision: 8,
        verified: true
    });

    var GRPH = new Currency({
        id: '13QuhSAkAueic5ncc8YRwyNxGQ6tRwVSS44a7uFgWsnk',
        displayName: 'Graph',
        shortName: 'GRPH',
        precision: 8,
        verified: true
    });

    var ESC = new Currency({
        id: 'FoKiAEqHSit88f4iu1neKkzsanYHQqLRyR4DXucRGKbW',
        displayName: 'EstateCoin',
        shortName: 'ESC',
        precision: 2,
        verified: true
    });

    var AGRO = new Currency({
        id: 'J8mgyjKQb4M7DjEKvewBSvKZULMZMDpUtua9VtByLbVD',
        displayName: 'Agro token',
        shortName: 'AGRO',
        precision: 8,
        verified: true
    });

    var KING = new Currency({
        id: 'CHUTTYkDd9qFmQthCL7eHTDHwYudfthqwYCYsdvpCZbf',
        displayName: 'King93',
        shortName: 'KING',
        precision: 8,
        verified: true
    });

    var ARNA = new Currency({
        id: 'BsDmB74Y1PvtVrE741i5CJThChQHHF96hDL5nXwv7JdS',
        displayName: 'Arena',
        shortName: 'ARNA',
        precision: 8,
        verified: true
    });

    var WNET = new Currency({
        id: 'AxAmJaro7BJ4KasYiZhw7HkjwgYtt2nekPuF2CN9LMym',
        displayName: 'Wavesnode.NET',
        shortName: 'WNET',
        precision: 8,
        verified: true
    });

    var PBK = new Currency({
        id: '3eBcKvyMavxACq54yvXk1rCAP4E475NCwGKV6AmQQNaw',
        displayName: 'PeerBanks',
        shortName: 'PBK',
        precision: 8,
        verified: true
    });

    var TOM = new Currency({
        id: '3e7aYkysNohFDonLVaUFGgZ46mV3Y3r7Rqzi95GYGxeK',
        displayName: 'Tomahawkcoin',
        shortName: 'TOM',
        precision: 0,
        verified: true
    });

    var ViC = new Currency({
        id: 'Gh8Ed6n1y9wscFHT6s4EH6uhKajvNQ88oPkkFkYkgXyX',
        displayName: 'WaVialcoin',
        shortName: 'ViC',
        precision: 8,
        verified: true
    });

    var EQ = new Currency({
        id: 'DoL6wC5a72Fuxg7FtfUMWbJB9kjRuvQ3BQKrgjym3gh6',
        displayName: 'EQUI Token',
        shortName: 'EQ',
        precision: 8,
        verified: true
    });

    var SHDW = new Currency({
        id: 'ETLzrCpBqTrpyuMGdiVLBPZnUoKwte88oVdJjoFi5R2h',
        displayName: 'ShadowToken',
        shortName: 'SHDW',
        precision: 8,
        verified: true
    });

    var GIN = new Currency({
        id: '9x9ATvB61fE5TU1zRdZvyvA5Q8ZYEs2yRmzTBAs69R9N',
        displayName: 'GingerDrink.EU',
        shortName: 'GIN',
        precision: 2,
        verified: true
    });

    var NEWS = new Currency({
        id: '2EAUTcAsFMsndSgiGacKRvygFR1e6gdSd8bEpiemsTPE',
        displayName: 'NEWSTOKEN',
        shortName: 'NEWS',
        precision: 8,
        verified: true
    });

    var COXST = new Currency({
        id: '7tZxVdAWc8QvsMrXBoicMgU2bSJsaEpFJnPYn1H31B8B',
        displayName: 'CoExistCoin',
        shortName: 'COXST',
        precision: 8,
        verified: true
    });

    var SMR = new Currency({
        id: 'EbY2Uf9ukD4ndg5J7MA7CjhB7xbAsiViTmVSemb186V8',
        displayName: 'Summer',
        shortName: 'SMR',
        precision: 8,
        verified: true
    });

    var RDT = new Currency({
        id: 'Fw2Sg8x4VZyxU5ManJTo69JCKg9Rox7xDNKxdQdxXDWk',
        displayName: 'Ryder Token',
        shortName: 'RDT',
        precision: 2,
        verified: true
    });

    var IRA = new Currency({
        id: '3eBcKvyMavxACq54yvXk1rCAP4E475NCwGKV6AmQQNaw',
        displayName: 'PeerBanks',
        shortName: 'IRA',
        precision: 8,
        verified: true
    });

    var _2B4T = new Currency({
        id: '2LU8GwJFvVebrCvgDhMTLDzm3dHxuN1x7ks8dQRiSj9N',
        displayName: '2B4T',
        shortName: '2B4T',
        precision: 2,
        verified: true
    });

    var MBX = new Currency({
        id: '2CX6EFHYmXYyop4hD7dUywST5K51Hvi2m5brFo35C6EZ',
        displayName: 'MyBitX',
        shortName: 'MBX',
        precision: 2,
        verified: true
    });

    var KNOWS = new Currency({
        id: 'CqSHx4WhszTZhabfWD8UuX8efg5hbZTPRNtnwW1ojJxe',
        displayName: 'KNOWS',
        shortName: 'KNOWS',
        precision: 8,
        verified: true
    });

    var MBI = new Currency({
        id: 'CJpRwfpBcFyA6p3g1fb7xuiArSQ7xLkNH8SD9AB4HeD9',
        displayName: 'MonsterByte',
        shortName: 'MBI',
        precision: 2,
        verified: true
    });

    var COF = new Currency({
        id: 'AcrRM9STdBu5PNiFveTCbRFTS8tADhKcsbC2KBp8A4tx',
        displayName: 'CoffeeCoin',
        shortName: 'COF',
        precision: 3,
        verified: true
    });

    var CHILL = new Currency({
        id: 'DsxRbfYXzwf4PFwUD6kyEJhj2Wd5E9NsHr5WynVKTzie',
        displayName: 'Chill',
        shortName: 'CHILL',
        precision: 8,
        verified: true
    });

    var KUN = new Currency({
        id: 'F6EK5bcdEShWPA9pGdgqGYmPPUZ9FaHnyVwPZfXCTxV7',
        displayName: 'KUNA',
        shortName: 'KUN',
        precision: 0,
        verified: true
    });

    var CEIT = new Currency({
        id: '83Y1Ub3Kp9uitTTgKGPnaZE6EC793XuC3muoJC8zsFir',
        displayName: 'CorpEdu',
        shortName: 'CEIT',
        precision: 4,
        verified: true
    });

    var SGIT = new Currency({
        id: 'BYkKnXLUS3qRyNvbSTvNWJ3pTsW7uZGHhV4HQ3pdf6DW',
        displayName: 'SmartGames',
        shortName: 'SGIT',
        precision: 4,
        verified: true
    });

    var AHT = new Currency({
        id: 'HfFHZaPzGMSdHvaaZ7S8mrZrPWEyGzfA6VDuSRzb8uY6',
        displayName: 'Bowhead',
        shortName: 'AHT',
        precision: 8,
        verified: true
    });

    var HALAL = new Currency({
        id: 'BjAZxDeFpYaQ1gwmg65vYArhve31k8j9mscQDecNZ2bX',
        displayName: 'HALAL',
        shortName: 'HALAL',
        precision: 7,
        verified: true
    });

    var DIMO = new Currency({
        id: 'BEth3AJY65jWWF7KCDSFgMS6g5AvDvoAWrn8UYEsoA17',
        displayName: 'DIMO',
        shortName: 'DIMO',
        precision: 8,
        verified: true
    });

    var WIN = new Currency({
        id: '7Ry7rUTSS1iCJBFa7trCbwzAwnvvAUrX3gcz2iTL8aAF',
        displayName: 'WinToken',
        shortName: 'WIN',
        precision: 2,
        verified: true
    });

    var YTB = new Currency({
        id: 'HhzJGgbbogGQubKkHUyEaHKs7fBRebjoJkgiDQ8jrYee',
        displayName: 'YouTubeCoin',
        shortName: 'YTB',
        precision: 0,
        verified: true
    });

    var GFL = new Currency({
        id: 'D6hYNYUSxsLtvkUJ4Mxp6s7mT4WACbwJSsVGCQKxkSfH',
        displayName: 'GoldenFleece',
        shortName: 'GFL',
        precision: 8,
        verified: true
    });

    var DAT = new Currency({
        id: 'DBLes8Bxb1P4qL1XaRRPL4d4xTVZSWHKP4oKGyFZjwBe',
        displayName: 'DATALIFE',
        shortName: 'DAT',
        precision: 6,
        verified: true
    });

    var VK = new Currency({
        id: '5WLqNPkA3oDp1hTFCeUukTL1qvFnk9Ew7DXTtCzvoCxi',
        displayName: 'VKCoin',
        shortName: 'VK',
        precision: 0,
        verified: true
    });

    var UWT = new Currency({
        id: 'AdEVVde2XTDa1qDPWfChUGH2XP67duQ4NnpQWXs7wETF',
        displayName: 'Useless Token',
        shortName: 'UWT',
        precision: 0,
        verified: true
    });

    var AP_0 = new Currency({
        id: 'BYMmfwocym3d3cuFc9XytbAWGCdAM9875n5fTFokGTMm',
        displayName: 'AP-glasscoin#0',
        shortName: 'AP#0',
        precision: 0,
        verified: true
    });

    var AP_1 = new Currency({
        id: 'FgPzwZqGngVG45d6WtP5273diR8cHRjs95aT6g1tuFUv',
        displayName: 'AP-glasscoin#1',
        shortName: 'AP#1',
        precision: 0,
        verified: true
    });

    var AP_2 = new Currency({
        id: '6qLNnEV34cE8CZi5hk3nTNiUeHZcKz35R7AafPSukSAt',
        displayName: 'AP-glasscoin#2',
        shortName: 'AP#2',
        precision: 0,
        verified: true
    });

    var OCL = new Currency({
        id: 'ABFYQjwDHSct6rNk59k3snoZfAqNHVZdHz4VGJe2oCV5',
        displayName: '$OCL Oceanlab',
        shortName: 'OCL',
        precision: 8,
        verified: true
    });

    var OCC = new Currency({
        id: 'CL9PN5rpMm3ed2x6g9SWDQJfHciZFwXee2hhehmitzRj',
        displayName: 'OurCoin Classic',
        shortName: 'OCC',
        precision: 2,
        verified: true
    });

    var SMART = new Currency({
        id: '4xDfFdPorzNmB5w8p28Fs5z6fPMf4QKJGcxY3DWT9ugG',
        displayName: 'SMART',
        shortName: 'SMART',
        precision: 8,
        verified: true
    });

    var DCN = new Currency({
        id: 'DnAGJqeraWszYBfRjjbxtZDb1vggjUDZjWo49i15hGo1',
        displayName: 'Duocoin',
        shortName: 'DCN',
        precision: 2,
        verified: true
    });

    var RSC = new Currency({
        id: 'EMdiF8uaySswfCdMxc114rSfzUsAKCtK9d8eSx6ruKP4',
        displayName: 'RusCoin',
        shortName: 'RSC',
        precision: 5,
        verified: true
    });

    var LIKE = new Currency({
        id: '71tUQ7miLb2vNViGYCarYvdNj2BnDyxuFMCQivViqZq6',
        displayName: 'like',
        shortName: 'LIKE',
        precision: 8,
        verified: true
    });

    var FUPOOF = new Currency({
        id: 'EAmQHCqBVeNunvYRC5bFQh6mtvF34bL9qAwug5PGvjjE',
        displayName: 'Fupoof Coin',
        shortName: 'FUPOOF',
        precision: 3,
        verified: true
    });

    var ANY = new Currency({
        id: '2L9piWsMG4dZ84WgybXa9SPYFhyBEiP5fcv1BmJ9Gy7X',
        displayName: 'anyco',
        shortName: 'ANY',
        precision: 8,
        verified: true
    });

    var BRW = new Currency({
        id: '3EAHaZPwV5gCoWkoLhjj7rSz9ix7Q4SE6mFczoxA3f9D',
        displayName: 'BrWaves',
        shortName: 'BRW',
        precision: 3,
        verified: true
    });

    var CNX = new Currency({
        id: 'CSX1Ynv6AXmJmfnG1hBczrL9tN5HWrjVx5Ur3WJeuErv',
        displayName: 'Cryptonetix',
        shortName: 'CNX',
        precision: 8,
        verified: true
    });

    var DARF = new Currency({
        id: '96NFBPoikAeacesZggFa6wBXAyczgZFyupbX5rJwFfdQ',
        displayName: 'DARF',
        shortName: 'DARF',
        precision: 8,
        verified: true
    });

    var WNT = new Currency({
        id: 'EqdXBgKgKqdpD3kGT4tS9VgLifZXS3ASihwM3hnprNdU',
        displayName: 'WavesNotify',
        shortName: 'WNT',
        precision: 0,
        verified: true
    });

    var CWV = new Currency({
        id: 'HxxSmVuX4HbHDiDSGg96nx7wgCBhB9UPHh6pxgnKXjv4',
        displayName: 'Cryptowave',
        shortName: 'CWV',
        precision: 3,
        verified: true
    });

    var WCASH = new Currency({
        id: '2sikuhpBdZV2x5gHoA7adCStxuTSJ8m6r4hSRDLKz2zN',
        displayName: 'WCASH',
        shortName: 'WCASH',
        precision: 8,
        verified: true
    });

    var LIFE = new Currency({
        id: '5qtfgMsSAQsYMC947aYZcej1qMVQvMfRgLc3mexMXWE1',
        displayName: 'LIFE',
        shortName: 'LIFE',
        precision: 8,
        verified: true
    });

    var RDCR = new Currency({
        id: 'EXKrrWnMYnZrPYbrygnwzKKx5jjaEqALEgQhtoCcBdKG',
        displayName: 'RDCR',
        shortName: 'RDCR',
        precision: 8,
        verified: true
    });

    var THNX = new Currency({
        id: '2XQGE8LY9hUruumZ9ewK82akHMnS8a2nSXKdKXfBnuLH',
        displayName: 'ThankYou',
        shortName: 'THNX',
        precision: 4,
        verified: true
    });

    var IKV = new Currency({
        id: '8SNKiX53Yi2yjG1ZbRM4dEQJaJDpns7aN1FWBg5AZDBn',
        displayName: 'Ikeva',
        shortName: 'IKV',
        precision: 5,
        verified: true
    });

    var WDESK = new Currency({
        id: 'CqdGdzvXVp2Gxn7wCZgCboMQu2cWYf6HKAsZFyg3Sq7Q',
        displayName: 'WavesDesk',
        shortName: 'WDESK',
        precision: 8,
        verified: true
    });

    var SUR = new Currency({
        id: '5EAm2T6rKnaDHBT8ptWnuEqvKszp8SW9XPFYD1yAAW2x',
        displayName: 'Suretly',
        shortName: 'SUR',
        precision: 8,
        verified: true
    });

    var SIBERIA = new Currency({
        id: '9QrUSk9mkkdRPKDzNnEVDBoMDb6iBny4XpxsYtpwJdH9',
        displayName: 'SIBERIA',
        shortName: 'SIBERIA',
        precision: 2,
        verified: true
    });

    var MODO = new Currency({
        id: '9kEcosT68xX1Azx2ZkUkgWmwQ5SxzN9rssFieiaxT1PN',
        displayName: 'MODO',
        shortName: 'MODO',
        precision: 8,
        verified: true
    });

    var GIVE = new Currency({
        id: 'AvcbtGUgZwXrfn7rJwBLzoHCrJhtUusnco5amqF7foWU',
        displayName: 'Give Coin',
        shortName: 'GIVE',
        precision: 2,
        verified: true
    });

    var SOL = new Currency({
        id: '6sosMnsaCM5iowMjdPHXDJNrByrw8L8SQCDeD2xoNeK4',
        displayName: 'SolarLab',
        shortName: 'SOL',
        precision: 8,
        verified: true
    });

    var EOT = new Currency({
        id: 'GdnNbe6E3txF63gv3rxhpfxytTJtG7ZYyHAvWWrrEbK5',
        displayName: 'EOT Token',
        shortName: 'EOT',
        precision: 8,
        verified: true
    });

    var FIX = new Currency({
        id: 'GS5RfWDS8ytVnxqr7M2pnqeFuu7BpSwGnADTcw23FvbZ',
        displayName: 'Finamatrix',
        shortName: 'FIX',
        precision: 8,
        verified: true
    });

    var KKO = new Currency({
        id: '6gZUKe6EhDnA8vMFdwLMjLm3QLhRe1v66LvST7ZWJcZW',
        displayName: 'Cacao Shares',
        shortName: 'KKO',
        precision: 8,
        verified: true
    });

    var JNT = new Currency({
        id: '8FHrsE6ixLyEnbcJqxXaGRcEU2aziuEBvQ6Tebgqrv5c',
        displayName: 'jNetCoin',
        shortName: 'JNT',
        precision: 5,
        verified: true
    });

    var CGT = new Currency({
        id: 'CVxqNTyfD39WrNsXSfpAUTzsA76astJpzQVEiZn8a1Ai',
        displayName: 'Cryptogene Token',
        shortName: 'CGT',
        precision: 0,
        verified: true
    });

    var AFFT = new Currency({
        id: '9UFoSQSZZU5j8au1cLYgJGNNtuXAc2s1C4Xd8sPimqL8',
        displayName: 'AFFT',
        shortName: 'AFFT',
        precision: 8,
        verified: true
    });

    var MFL = new Currency({
        id: '7EHVUjcgEV9Du8qp95tS1eBV8DFtenmX64H3QawdCkC4',
        displayName: 'McFly',
        shortName: 'MFL',
        precision: 2,
        verified: true
    });

    var TURTL = new Currency({
        id: '7VDRFwm2HbaJCk3U4HQDhLGdSCxZwPe3cHefVXy7ejYe',
        displayName: 'WorldTurtleCoin',
        shortName: 'TURTL',
        precision: 8,
        verified: true
    });

    var PropX = new Currency({
        id: '7QVcLyMCQ53KSCLhZN7m3FLbfjuoHxxk5xBiToE1gmAE',
        displayName: 'PropX',
        shortName: 'PropX',
        precision: 8,
        verified: true
    });

    var ECT = new Currency({
        id: 'ErZseGoQ81jWTnKbGim7djVgyAqrsYLQr5SwrEjnF7wM',
        displayName: 'eCoin Token',
        shortName: 'ECT',
        precision: 0,
        verified: true
    });

    var STT = new Currency({
        id: 'CNhUwUpGoMmPxDsqrUsVDa6WDzwZVdh4N8gVA85tBB28',
        displayName: 'SmartTracker',
        shortName: 'STT',
        precision: 0,
        verified: true
    });

    var SCLRI = new Currency({
        id: '4GZ5tgKxPeu5kCYpcAE871grUPXWW3My5uccRVHRJ2k2',
        displayName: 'Clean/Smart City',
        shortName: 'SCLRI',
        precision: 2,
        verified: true
    });

    var Knish = new Currency({
        id: 'CvutHGapUdjVHXZ1KwGUD1Z3R2rwDwwbLJrTXSGUYfuK',
        displayName: 'Knish',
        shortName: 'Knish',
        precision: 8,
        verified: true
    });

    var WPC = new Currency({
        id: 'ANTz8NnpfbEcDFXo4gwd7UL5ugc9bdTcPGbEPktRPZw2',
        displayName: 'whoppercoin',
        shortName: 'WPC',
        precision: 1,
        verified: true
    });

    var cryptoSterling = new Currency({
        id: '61LRXnv6iB2QDwBVi34r6eEyx8h7VZdyBApB4aP9eKqA',
        displayName: 'cryptoSterling',
        shortName: 'cryptoSterling',
        precision: 0,
        verified: true
    });

    var NGN = new Currency({
        id: '6CjhSBXPF2gga6s6F9UkGKAtnYawCqySH1wUJA2cU5pW',
        displayName: '₦ | NGN',
        shortName: 'NGN',
        precision: 2,
        verified: true
    });

    var ALTOCAR = new Currency({
        id: '5ZVP6vp8Rt7GneEozNATcs7LPjQfwTun9WwnN1ispAH4',
        displayName: 'ALTOCAR',
        shortName: 'ALTOCAR',
        precision: 8,
        verified: true
    });

    var ANAT = new Currency({
        id: '7YUrQFP6Fgn8EwbQb3rBtJjBattsvX5B4tsCsJrn14Py',
        displayName: 'ANAT',
        shortName: 'ANAT',
        precision: 8,
        verified: true
    });

    var ATKN = new Currency({
        id: '7U5YKTvz7bt85FyWRB9bvSbqtKcdK3YVJDGfuJ1XjxBh',
        displayName: 'A-TOKEN',
        shortName: 'ATKN',
        precision: 8,
        verified: true
    });

    var ATOM = new Currency({
        id: '83M2vz5tTwovXyW6ytrT7771DsEpttaGyCn66toQmT5N',
        displayName: 'AtomCoinAnn',
        shortName: 'ATOM',
        precision: 2,
        verified: true
    });

    var BAR = new Currency({
        id: 'HU5B3q3neZRpq5R9uzoRjopJUpELtnFmz1KW2TAUbp9m',
        displayName: 'BARCOIN',
        shortName: 'BAR',
        precision: 0,
        verified: true
    });

    var BCF = new Currency({
        id: '6ShaywJbyebptogQ5gMUvtbEyCdXqV4gGPfAPEdq2Dre',
        displayName: 'BCF SHARES',
        shortName: 'BCF',
        precision: 6,
        verified: true
    });

    var BET = new Currency({
        id: 'FkgGR1mYeEdPLrvCRTfQcZeyCadWEVGuryDEhuPuZoUf',
        displayName: 'BET\'s',
        shortName: 'BET',
        precision: 1,
        verified: true
    });

    var BIRTAL = new Currency({
        id: 'J1tggntaeLccEr8t9s8cc9VpqGj3QkHMSrfyEkdGzoXF',
        displayName: 'BirTal',
        shortName: 'BIRTAL',
        precision: 8,
        verified: true
    });

    var BITCHEKE = new Currency({
        id: '9CPQU2EdbYxHsiytpZV4L8cypZHL17B4a81xedpspNT8',
        displayName: 'BitCheke',
        shortName: 'BITCHEKE',
        precision: 3,
        verified: true
    });

    var BITD = new Currency({
        id: 'B5f8oYUingX3XyKjRAcimPapELPfFMhRz6oVzUk5GDW5',
        displayName: 'BITDOLLARS',
        shortName: 'BITD',
        precision: 8,
        verified: true
    });

    var BKC = new Currency({
        id: '2a2AorHdSaWiiTiYR11vEKjLBzsqtQ5i1KzPNfW97xBb',
        displayName: 'Blokcloud',
        shortName: 'BKC',
        precision: 8,
        verified: true
    });

    var CROW = new Currency({
        id: '5XWiXK6RbwXsTnY2dSHQWnKVjvLsMAEeE1rFqQz3Ton2',
        displayName: 'CrowdWave',
        shortName: 'CROW',
        precision: 3,
        verified: true
    });

    var CBT = new Currency({
        id: 'HfTchexAmETtGoPCU1V72t6WNgPPoEsLjBTpeeBzC46L',
        displayName: 'CryptoBazar',
        shortName: 'CBT',
        precision: 4,
        verified: true
    });

    var EDEN = new Currency({
        id: 'HQMz6yc8hxzA3MUvvGSNByxWLMcmt6uoz5ZE3ebkS75n',
        displayName: 'EdenChain',
        shortName: 'EDEN',
        precision: 8,
        verified: true
    });

    var EQUA = new Currency({
        id: 'ECcmoyW2wQcQMvXp3QbwnMFBpiRthHj54MpYq7scQBeZ',
        displayName: 'EquaCoin',
        shortName: 'EQUA',
        precision: 4,
        verified: true
    });

    var EQUILD = new Currency({
        id: 'FrErWYxQojiTVMamqLLvkmeKKX9UTXz8EL9NF3AeYWPi',
        displayName: 'equild',
        shortName: 'EQUILD',
        precision: 8,
        verified: true
    });

    var ETERP = new Currency({
        id: 'BiSYeqfANiJjUjR3GwCaeCPZQaT4Ly1vQb12PcambKbz',
        displayName: 'EterPay',
        shortName: 'ETERP',
        precision: 8,
        verified: true
    });

    var FENIX = new Currency({
        id: '3pEoYCzUb7hWvqoMQGPYffTsxxPDkSzwSskypmYFBLFP',
        displayName: 'FENIX&WAVES',
        shortName: 'FENIX',
        precision: 8,
        verified: true
    });

    var FTB = new Currency({
        id: 'E8jdQECM6i9j28bpH81zZWyAwtaZwJMtzPWz4jCCmot3',
        displayName: 'Fincoin',
        shortName: 'FTB',
        precision: 6,
        verified: true
    });

    var FLEX = new Currency({
        id: 't1ocHkKuQLKYhtH7nm1rYuj1iZ8d75bqAjgRTwiGhQF',
        displayName: 'Flex',
        shortName: 'FLEX',
        precision: 0,
        verified: true
    });

    var FNX = new Currency({
        id: 'RiVZJ25d5vMYcVo4XRK5n2whjh4WwYGshmmwXgF9MK4',
        displayName: 'FNX&WVS',
        shortName: 'FNX',
        precision: 8,
        verified: true
    });

    var GBC = new Currency({
        id: 'byHDS3JprxWhPbuYBy4y4SvYbbvZiAQV9MNiDSsRPz6',
        displayName: 'Goldbar coin',
        shortName: 'GBC',
        precision: 3,
        verified: true
    });

    var Grant = new Currency({
        id: 'C9p15S1PJN4tMeodygkBEEr2GQUX5dtbtuadTcuaj7t5',
        displayName: 'Grant',
        shortName: 'Grant',
        precision: 8,
        verified: true
    });

    var GrantsBounty = new Currency({
        id: '47iX3APMeD4ZGmhQr73qg5boyoJZXGWpfX5sbcAD6jsn',
        displayName: 'GrantsBounty',
        shortName: 'GrantsBounty',
        precision: 8,
        verified: true
    });

    var HEART = new Currency({
        id: '5xFEsfHdtHLZ2yexduffCBqryWxV4Py8FHtA9tLWqtrJ',
        displayName: 'HEART',
        shortName: 'HEART',
        precision: 1,
        verified: true
    });

    var HOME = new Currency({
        id: '9fkbSVSceusGtsL9KxQHCaqpt2ddds6ukMEKrabgdbac',
        displayName: 'HomeToken',
        shortName: 'HOME',
        precision: 8,
        verified: true
    });

    var HTC = new Currency({
        id: '7GCmsbyYBJ9DAJayC3hKuZV4REZXdGdXRjWgsY9oB3wZ',
        displayName: 'HotelCoin',
        shortName: 'HTC',
        precision: 8,
        verified: true
    });

    var IMMO = new Currency({
        id: '8yzwMFmNFAv8VALWfmEPHk26tMv9MBS7eHoTm7i1FXyT',
        displayName: 'Immodestea',
        shortName: 'IMMO',
        precision: 8,
        verified: true
    });

    var JNET = new Currency({
        id: '8FHrsE6ixLyEnbcJqxXaGRcEU2aziuEBvQ6Tebgqrv5c',
        displayName: 'jNetCoin',
        shortName: 'JNET',
        precision: 5,
        verified: true
    });

    var KRIP = new Currency({
        id: 'Hm9DM6i5DsnHoPhxWWo5j2bFYYVCUaoC9n66EtzmwgAM',
        displayName: 'KripCoin',
        shortName: 'KRIP',
        precision: 5,
        verified: true
    });

    var LLA = new Currency({
        id: 'CvD7GedwdeHCxtiiQgbEAV6JHxXv9DQ8bkmrFAauiNyy',
        displayName: 'Lalena (LLA)',
        shortName: 'LLA',
        precision: 8,
        verified: true
    });

    var limburg = new Currency({
        id: 'FYCGQ1iKBqbYnQgeLQFEazw4oF2PyRYhdsUPWBEWk7F6',
        displayName: 'LimburgCoin',
        shortName: 'limburg',
        precision: 8,
        verified: true
    });

    var LIVEBIT = new Currency({
        id: '7W2CHBfQFXfkZVrPWrj34W6pveKHVky9dvoFq1MXNY24',
        displayName: 'LiveBit',
        shortName: 'LIVEBIT',
        precision: 8,
        verified: true
    });

    var MED = new Currency({
        id: 'CnkUwcYpVpzk3mMM2XfofymwXBnmrSecFbBdMx6WYDCa',
        displayName: 'Medicine Man',
        shortName: 'MED',
        precision: 8,
        verified: true
    });

    var MNG = new Currency({
        id: '6672vWQDHDV6WRU4GsRjBYo6444bh2fEWmXW1KnSSrw4',
        displayName: 'Mining',
        shortName: 'MNG',
        precision: 8,
        verified: true
    });

    var MMBT = new Currency({
        id: '82in5zvV8XdnFzCwYWCNaNbRWSvEa4CfCYfJSAaStafH',
        displayName: 'MMBT',
        shortName: 'MMBT',
        precision: 4,
        verified: true
    });

    var MPST = new Currency({
        id: '44n9LfHecPgovJAZtgdqLg9bT4kzRSF2LgGGSnsyojRn',
        displayName: 'MPST',
        shortName: 'MPST',
        precision: 8,
        verified: true
    });

    var MFS = new Currency({
        id: 'A29o9EnYC9rjPnCw4ujrgTze7E3hLstiLeiSeoUbanfv',
        displayName: 'My Fair Share',
        shortName: 'MFS',
        precision: 8,
        verified: true
    });

    var MCS = new Currency({
        id: '4RndW3NAfxHV1xdCn67t4P6prU9B8SyxNTpYFAocmttM',
        displayName: 'MyCryptoSpot',
        shortName: 'MCS',
        precision: 8,
        verified: true
    });

    var NICNAC = new Currency({
        id: 'ENpaU88woC6Q1pbheURcA5TMX7ykhC5zFPqzdVfhP1BC',
        displayName: 'NicNacToken',
        shortName: 'NICNAC',
        precision: 3,
        verified: true
    });

    var NUTS = new Currency({
        id: '67dY6uMTpg9Ks7Abn2muwTyY24qjrhjviKxMfgURQhos',
        displayName: 'Nutshells',
        shortName: 'NUTS',
        precision: 6,
        verified: true
    });

    var OCTANOX = new Currency({
        id: 'DxE8xbjHT7rXyRd2DMz5TnNNNC91Kz1SZ9k4dpH6X4JP',
        displayName: 'Octanox',
        shortName: 'OTX',
        precision: 8,
        verified: true
    });

    var P2P = new Currency({
        id: '6Z2EYvNU447o96Zevei4Zb5rNntENs2br2B5kQ5HXkiq',
        displayName: 'P2P Coin',
        shortName: 'P2P',
        precision: 8,
        verified: true
    });

    var preNEX = new Currency({
        id: 'FBKxJx6Ho6z1bABvGJo1J1sbCrr4Cs3iUTGsxy3suG4F',
        displayName: 'preNEX',
        shortName: 'preNEX',
        precision: 0,
        verified: true
    });

    var preVITO = new Currency({
        id: '6LcUbnDY585ndN8XbHmnbwF8P8BZsoPqzvEyWbjdsrqQ',
        displayName: 'preVITO',
        shortName: 'preVITO',
        precision: 3,
        verified: true
    });

    var PRIMO = new Currency({
        id: '4EmxnV7DhizwpKh5J13Waxovth95uSjknokNFxNAzAaS',
        displayName: 'Primo Coin',
        shortName: 'PRIMO',
        precision: 8,
        verified: true
    });

    var PYTI = new Currency({
        id: 'F6ppo1zRQnMW6VcYRj2LiEqjL6ahvdYU4zNQXWxstLbg',
        displayName: 'Priveleged YTI',
        shortName: 'PYTI',
        precision: 2,
        verified: true
    });

    var PUMP = new Currency({
        id: '5fMUzjhtVkwxyUyDPzSZuCz2HtpesaaTNMTRsFzZvkP',
        displayName: 'Pumpcoin',
        shortName: 'PUMP',
        precision: 8,
        verified: true
    });

    var QUASA = new Currency({
        id: '33GpTrJ72YiDA21nEtssN8jKYf5jwbv8GFH22y37AVjD',
        displayName: 'QuasaCoin',
        shortName: 'QUASA',
        precision: 8,
        verified: true
    });

    var REDFISH = new Currency({
        id: '5sU8dF7DyN7dKN4NiFTtVC5shqthSgTEuvKUu2iusyS2',
        displayName: 'Redfishcoin',
        shortName: 'REDFISH',
        precision: 8,
        verified: true
    });

    var RMOB = new Currency({
        id: 'BmcArNN9VnKAp3HbvpKaoE3utwEXqvP1UjunS9DVKdGS',
        displayName: 'RewardMob',
        shortName: 'RMOB',
        precision: 8,
        verified: true
    });

    var RXSC = new Currency({
        id: 'SGBHnkG1Z8VbEtaCF5gpNihg1SRFky6CzrwmyL8GJnj',
        displayName: 'RxSmartCoffee',
        shortName: 'RXSC',
        precision: 8,
        verified: true
    });

    var SEBEUM = new Currency({
        id: '73XxLgHdzDfus6nRuwpo3dceCRMNiU5VwkiUK1AAfaQk',
        displayName: 'Sebeum',
        shortName: 'SEBEUM',
        precision: 5,
        verified: true
    });

    var SGCN = new Currency({
        id: 'AYMwsNAa4pdg1raJnGvibdLkAhqXQTrXo2SQfecAzfg1',
        displayName: 'SGelderCoin',
        shortName: 'SGCN',
        precision: 8,
        verified: true
    });

    var SHEEP = new Currency({
        id: 'mjkFnVZBdS1VB5MdWjgEFYHyTaoVGuepypLpTEGQdEp',
        displayName: 'Sheepbit',
        shortName: 'SHEEP',
        precision: 8,
        verified: true
    });

    var SGT = new Currency({
        id: 'BPSBJtgWQvx6QqNz9WHEZVhJAmTvGPArQ1Y5nFVkTPAR',
        displayName: 'Snuggoo (SGT)',
        shortName: 'SGT',
        precision: 2,
        verified: true
    });

    var SQUASH = new Currency({
        id: '4Cxj1FfwKWMwfZZ34QxyZtRfUq4jHSmX9pwXafzBzmdC',
        displayName: 'SquashCoin',
        shortName: 'SQUASH',
        precision: 2,
        verified: true
    });

    var SRE = new Currency({
        id: 'BotFPyCivCDaoQHSD3myBw7GAxsZdiRS76G1WdFVuSXC',
        displayName: 'SRE_Token',
        shortName: 'SRE',
        precision: 8,
        verified: true
    });

    var STYLO = new Currency({
        id: '5VRTinDkxBi4oYBSWjkijyZtacH3QVa8Q8qPodhvczv6',
        displayName: 'stylocoin',
        shortName: 'STYLO',
        precision: 4,
        verified: true
    });

    var SXAS = new Currency({
        id: 'EjR1ThR2MBgukq4Z5zhdXzcct2Vzvq1QgnkMjcFRhXio',
        displayName: 'SXAS',
        shortName: 'SXAS',
        precision: 6,
        verified: true
    });

    var TENEBRIS = new Currency({
        id: 'EJs2V3hd6FXGDYH7HKFDhVcgtCmDa31zRygV1KwF5PHS',
        displayName: 'Tenebris',
        shortName: 'TENEBRIS',
        precision: 8,
        verified: true
    });

    var TEXCOIN = new Currency({
        id: '68XWWEmAUoLHXGFy6n8nb6M5c2WrSrekiWSPx8VT7e1e',
        displayName: 'TEXCOIN',
        shortName: 'TEXCOIN',
        precision: 3,
        verified: true
    });

    var Tidals = new Currency({
        id: 'AAUgxEx61UK5Y9MiEYMsdnCqVhGxBcTJEGTMHJeybuBC',
        displayName: 'Tidal Waves',
        shortName: 'Tidals',
        precision: 8,
        verified: true
    });

    var TFT = new Currency({
        id: 'B1u2TBpTYHWCuMuKLnbQfLvdLJ3zjgPiy3iMS2TSYugZ',
        displayName: 'TIMESFARMTOKEN',
        shortName: 'TFT',
        precision: 6,
        verified: true
    });

    var LOYAL = new Currency({
        id: '3YBdrSJjkAfQiFVefJ6vSRLrRtsWfSgjFd2W53oCWpZM',
        displayName: 'tokenloyalty.io',
        shortName: 'LOYAL',
        precision: 8,
        verified: true
    });

    var TOPS = new Currency({
        id: '865pJ6TrYL39oMHoKtxBCNjdYsyMtaymz3doFfbEv5hh',
        displayName: 'TOPS',
        shortName: 'TOPS',
        precision: 5,
        verified: true
    });

    var TRGL = new Currency({
        id: '5i65cqtC1s34YmyUUxFM4ps5DLQHtLvZwCfaPb6QhXdh',
        displayName: 'TRGL',
        shortName: 'TRGL',
        precision: 0,
        verified: true
    });

    var TRUZTAR = new Currency({
        id: '7EHF5yybMR9kkB5Ntz3pqYTQY3zK6a5rHy4gjDYVbWpS',
        displayName: 'Truztar',
        shortName: 'TRUZTAR',
        precision: 8,
        verified: true
    });

    var TWENTYONE = new Currency({
        id: 'Dbd7nKCm9RRq6Vjh9VLumXeEKPZfM4dgox19q7jjHx5L',
        displayName: 'Twenty-One',
        shortName: 'TWENTYONE',
        precision: 8,
        verified: true
    });

    var UOOMAG = new Currency({
        id: 'DgwLgKXfC3G7SKbSoz82ZQVGQNLHqqfEovtdv7sjHGKu',
        displayName: 'UOOMAG',
        shortName: 'UOOMAG',
        precision: 8,
        verified: true
    });

    var VTN = new Currency({
        id: '32gwVYerx37pxuNG6eaiFRdya5ETpH8imNsf31VT5WqH',
        displayName: 'VOLTROON',
        shortName: 'VTN',
        precision: 8,
        verified: true
    });

    var WTC = new Currency({
        id: '7VDRFwm2HbaJCk3U4HQDhLGdSCxZwPe3cHefVXy7ejYe',
        displayName: 'WorldTurtleCoin',
        shortName: 'WTC',
        precision: 8,
        verified: true
    });

    var XVCA = new Currency({
        id: '78op8zPXC1Uf5541a7Pm1SmqrutAC9tsNxbrMTLscoHy',
        displayName: 'XVCA',
        shortName: 'XVCA',
        precision: 3,
        verified: true
    });

    var ANRYZE = new Currency({
        id: 'HXdFUiw5yLLWhkorsRy1E5GttG2QZfzEYAVgEgjBNh8t',
        displayName: 'ANRYZE',
        shortName: 'ANRYZE',
        precision: 8,
        verified: true
    });

    var KLX = new Currency({
        id: '7gMmyXjd4uZwaAFcfrfXQR4fAhDi8waXANb8zjqhRSfq',
        displayName: 'Kylix',
        shortName: 'KLX',
        precision: 2,
        verified: true
    });

    var POST = new Currency({
        id: 'DQUrzGsXp84Z4aPXLEkhgApf8TpCQqtoY87gdwUTurL7',
        displayName: 'NEWS',
        shortName: 'POST',
        precision: 8,
        verified: true
    });

    var TRY = new Currency({
        id: '2mX5DzVKWrAJw8iwdJnV2qtoeVG9h5nTDpTqC1wb1WEN',
        displayName: 'TRY',
        shortName: 'TRY',
        precision: 2,
        verified: true
    });

    var JDC = new Currency({
        id: 'Chs34HQrj37VbWHr8NDZiRZEkyEGBiPowSF4RjrRBCHn',
        displayName: 'JustDatingCoin',
        shortName: 'JDC',
        precision: 8,
        verified: true
    });

    var Blue = new Currency({
        id: 'HkhKVMzWNE7DJ5fZJpwBMs4FMxFwZFFh9UT5GXAVdZvE',
        displayName: 'BlueToken',
        shortName: 'Blue',
        precision: 0,
        verified: true
    });

    var AKCHE = new Currency({
        id: '3ihiQ1TJhe7fBrMc8o9EY8tQNU6phkmp8ZEyvVe4Jfhk',
        displayName: 'AKCHE',
        shortName: 'AKCHE',
        precision: 4,
        verified: true
    });

    var TDX = new Currency({
        id: '3QvxP6YFBKpWJSMAfYtL8Niv8KmmKsnpb9uQwQpg8QN2',
        displayName: 'Tidex',
        shortName: 'TDX',
        precision: 2,
        verified: true
    });

    var InPay = new Currency({
        id: '9pPVf3gcLH3NQA2aYVRcTV2N2i32qBzA5cEMWYqBYfMi',
        displayName: 'InPay',
        shortName: 'InPay',
        precision: 8,
        verified: true
    });

    var LIQUID = new Currency({
        id: '7FzrHF1pueRFrPEupz6oiVGTUZqe8epvC7ggWUx8n1bd',
        displayName: 'Liquid',
        shortName: 'LIQUID',
        precision: 8,
        verified: true
    });

    var TN = new Currency({
        id: 'HxQSdHu1X4ZVXmJs232M6KfZi78FseeWaEXJczY6UxJ3',
        displayName: 'TurtleNode',
        shortName: 'TN',
        precision: 2,
        verified: true
    });

    var ENAN = new Currency({
        id: '53sxSVvj3PJkZhZKz6gLc5coXxAyC7zbgo5RtXfqRsym',
        displayName: 'eco-NAN',
        shortName: 'ENAN',
        precision: 8,
        verified: true
    });

    var ContestCoin = new Currency({
        id: '2ULyqYTJfrDknc2m5iPPkrvpHtRiB57nHag4RCSwZWQS',
        displayName: 'ContestCoin',
        shortName: 'ContestCoin',
        precision: 0,
        verified: true
    });

    var SMQ = new Currency({
        id: 'CBik4JEmsoPZKKATnShULYj2ebUao5aada9N1XGznEET',
        displayName: 'Simdaq Token',
        shortName: 'SMQ',
        precision: 8,
        verified: true
    });

    var DASH = new Currency({
        id: 'B3uGHFRpSUuGEDWjqB9LWWxafQj8VTvpMucEyoxzws5H',
        displayName: 'Dash token',
        shortName: 'DASH',
        precision: 8,
        verified: true
    });

    function isCached(assetId) {
        return currencyCache.hasOwnProperty(assetId);
    }

    function invalidateCache() {
        currencyCache = {};

        currencyCache[WAVES.id] = WAVES;
        currencyCache[BTC.id] = BTC;
        currencyCache[BCH.id] = BCH;
        currencyCache[ETH.id] = ETH;
        currencyCache[LTC.id] = LTC;
        currencyCache[ZEC.id] = ZEC;
        currencyCache[USD.id] = USD;
        currencyCache[EUR.id] = EUR;
        currencyCache[CNY.id] = CNY;
        currencyCache[WCT.id] = WCT;
        currencyCache[MRT.id] = MRT;
        currencyCache[WGO.id] = WGO;
        currencyCache[INCNT.id] = INCNT;
        currencyCache[RBX.id] = RBX;
        currencyCache[MER.id] = MER;
        currencyCache[BAt.id] = BAt;
        currencyCache[UPC.id] = UPC;
        currencyCache[KLN.id] = KLN;
        currencyCache[TKS.id] = TKS;
        currencyCache[WPN.id] = WPN;
        currencyCache[EFYT.id] = EFYT;
        currencyCache[MGO.id] = MGO;
        currencyCache[ETT.id] = ETT;
        currencyCache[ZRC.id] = ZRC;
        currencyCache[PBKX.id] = PBKX;
        currencyCache[PING.id] = PING;
        currencyCache[STAR.id] = STAR;
        currencyCache[BEAR.id] = BEAR;
        currencyCache[DAR.id] = DAR;
        currencyCache[GLIPP.id] = GLIPP;
        currencyCache[mTNT.id] = mTNT;
        currencyCache[BKT.id] = BKT;
        currencyCache[WGR.id] = WGR;
        currencyCache[PBT.id] = PBT;
        currencyCache[PPIO.id] = PPIO;
        currencyCache[STA.id] = STA;
        currencyCache[CORE.id] = CORE;
        currencyCache[KSS.id] = KSS;
        currencyCache[WFN.id] = WFN;
        currencyCache[GRPH.id] = GRPH;
        currencyCache[ESC.id] = ESC;
        currencyCache[AGRO.id] = AGRO;
        currencyCache[KING.id] = KING;
        currencyCache[ARNA.id] = ARNA;
        currencyCache[WNET.id] = WNET;
        currencyCache[PBK.id] = PBK;
        currencyCache[TOM.id] = TOM;
        currencyCache[ViC.id] = ViC;
        currencyCache[EQ.id] = EQ;
        currencyCache[SHDW.id] = SHDW;
        currencyCache[GIN.id] = GIN;
        currencyCache[NEWS.id] = NEWS;
        currencyCache[COXST.id] = COXST;
        currencyCache[SMR.id] = SMR;
        currencyCache[RDT.id] = RDT;
        currencyCache[IRA.id] = IRA;
        currencyCache[_2B4T.id] = _2B4T;
        currencyCache[MBX.id] = MBX;
        currencyCache[KNOWS.id] = KNOWS;
        currencyCache[MBI.id] = MBI;
        currencyCache[COF.id] = COF;
        currencyCache[CHILL.id] = CHILL;
        currencyCache[KUN.id] = KUN;
        currencyCache[CEIT.id] = CEIT;
        currencyCache[SGIT.id] = SGIT;
        currencyCache[AHT.id] = AHT;
        currencyCache[HALAL.id] = HALAL;
        currencyCache[DIMO.id] = DIMO;
        currencyCache[WIN.id] = WIN;
        currencyCache[YTB.id] = YTB;
        currencyCache[GFL.id] = GFL;
        currencyCache[DAT.id] = DAT;
        currencyCache[VK.id] = VK;
        currencyCache[UWT.id] = UWT;
        currencyCache[AP_0.id] = AP_0;
        currencyCache[AP_1.id] = AP_1;
        currencyCache[AP_2.id] = AP_2;
        currencyCache[OCL.id] = OCL;
        currencyCache[OCC.id] = OCC;
        currencyCache[SMART.id] = SMART;
        currencyCache[DCN.id] = DCN;
        currencyCache[RSC.id] = RSC;
        currencyCache[LIKE.id] = LIKE;
        currencyCache[FUPOOF.id] = FUPOOF;
        currencyCache[ANY.id] = ANY;
        currencyCache[BRW.id] = BRW;
        currencyCache[CNX.id] = CNX;
        currencyCache[DARF.id] = DARF;
        currencyCache[WNT.id] = WNT;
        currencyCache[CWV.id] = CWV;
        currencyCache[WCASH.id] = WCASH;
        currencyCache[LIFE.id] = LIFE;
        currencyCache[RDCR.id] = RDCR;
        currencyCache[THNX.id] = THNX;
        currencyCache[IKV.id] = IKV;
        currencyCache[WDESK.id] = WDESK;
        currencyCache[SUR.id] = SUR;
        currencyCache[SIBERIA.id] = SIBERIA;
        currencyCache[MODO.id] = MODO;
        currencyCache[GIVE.id] = GIVE;
        currencyCache[SOL.id] = SOL;
        currencyCache[EOT.id] = EOT;
        currencyCache[FIX.id] = FIX;
        currencyCache[KKO.id] = KKO;
        currencyCache[JNT.id] = JNT;
        currencyCache[CGT.id] = CGT;
        currencyCache[AFFT.id] = AFFT;
        currencyCache[MFL.id] = MFL;
        currencyCache[TURTL.id] = TURTL;
        currencyCache[PropX.id] = PropX;
        currencyCache[ECT.id] = ECT;
        currencyCache[STT.id] = STT;
        currencyCache[SCLRI.id] = SCLRI;
        currencyCache[Knish.id] = Knish;
        currencyCache[WPC.id] = WPC;
        currencyCache[cryptoSterling.id] = cryptoSterling;
        currencyCache[NGN.id] = NGN;
        currencyCache[ALTOCAR.id] = ALTOCAR;
        currencyCache[ANAT.id] = ANAT;
        currencyCache[ATKN.id] = ATKN;
        currencyCache[ATOM.id] = ATOM;
        currencyCache[BAR.id] = BAR;
        currencyCache[BCF.id] = BCF;
        currencyCache[BET.id] = BET;
        currencyCache[BIRTAL.id] = BIRTAL;
        currencyCache[BITCHEKE.id] = BITCHEKE;
        currencyCache[BITD.id] = BITD;
        currencyCache[BKC.id] = BKC;
        currencyCache[CROW.id] = CROW;
        currencyCache[CBT.id] = CBT;
        currencyCache[EDEN.id] = EDEN;
        currencyCache[EQUA.id] = EQUA;
        currencyCache[EQUILD.id] = EQUILD;
        currencyCache[ETERP.id] = ETERP;
        currencyCache[FENIX.id] = FENIX;
        currencyCache[FTB.id] = FTB;
        currencyCache[FLEX.id] = FLEX;
        currencyCache[FNX.id] = FNX;
        currencyCache[GBC.id] = GBC;
        currencyCache[Grant.id] = Grant;
        currencyCache[GrantsBounty.id] = GrantsBounty;
        currencyCache[HEART.id] = HEART;
        currencyCache[HOME.id] = HOME;
        currencyCache[HTC.id] = HTC;
        currencyCache[IMMO.id] = IMMO;
        currencyCache[JNET.id] = JNET;
        currencyCache[KRIP.id] = KRIP;
        currencyCache[LLA.id] = LLA;
        currencyCache[limburg.id] = limburg;
        currencyCache[LIVEBIT.id] = LIVEBIT;
        currencyCache[MED.id] = MED;
        currencyCache[MNG.id] = MNG;
        currencyCache[MMBT.id] = MMBT;
        currencyCache[MPST.id] = MPST;
        currencyCache[MFS.id] = MFS;
        currencyCache[MCS.id] = MCS;
        currencyCache[NICNAC.id] = NICNAC;
        currencyCache[NUTS.id] = NUTS;
        currencyCache[OCTANOX.id] = OCTANOX;
        currencyCache[P2P.id] = P2P;
        currencyCache[preNEX.id] = preNEX;
        currencyCache[preVITO.id] = preVITO;
        currencyCache[PRIMO.id] = PRIMO;
        currencyCache[PYTI.id] = PYTI;
        currencyCache[PUMP.id] = PUMP;
        currencyCache[QUASA.id] = QUASA;
        currencyCache[REDFISH.id] = REDFISH;
        currencyCache[RMOB.id] = RMOB;
        currencyCache[RXSC.id] = RXSC;
        currencyCache[SEBEUM.id] = SEBEUM;
        currencyCache[SGCN.id] = SGCN;
        currencyCache[SHEEP.id] = SHEEP;
        currencyCache[SGT.id] = SGT;
        currencyCache[SQUASH.id] = SQUASH;
        currencyCache[SRE.id] = SRE;
        currencyCache[STYLO.id] = STYLO;
        currencyCache[SXAS.id] = SXAS;
        currencyCache[TENEBRIS.id] = TENEBRIS;
        currencyCache[TEXCOIN.id] = TEXCOIN;
        currencyCache[Tidals.id] = Tidals;
        currencyCache[TFT.id] = TFT;
        currencyCache[LOYAL.id] = LOYAL;
        currencyCache[TOPS.id] = TOPS;
        currencyCache[TRGL.id] = TRGL;
        currencyCache[TRUZTAR.id] = TRUZTAR;
        currencyCache[TWENTYONE.id] = TWENTYONE;
        currencyCache[UOOMAG.id] = UOOMAG;
        currencyCache[VTN.id] = VTN;
        currencyCache[WTC.id] = WTC;
        currencyCache[XVCA.id] = XVCA;
        currencyCache[ANRYZE.id] = ANRYZE;
        currencyCache[KLX.id] = KLX;
        currencyCache[POST.id] = POST;
        currencyCache[TRY.id] = TRY;
        currencyCache[JDC.id] = JDC;
        currencyCache[Blue.id] = Blue;
        currencyCache[AKCHE.id] = AKCHE;
        currencyCache[TDX.id] = TDX;
        currencyCache[InPay.id] = InPay;
        currencyCache[LIQUID.id] = LIQUID;
        currencyCache[TN.id] = TN;
        currencyCache[ENAN.id] = ENAN;
        currencyCache[ContestCoin.id] = ContestCoin;
        currencyCache[SMQ.id] = SMQ;
    }

    invalidateCache();

    return {
        create: function (data) {
            // if currency data.id is not set - it's a temporary instance
            if (!_.has(data, 'id')) {
                return new Currency(data);
            }

            if (!currencyCache[data.id]) {
                currencyCache[data.id] = new Currency(data);
            }

            return currencyCache[data.id];
        },
        invalidateCache: invalidateCache,
        isCached: isCached,
        WAVES: WAVES,
        BTC: BTC,
        BCH: BCH,
        ETH: ETH,
        LTC: LTC,
        ZEC: ZEC,
        USD: USD,
        EUR: EUR,
        CNY: CNY,
        WCT: WCT,
        MRT: MRT,
        WGO: WGO,
        INCNT: INCNT,
        RBX: RBX,
        MER: MER,
        BAt: BAt,
        UPC: UPC,
        KLN: KLN,
        TKS: TKS,
        WPN: WPN,
        EFYT: EFYT,
        MGO: MGO,
        ETT: ETT,
        ZRC: ZRC,
        PBKX: PBKX,
        PING: PING,
        STAR: STAR,
        BEAR: BEAR,
        DAR: DAR,
        GLIPP: GLIPP,
        mTNT: mTNT,
        BKT: BKT,
        WGR: WGR,
        PBT: PBT,
        PPIO: PPIO,
        STA: STA,
        CORE: CORE,
        KSS: KSS,
        WFN: WFN,
        GRPH: GRPH,
        ESC: ESC,
        AGRO: AGRO,
        KING: KING,
        ARNA: ARNA,
        WNET: WNET,
        PBK: PBK,
        TOM: TOM,
        ViC: ViC,
        EQ: EQ,
        SHDW: SHDW,
        GIN: GIN,
        NEWS: NEWS,
        COXST: COXST,
        SMR: SMR,
        RDT: RDT,
        IRA: IRA,
        _2B4T: _2B4T,
        MBX: MBX,
        KNOWS: KNOWS,
        MBI: MBI,
        COF: COF,
        CHILL: CHILL,
        KUN: KUN,
        CEIT: CEIT,
        SGIT: SGIT,
        AHT: AHT,
        HALAL: HALAL,
        DIMO: DIMO,
        WIN: WIN,
        YTB: YTB,
        GFL: GFL,
        DAT: DAT,
        VK: VK,
        UWT: UWT,
        AP_0: AP_0,
        AP_1: AP_1,
        AP_2: AP_2,
        OCL: OCL,
        OCC: OCC,
        SMART: SMART,
        DCN: DCN,
        RSC: RSC,
        LIKE: LIKE,
        FUPOOF: FUPOOF,
        ANY: ANY,
        BRW: BRW,
        CNX: CNX,
        DARF: DARF,
        WNT: WNT,
        CWV: CWV,
        WCASH: WCASH,
        LIFE: LIFE,
        RDCR: RDCR,
        THNX: THNX,
        IKV: IKV,
        WDESK: WDESK,
        SUR: SUR,
        SIBERIA: SIBERIA,
        MODO: MODO,
        GIVE: GIVE,
        SOL: SOL,
        EOT: EOT,
        FIX: FIX,
        KKO: KKO,
        JNT: JNT,
        CGT: CGT,
        AFFT: AFFT,
        MFL: MFL,
        TURTL: TURTL,
        PropX: PropX,
        ECT: ECT,
        STT: STT,
        SCLRI: SCLRI,
        Knish: Knish,
        WPC: WPC,
        cryptoSterling: cryptoSterling,
        NGN: NGN,
        ALTOCAR: ALTOCAR,
        ANAT: ANAT,
        ATKN: ATKN,
        ATOM: ATOM,
        BAR: BAR,
        BCF: BCF,
        BET: BET,
        BIRTAL: BIRTAL,
        BITCHEKE: BITCHEKE,
        BITD: BITD,
        BKC: BKC,
        CROW: CROW,
        CBT: CBT,
        EDEN: EDEN,
        EQUA: EQUA,
        EQUILD: EQUILD,
        ETERP: ETERP,
        FENIX: FENIX,
        FTB: FTB,
        FLEX: FLEX,
        FNX: FNX,
        GBC: GBC,
        Grant: Grant,
        GrantsBounty: GrantsBounty,
        HEART: HEART,
        HOME: HOME,
        HTC: HTC,
        IMMO: IMMO,
        JNET: JNET,
        KRIP: KRIP,
        LLA: LLA,
        limburg: limburg,
        LIVEBIT: LIVEBIT,
        MED: MED,
        MNG: MNG,
        MMBT: MMBT,
        MPST: MPST,
        MFS: MFS,
        MCS: MCS,
        NICNAC: NICNAC,
        NUTS: NUTS,
        OCTANOX: OCTANOX,
        P2P: P2P,
        preNEX: preNEX,
        preVITO: preVITO,
        PRIMO: PRIMO,
        PYTI: PYTI,
        PUMP: PUMP,
        QUASA: QUASA,
        REDFISH: REDFISH,
        RMOB: RMOB,
        RXSC: RXSC,
        SEBEUM: SEBEUM,
        SGCN: SGCN,
        SHEEP: SHEEP,
        SGT: SGT,
        SQUASH: SQUASH,
        SRE: SRE,
        STYLO: STYLO,
        SXAS: SXAS,
        TENEBRIS: TENEBRIS,
        TEXCOIN: TEXCOIN,
        Tidals: Tidals,
        TFT: TFT,
        LOYAL: LOYAL,
        TOPS: TOPS,
        TRGL: TRGL,
        TRUZTAR: TRUZTAR,
        TWENTYONE: TWENTYONE,
        UOOMAG: UOOMAG,
        VTN: VTN,
        WTC: WTC,
        XVCA: XVCA,
        ANRYZE: ANRYZE,
        KLX: KLX,
        POST: POST,
        TRY: TRY,
        JDC: JDC,
        Blue: Blue,
        AKCHE: AKCHE,
        TDX: TDX,
        InPay: InPay,
        LIQUID: LIQUID,
        TN: TN,
        ENAN: ENAN,
        ContestCoin: ContestCoin,
        SMQ: SMQ,
        DASH: DASH
    };
})();

var Money = function(amount, currency) {
    var DECIMAL_SEPARATOR = '.';
    var THOUSANDS_SEPARATOR = ',';

    if (amount === undefined)
        throw Error('Amount is required');

    if (currency === undefined)
        throw Error('Currency is required');

    this.amount = new Decimal(amount)
        .toDecimalPlaces(currency.precision, Decimal.ROUND_FLOOR);
    this.currency = currency;

    var integerPart = function (value) {
        return value.trunc();
    };

    var fractionPart = function (value) {
        return value.minus(integerPart(value));
    };

    var format = function (value) {
        return value.toFixed(currency.precision, currency.roundingMode);
    };

    var validateCurrency = function (expected, actual) {
        if (expected.id !== actual.id)
            throw new Error('Currencies must be the same for operands. Expected: ' +
                expected.displayName + '; Actual: ' + actual.displayName);
    };

    var fromTokensToCoins = function (valueInTokens, currencyPrecision) {
        return valueInTokens.mul(Math.pow(10, currencyPrecision)).trunc();
    };

    var fromCoinsToTokens = function (valueInCoins, currencyPrecision) {
        return valueInCoins.trunc().div(Math.pow(10, currencyPrecision));
    };

    // in 2016 Safari doesn't support toLocaleString()
    // that's why we need this method
    var formatWithThousandsSeparator = function (formattedAmount) {
        var parts = formattedAmount.split(DECIMAL_SEPARATOR);
        parts[0] = parts[0].replace(/\B(?=(\d{3})+(?!\d))/g, THOUSANDS_SEPARATOR);

        return parts.join(DECIMAL_SEPARATOR);
    };

    this.formatAmount = function (stripZeroes, useThousandsSeparator) {
        var result = stripZeroes ?
            this.toTokens().toFixed(this.amount.decimalPlaces()) :
            format(this.amount);

        return useThousandsSeparator ? formatWithThousandsSeparator(result) : result;
    };

    this.formatIntegerPart = function () {
        return integerPart(this.amount).toFixed(0);
    };

    this.formatFractionPart = function () {
        var valueWithLeadingZero = format(fractionPart(this.amount));

        return valueWithLeadingZero.slice(1); // stripping the leading zero
    };

    this.toTokens = function () {
        var result = fromCoinsToTokens(fromTokensToCoins(this.amount, this.currency.precision),
            this.currency.precision);

        return result.toNumber();
    };

    this.toCoins = function () {
        return fromTokensToCoins(this.amount, this.currency.precision).toNumber();
    };

    this.plus = function (money) {
        validateCurrency(this.currency, money.currency);

        return new Money(this.amount.plus(money.amount), this.currency);
    };

    this.minus = function (money) {
        validateCurrency(this.currency, money.currency);

        return new Money(this.amount.minus(money.amount), this.currency);
    };

    this.greaterThan = function (other) {
        validateCurrency(this.currency, other.currency);

        return this.amount.greaterThan(other.amount);
    };

    this.greaterThanOrEqualTo = function (other) {
        validateCurrency(this.currency, other.currency);

        return this.amount.greaterThanOrEqualTo(other.amount);
    };

    this.lessThan = function (other) {
        validateCurrency(this.currency, other.currency);

        return this.amount.lessThan(other.amount);
    };

    this.lessThanOrEqualTo = function (other) {
        validateCurrency(this.currency, other.currency);

        return this.amount.lessThanOrEqualTo(other.amount);
    };

    this.multiply = function (multiplier) {
        if (!_.isNumber(multiplier))
            throw new Error('Number is expected');

        if (isNaN(multiplier))
            throw new Error('Multiplication by NaN is not supported');

        return new Money(this.amount.mul(multiplier), this.currency);
    };

    this.toString = function () {
        return this.formatAmount(false, true) + ' ' + this.currency.toString();
    };

    return this;
};

Money.fromTokens = function (amount, currency) {
    return new Money(amount, currency);
};

Money.fromCoins = function (amount, currency) {
    currency = currency || {};
    if (currency.precision === undefined)
        throw new Error('A valid currency must be provided');

    amount = new Decimal(amount);
    amount = amount.div(Math.pow(10, currency.precision));

    return new Money(amount, currency);
};

// set up decimal to format 0.00000001 as is instead of 1e-8
Decimal.config({toExpNeg: -(Currency.WAVES.precision + 1)});


(function() {
    'use strict';

    angular.module('waves.core', [
        'waves.core.services',
        'waves.core.constants',
        'waves.core.filter',
        'waves.core.directives'
    ]);
})();

(function() {
    'use strict';

    angular
        .module('waves.core.constants', [])
        .constant('constants.network', {
            NETWORK_NAME: 'devel', // 'devnet', 'testnet', 'mainnet'
            ADDRESS_VERSION: 1,
            NETWORK_CODE: 'T',
            INITIAL_NONCE: 0
        });

    angular
        .module('waves.core.constants')
        .constant('constants.address', {
            RAW_ADDRESS_LENGTH : 35,
            ADDRESS_PREFIX: '1W',
            MAINNET_ADDRESS_REGEXP: /^[a-zA-Z0-9]{35}$/
        });

    angular
        .module('waves.core.constants')
        .constant('constants.features', {
            ALIAS_VERSION: 2
        });

    angular
        .module('waves.core.constants')
        .constant('constants.ui', {
            MINIMUM_PAYMENT_AMOUNT : 1e-8,
            MINIMUM_TRANSACTION_FEE : 0.001,
            AMOUNT_DECIMAL_PLACES : 8,
            JAVA_MAX_LONG: 9223372036854775807,
            MAXIMUM_ATTACHMENT_BYTE_SIZE: 140
        });

    angular
        .module('waves.core.constants')
        .constant('constants.transactions', {
            PAYMENT_TRANSACTION_TYPE : 2,
            ASSET_ISSUE_TRANSACTION_TYPE: 3,
            ASSET_TRANSFER_TRANSACTION_TYPE: 4,
            ASSET_REISSUE_TRANSACTION_TYPE: 5,
            ASSET_BURN_TRANSACTION_TYPE: 6,
            EXCHANGE_TRANSACTION_TYPE: 7,
            START_LEASING_TRANSACTION_TYPE: 8,
            CANCEL_LEASING_TRANSACTION_TYPE: 9,
            CREATE_ALIAS_TRANSACTION_TYPE: 10,
            MASS_PAYMENT_TRANSACTION_TYPE: 11
        });
})();

(function () {
    'use strict';
    angular.module('waves.core.directives', []);
})();

(function() {
    'use strict';

    angular.module('waves.core.services', ['waves.core', 'restangular'])
        .config(function () {
            if (!String.prototype.startsWith) {
                Object.defineProperty(String.prototype, 'startsWith', {
                    enumerable: false,
                    configurable: false,
                    writable: false,
                    value: function(searchString, position) {
                        position = position || 0;
                        return this.lastIndexOf(searchString, position) === position;
                    }
                });
            }

            if (typeof String.prototype.endsWith !== 'function') {
                String.prototype.endsWith = function(suffix) {
                    return this.indexOf(suffix, this.length - suffix.length) !== -1;
                };
            }
        });
})();

/**
 * @author Björn Wenzel
 */
(function () {
    'use strict';
    angular.module('waves.core.filter', []);
})();

//https://github.com/bitcoin/bips/blob/master/bip-0039/bip-0039-wordlists.md
(function() {
    'use strict';

    angular
        .module('waves.core.services')
        .constant('wordList', [
            'abandon', 'ability', 'able', 'about', 'above', 'absent', 'absorb', 'abstract', 'absurd', 'abuse', 'access',
            'accident', 'account', 'accuse', 'achieve', 'acid', 'acoustic', 'acquire', 'across', 'act', 'action',
            'actor', 'actress', 'actual', 'adapt', 'add', 'addict', 'address', 'adjust', 'admit', 'adult', 'advance',
            'advice', 'aerobic', 'affair', 'afford', 'afraid', 'again', 'age', 'agent', 'agree', 'ahead', 'aim', 'air',
            'airport', 'aisle', 'alarm', 'album', 'alcohol', 'alert', 'alien', 'all', 'alley', 'allow', 'almost',
            'alone', 'alpha', 'already', 'also', 'alter', 'always', 'amateur', 'amazing', 'among', 'amount', 'amused',
            'analyst', 'anchor', 'ancient', 'anger', 'angle', 'angry', 'animal', 'ankle', 'announce', 'annual',
            'another', 'answer', 'antenna', 'antique', 'anxiety', 'any', 'apart', 'apology', 'appear', 'apple',
            'approve', 'april', 'arch', 'arctic', 'area', 'arena', 'argue', 'arm', 'armed', 'armor', 'army', 'around',
            'arrange', 'arrest', 'arrive', 'arrow', 'art', 'artefact', 'artist', 'artwork', 'ask', 'aspect', 'assault',
            'asset', 'assist', 'assume', 'asthma', 'athlete', 'atom', 'attack', 'attend', 'attitude', 'attract',
            'auction', 'audit', 'august', 'aunt', 'author', 'auto', 'autumn', 'average', 'avocado', 'avoid', 'awake',
            'aware', 'away', 'awesome', 'awful', 'awkward', 'axis', 'baby', 'bachelor', 'bacon', 'badge', 'bag',
            'balance', 'balcony', 'ball', 'bamboo', 'banana', 'banner', 'bar', 'barely', 'bargain', 'barrel', 'base',
            'basic', 'basket', 'battle', 'beach', 'bean', 'beauty', 'because', 'become', 'beef', 'before', 'begin',
            'behave', 'behind', 'believe', 'below', 'belt', 'bench', 'benefit', 'best', 'betray', 'better', 'between',
            'beyond', 'bicycle', 'bid', 'bike', 'bind', 'biology', 'bird', 'birth', 'bitter', 'black', 'blade', 'blame',
            'blanket', 'blast', 'bleak', 'bless', 'blind', 'blood', 'blossom', 'blouse', 'blue', 'blur', 'blush',
            'board', 'boat', 'body', 'boil', 'bomb', 'bone', 'bonus', 'book', 'boost', 'border', 'boring', 'borrow',
            'boss', 'bottom', 'bounce', 'box', 'boy', 'bracket', 'brain', 'brand', 'brass', 'brave', 'bread', 'breeze',
            'brick', 'bridge', 'brief', 'bright', 'bring', 'brisk', 'broccoli', 'broken', 'bronze', 'broom', 'brother',
            'brown', 'brush', 'bubble', 'buddy', 'budget', 'buffalo', 'build', 'bulb', 'bulk', 'bullet', 'bundle',
            'bunker', 'burden', 'burger', 'burst', 'bus', 'business', 'busy', 'butter', 'buyer', 'buzz', 'cabbage',
            'cabin', 'cable', 'cactus', 'cage', 'cake', 'call', 'calm', 'camera', 'camp', 'can', 'canal', 'cancel',
            'candy', 'cannon', 'canoe', 'canvas', 'canyon', 'capable', 'capital', 'captain', 'car', 'carbon', 'card',
            'cargo', 'carpet', 'carry', 'cart', 'case', 'cash', 'casino', 'castle', 'casual', 'cat', 'catalog', 'catch',
            'category', 'cattle', 'caught', 'cause', 'caution', 'cave', 'ceiling', 'celery', 'cement', 'census',
            'century', 'cereal', 'certain', 'chair', 'chalk', 'champion', 'change', 'chaos', 'chapter', 'charge',
            'chase', 'chat', 'cheap', 'check', 'cheese', 'chef', 'cherry', 'chest', 'chicken', 'chief', 'child',
            'chimney', 'choice', 'choose', 'chronic', 'chuckle', 'chunk', 'churn', 'cigar', 'cinnamon', 'circle',
            'citizen', 'city', 'civil', 'claim', 'clap', 'clarify', 'claw', 'clay', 'clean', 'clerk', 'clever', 'click',
            'client', 'cliff', 'climb', 'clinic', 'clip', 'clock', 'clog', 'close', 'cloth', 'cloud', 'clown', 'club',
            'clump', 'cluster', 'clutch', 'coach', 'coast', 'coconut', 'code', 'coffee', 'coil', 'coin', 'collect',
            'color', 'column', 'combine', 'come', 'comfort', 'comic', 'common', 'company', 'concert', 'conduct',
            'confirm', 'congress', 'connect', 'consider', 'control', 'convince', 'cook', 'cool', 'copper', 'copy',
            'coral', 'core', 'corn', 'correct', 'cost', 'cotton', 'couch', 'country', 'couple', 'course', 'cousin',
            'cover', 'coyote', 'crack', 'cradle', 'craft', 'cram', 'crane', 'crash', 'crater', 'crawl', 'crazy',
            'cream', 'credit', 'creek', 'crew', 'cricket', 'crime', 'crisp', 'critic', 'crop', 'cross', 'crouch',
            'crowd', 'crucial', 'cruel', 'cruise', 'crumble', 'crunch', 'crush', 'cry', 'crystal', 'cube', 'culture',
            'cup', 'cupboard', 'curious', 'current', 'curtain', 'curve', 'cushion', 'custom', 'cute', 'cycle', 'dad',
            'damage', 'damp', 'dance', 'danger', 'daring', 'dash', 'daughter', 'dawn', 'day', 'deal', 'debate',
            'debris', 'decade', 'december', 'decide', 'decline', 'decorate', 'decrease', 'deer', 'defense', 'define',
            'defy', 'degree', 'delay', 'deliver', 'demand', 'demise', 'denial', 'dentist', 'deny', 'depart', 'depend',
            'deposit', 'depth', 'deputy', 'derive', 'describe', 'desert', 'design', 'desk', 'despair', 'destroy',
            'detail', 'detect', 'develop', 'device', 'devote', 'diagram', 'dial', 'diamond', 'diary', 'dice', 'diesel',
            'diet', 'differ', 'digital', 'dignity', 'dilemma', 'dinner', 'dinosaur', 'direct', 'dirt', 'disagree',
            'discover', 'disease', 'dish', 'dismiss', 'disorder', 'display', 'distance', 'divert', 'divide', 'divorce',
            'dizzy', 'doctor', 'document', 'dog', 'doll', 'dolphin', 'domain', 'donate', 'donkey', 'donor', 'door',
            'dose', 'double', 'dove', 'draft', 'dragon', 'drama', 'drastic', 'draw', 'dream', 'dress', 'drift', 'drill',
            'drink', 'drip', 'drive', 'drop', 'drum', 'dry', 'duck', 'dumb', 'dune', 'during', 'dust', 'dutch', 'duty',
            'dwarf', 'dynamic', 'eager', 'eagle', 'early', 'earn', 'earth', 'easily', 'east', 'easy', 'echo', 'ecology',
            'economy', 'edge', 'edit', 'educate', 'effort', 'egg', 'eight', 'either', 'elbow', 'elder', 'electric',
            'elegant', 'element', 'elephant', 'elevator', 'elite', 'else', 'embark', 'embody', 'embrace', 'emerge',
            'emotion', 'employ', 'empower', 'empty', 'enable', 'enact', 'end', 'endless', 'endorse', 'enemy', 'energy',
            'enforce', 'engage', 'engine', 'enhance', 'enjoy', 'enlist', 'enough', 'enrich', 'enroll', 'ensure',
            'enter', 'entire', 'entry', 'envelope', 'episode', 'equal', 'equip', 'era', 'erase', 'erode', 'erosion',
            'error', 'erupt', 'escape', 'essay', 'essence', 'estate', 'eternal', 'ethics', 'evidence', 'evil', 'evoke',
            'evolve', 'exact', 'example', 'excess', 'exchange', 'excite', 'exclude', 'excuse', 'execute', 'exercise',
            'exhaust', 'exhibit', 'exile', 'exist', 'exit', 'exotic', 'expand', 'expect', 'expire', 'explain', 'expose',
            'express', 'extend', 'extra', 'eye', 'eyebrow', 'fabric', 'face', 'faculty', 'fade', 'faint', 'faith',
            'fall', 'false', 'fame', 'family', 'famous', 'fan', 'fancy', 'fantasy', 'farm', 'fashion', 'fat', 'fatal',
            'father', 'fatigue', 'fault', 'favorite', 'feature', 'february', 'federal', 'fee', 'feed', 'feel', 'female',
            'fence', 'festival', 'fetch', 'fever', 'few', 'fiber', 'fiction', 'field', 'figure', 'file', 'film',
            'filter', 'final', 'find', 'fine', 'finger', 'finish', 'fire', 'firm', 'first', 'fiscal', 'fish', 'fit',
            'fitness', 'fix', 'flag', 'flame', 'flash', 'flat', 'flavor', 'flee', 'flight', 'flip', 'float', 'flock',
            'floor', 'flower', 'fluid', 'flush', 'fly', 'foam', 'focus', 'fog', 'foil', 'fold', 'follow', 'food',
            'foot', 'force', 'forest', 'forget', 'fork', 'fortune', 'forum', 'forward', 'fossil', 'foster', 'found',
            'fox', 'fragile', 'frame', 'frequent', 'fresh', 'friend', 'fringe', 'frog', 'front', 'frost', 'frown',
            'frozen', 'fruit', 'fuel', 'fun', 'funny', 'furnace', 'fury', 'future', 'gadget', 'gain', 'galaxy',
            'gallery', 'game', 'gap', 'garage', 'garbage', 'garden', 'garlic', 'garment', 'gas', 'gasp', 'gate',
            'gather', 'gauge', 'gaze', 'general', 'genius', 'genre', 'gentle', 'genuine', 'gesture', 'ghost', 'giant',
            'gift', 'giggle', 'ginger', 'giraffe', 'girl', 'give', 'glad', 'glance', 'glare', 'glass', 'glide',
            'glimpse', 'globe', 'gloom', 'glory', 'glove', 'glow', 'glue', 'goat', 'goddess', 'gold', 'good', 'goose',
            'gorilla', 'gospel', 'gossip', 'govern', 'gown', 'grab', 'grace', 'grain', 'grant', 'grape', 'grass',
            'gravity', 'great', 'green', 'grid', 'grief', 'grit', 'grocery', 'group', 'grow', 'grunt', 'guard', 'guess',
            'guide', 'guilt', 'guitar', 'gun', 'gym', 'habit', 'hair', 'half', 'hammer', 'hamster', 'hand', 'happy',
            'harbor', 'hard', 'harsh', 'harvest', 'hat', 'have', 'hawk', 'hazard', 'head', 'health', 'heart', 'heavy',
            'hedgehog', 'height', 'hello', 'helmet', 'help', 'hen', 'hero', 'hidden', 'high', 'hill', 'hint', 'hip',
            'hire', 'history', 'hobby', 'hockey', 'hold', 'hole', 'holiday', 'hollow', 'home', 'honey', 'hood', 'hope',
            'horn', 'horror', 'horse', 'hospital', 'host', 'hotel', 'hour', 'hover', 'hub', 'huge', 'human', 'humble',
            'humor', 'hundred', 'hungry', 'hunt', 'hurdle', 'hurry', 'hurt', 'husband', 'hybrid', 'ice', 'icon', 'idea',
            'identify', 'idle', 'ignore', 'ill', 'illegal', 'illness', 'image', 'imitate', 'immense', 'immune',
            'impact', 'impose', 'improve', 'impulse', 'inch', 'include', 'income', 'increase', 'index', 'indicate',
            'indoor', 'industry', 'infant', 'inflict', 'inform', 'inhale', 'inherit', 'initial', 'inject', 'injury',
            'inmate', 'inner', 'innocent', 'input', 'inquiry', 'insane', 'insect', 'inside', 'inspire', 'install',
            'intact', 'interest', 'into', 'invest', 'invite', 'involve', 'iron', 'island', 'isolate', 'issue', 'item',
            'ivory', 'jacket', 'jaguar', 'jar', 'jazz', 'jealous', 'jeans', 'jelly', 'jewel', 'job', 'join', 'joke',
            'journey', 'joy', 'judge', 'juice', 'jump', 'jungle', 'junior', 'junk', 'just', 'kangaroo', 'keen', 'keep',
            'ketchup', 'key', 'kick', 'kid', 'kidney', 'kind', 'kingdom', 'kiss', 'kit', 'kitchen', 'kite', 'kitten',
            'kiwi', 'knee', 'knife', 'knock', 'know', 'lab', 'label', 'labor', 'ladder', 'lady', 'lake', 'lamp',
            'language', 'laptop', 'large', 'later', 'latin', 'laugh', 'laundry', 'lava', 'law', 'lawn', 'lawsuit',
            'layer', 'lazy', 'leader', 'leaf', 'learn', 'leave', 'lecture', 'left', 'leg', 'legal', 'legend', 'leisure',
            'lemon', 'lend', 'length', 'lens', 'leopard', 'lesson', 'letter', 'level', 'liar', 'liberty', 'library',
            'license', 'life', 'lift', 'light', 'like', 'limb', 'limit', 'link', 'lion', 'liquid', 'list', 'little',
            'live', 'lizard', 'load', 'loan', 'lobster', 'local', 'lock', 'logic', 'lonely', 'long', 'loop', 'lottery',
            'loud', 'lounge', 'love', 'loyal', 'lucky', 'luggage', 'lumber', 'lunar', 'lunch', 'luxury', 'lyrics',
            'machine', 'mad', 'magic', 'magnet', 'maid', 'mail', 'main', 'major', 'make', 'mammal', 'man', 'manage',
            'mandate', 'mango', 'mansion', 'manual', 'maple', 'marble', 'march', 'margin', 'marine', 'market',
            'marriage', 'mask', 'mass', 'master', 'match', 'material', 'math', 'matrix', 'matter', 'maximum', 'maze',
            'meadow', 'mean', 'measure', 'meat', 'mechanic', 'medal', 'media', 'melody', 'melt', 'member', 'memory',
            'mention', 'menu', 'mercy', 'merge', 'merit', 'merry', 'mesh', 'message', 'metal', 'method', 'middle',
            'midnight', 'milk', 'million', 'mimic', 'mind', 'minimum', 'minor', 'minute', 'miracle', 'mirror', 'misery',
            'miss', 'mistake', 'mix', 'mixed', 'mixture', 'mobile', 'model', 'modify', 'mom', 'moment', 'monitor',
            'monkey', 'monster', 'month', 'moon', 'moral', 'more', 'morning', 'mosquito', 'mother', 'motion', 'motor',
            'mountain', 'mouse', 'move', 'movie', 'much', 'muffin', 'mule', 'multiply', 'muscle', 'museum', 'mushroom',
            'music', 'must', 'mutual', 'myself', 'mystery', 'myth', 'naive', 'name', 'napkin', 'narrow', 'nasty',
            'nation', 'nature', 'near', 'neck', 'need', 'negative', 'neglect', 'neither', 'nephew', 'nerve', 'nest',
            'net', 'network', 'neutral', 'never', 'news', 'next', 'nice', 'night', 'noble', 'noise', 'nominee',
            'noodle', 'normal', 'north', 'nose', 'notable', 'note', 'nothing', 'notice', 'novel', 'now', 'nuclear',
            'number', 'nurse', 'nut', 'oak', 'obey', 'object', 'oblige', 'obscure', 'observe', 'obtain', 'obvious',
            'occur', 'ocean', 'october', 'odor', 'off', 'offer', 'office', 'often', 'oil', 'okay', 'old', 'olive',
            'olympic', 'omit', 'once', 'one', 'onion', 'online', 'only', 'open', 'opera', 'opinion', 'oppose',
            'option', 'orange', 'orbit', 'orchard', 'order', 'ordinary', 'organ', 'orient', 'original', 'orphan',
            'ostrich', 'other', 'outdoor', 'outer', 'output', 'outside', 'oval', 'oven', 'over', 'own', 'owner',
            'oxygen', 'oyster', 'ozone', 'pact', 'paddle', 'page', 'pair', 'palace', 'palm', 'panda', 'panel', 'panic',
            'panther', 'paper', 'parade', 'parent', 'park', 'parrot', 'party', 'pass', 'patch', 'path', 'patient',
            'patrol', 'pattern', 'pause', 'pave', 'payment', 'peace', 'peanut', 'pear', 'peasant', 'pelican', 'pen',
            'penalty', 'pencil', 'people', 'pepper', 'perfect', 'permit', 'person', 'pet', 'phone', 'photo', 'phrase',
            'physical', 'piano', 'picnic', 'picture', 'piece', 'pig', 'pigeon', 'pill', 'pilot', 'pink', 'pioneer',
            'pipe', 'pistol', 'pitch', 'pizza', 'place', 'planet', 'plastic', 'plate', 'play', 'please', 'pledge',
            'pluck', 'plug', 'plunge', 'poem', 'poet', 'point', 'polar', 'pole', 'police', 'pond', 'pony', 'pool',
            'popular', 'portion', 'position', 'possible', 'post', 'potato', 'pottery', 'poverty', 'powder', 'power',
            'practice', 'praise', 'predict', 'prefer', 'prepare', 'present', 'pretty', 'prevent', 'price', 'pride',
            'primary', 'print', 'priority', 'prison', 'private', 'prize', 'problem', 'process', 'produce', 'profit',
            'program', 'project', 'promote', 'proof', 'property', 'prosper', 'protect', 'proud', 'provide', 'public',
            'pudding', 'pull', 'pulp', 'pulse', 'pumpkin', 'punch', 'pupil', 'puppy', 'purchase', 'purity', 'purpose',
            'purse', 'push', 'put', 'puzzle', 'pyramid', 'quality', 'quantum', 'quarter', 'question', 'quick', 'quit',
            'quiz', 'quote', 'rabbit', 'raccoon', 'race', 'rack', 'radar', 'radio', 'rail', 'rain', 'raise', 'rally',
            'ramp', 'ranch', 'random', 'range', 'rapid', 'rare', 'rate', 'rather', 'raven', 'raw', 'razor', 'ready',
            'real', 'reason', 'rebel', 'rebuild', 'recall', 'receive', 'recipe', 'record', 'recycle', 'reduce',
            'reflect', 'reform', 'refuse', 'region', 'regret', 'regular', 'reject', 'relax', 'release', 'relief',
            'rely', 'remain', 'remember', 'remind', 'remove', 'render', 'renew', 'rent', 'reopen', 'repair', 'repeat',
            'replace', 'report', 'require', 'rescue', 'resemble', 'resist', 'resource', 'response', 'result', 'retire',
            'retreat', 'return', 'reunion', 'reveal', 'review', 'reward', 'rhythm', 'rib', 'ribbon', 'rice', 'rich',
            'ride', 'ridge', 'rifle', 'right', 'rigid', 'ring', 'riot', 'ripple', 'risk', 'ritual', 'rival', 'river',
            'road', 'roast', 'robot', 'robust', 'rocket', 'romance', 'roof', 'rookie', 'room', 'rose', 'rotate',
            'rough', 'round', 'route', 'royal', 'rubber', 'rude', 'rug', 'rule', 'run', 'runway', 'rural', 'sad',
            'saddle', 'sadness', 'safe', 'sail', 'salad', 'salmon', 'salon', 'salt', 'salute', 'same', 'sample', 'sand',
            'satisfy', 'satoshi', 'sauce', 'sausage', 'save', 'say', 'scale', 'scan', 'scare', 'scatter', 'scene',
            'scheme', 'school', 'science', 'scissors', 'scorpion', 'scout', 'scrap', 'screen', 'script', 'scrub', 'sea',
            'search', 'season', 'seat', 'second', 'secret', 'section', 'security', 'seed', 'seek', 'segment', 'select',
            'sell', 'seminar', 'senior', 'sense', 'sentence', 'series', 'service', 'session', 'settle', 'setup',
            'seven', 'shadow', 'shaft', 'shallow', 'share', 'shed', 'shell', 'sheriff', 'shield', 'shift', 'shine',
            'ship', 'shiver', 'shock', 'shoe', 'shoot', 'shop', 'short', 'shoulder', 'shove', 'shrimp', 'shrug',
            'shuffle', 'shy', 'sibling', 'sick', 'side', 'siege', 'sight', 'sign', 'silent', 'silk', 'silly', 'silver',
            'similar', 'simple', 'since', 'sing', 'siren', 'sister', 'situate', 'six', 'size', 'skate', 'sketch', 'ski',
            'skill', 'skin', 'skirt', 'skull', 'slab', 'slam', 'sleep', 'slender', 'slice', 'slide', 'slight', 'slim',
            'slogan', 'slot', 'slow', 'slush', 'small', 'smart', 'smile', 'smoke', 'smooth', 'snack', 'snake', 'snap',
            'sniff', 'snow', 'soap', 'soccer', 'social', 'sock', 'soda', 'soft', 'solar', 'soldier', 'solid',
            'solution', 'solve', 'someone', 'song', 'soon', 'sorry', 'sort', 'soul', 'sound', 'soup', 'source', 'south',
            'space', 'spare', 'spatial', 'spawn', 'speak', 'special', 'speed', 'spell', 'spend', 'sphere', 'spice',
            'spider', 'spike', 'spin', 'spirit', 'split', 'spoil', 'sponsor', 'spoon', 'sport', 'spot', 'spray',
            'spread', 'spring', 'spy', 'square', 'squeeze', 'squirrel', 'stable', 'stadium', 'staff', 'stage', 'stairs',
            'stamp', 'stand', 'start', 'state', 'stay', 'steak', 'steel', 'stem', 'step', 'stereo', 'stick', 'still',
            'sting', 'stock', 'stomach', 'stone', 'stool', 'story', 'stove', 'strategy', 'street', 'strike', 'strong',
            'struggle', 'student', 'stuff', 'stumble', 'style', 'subject', 'submit', 'subway', 'success', 'such',
            'sudden', 'suffer', 'sugar', 'suggest', 'suit', 'summer', 'sun', 'sunny', 'sunset', 'super', 'supply',
            'supreme', 'sure', 'surface', 'surge', 'surprise', 'surround', 'survey', 'suspect', 'sustain', 'swallow',
            'swamp', 'swap', 'swarm', 'swear', 'sweet', 'swift', 'swim', 'swing', 'switch', 'sword', 'symbol',
            'symptom', 'syrup', 'system', 'table', 'tackle', 'tag', 'tail', 'talent', 'talk', 'tank', 'tape', 'target',
            'task', 'taste', 'tattoo', 'taxi', 'teach', 'team', 'tell', 'ten', 'tenant', 'tennis', 'tent', 'term',
            'test', 'text', 'thank', 'that', 'theme', 'then', 'theory', 'there', 'they', 'thing', 'this', 'thought',
            'three', 'thrive', 'throw', 'thumb', 'thunder', 'ticket', 'tide', 'tiger', 'tilt', 'timber', 'time', 'tiny',
            'tip', 'tired', 'tissue', 'title', 'toast', 'tobacco', 'today', 'toddler', 'toe', 'together', 'toilet',
            'token', 'tomato', 'tomorrow', 'tone', 'tongue', 'tonight', 'tool', 'tooth', 'top', 'topic', 'topple',
            'torch', 'tornado', 'tortoise', 'toss', 'total', 'tourist', 'toward', 'tower', 'town', 'toy', 'track',
            'trade', 'traffic', 'tragic', 'train', 'transfer', 'trap', 'trash', 'travel', 'tray', 'treat', 'tree',
            'trend', 'trial', 'tribe', 'trick', 'trigger', 'trim', 'trip', 'trophy', 'trouble', 'truck', 'true',
            'truly', 'trumpet', 'trust', 'truth', 'try', 'tube', 'tuition', 'tumble', 'tuna', 'tunnel', 'turkey',
            'turn', 'turtle', 'twelve', 'twenty', 'twice', 'twin', 'twist', 'two', 'type', 'typical', 'ugly',
            'umbrella', 'unable', 'unaware', 'uncle', 'uncover', 'under', 'undo', 'unfair', 'unfold', 'unhappy',
            'uniform', 'unique', 'unit', 'universe', 'unknown', 'unlock', 'until', 'unusual', 'unveil', 'update',
            'upgrade', 'uphold', 'upon', 'upper', 'upset', 'urban', 'urge', 'usage', 'use', 'used', 'useful', 'useless',
            'usual', 'utility', 'vacant', 'vacuum', 'vague', 'valid', 'valley', 'valve', 'van', 'vanish', 'vapor',
            'various', 'vast', 'vault', 'vehicle', 'velvet', 'vendor', 'venture', 'venue', 'verb', 'verify', 'version',
            'very', 'vessel', 'veteran', 'viable', 'vibrant', 'vicious', 'victory', 'video', 'view', 'village',
            'vintage', 'violin', 'virtual', 'virus', 'visa', 'visit', 'visual', 'vital', 'vivid', 'vocal', 'voice',
            'void', 'volcano', 'volume', 'vote', 'voyage', 'wage', 'wagon', 'wait', 'walk', 'wall', 'walnut', 'want',
            'warfare', 'warm', 'warrior', 'wash', 'wasp', 'waste', 'water', 'wave', 'way', 'wealth', 'weapon', 'wear',
            'weasel', 'weather', 'web', 'wedding', 'weekend', 'weird', 'welcome', 'west', 'wet', 'whale', 'what',
            'wheat', 'wheel', 'when', 'where', 'whip', 'whisper', 'wide', 'width', 'wife', 'wild', 'will', 'win',
            'window', 'wine', 'wing', 'wink', 'winner', 'winter', 'wire', 'wisdom', 'wise', 'wish', 'witness', 'wolf',
            'woman', 'wonder', 'wood', 'wool', 'word', 'work', 'world', 'worry', 'worth', 'wrap', 'wreck', 'wrestle',
            'wrist', 'write', 'wrong', 'yard', 'year', 'yellow', 'you', 'young', 'youth', 'zebra', 'zero', 'zone', 'zoo'
        ]);
})();

(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('passPhraseService', ['wordList', '$window', function (wordList, $window) {
            this.generate = function () {
                var crypto = $window.crypto || $window.msCrypto;
                var bits = 160;
                var wordCount = wordList.length;
                var log2FromWordCount = Math.log(wordCount) / Math.log(2);
                var wordsInPassPhrase = Math.ceil(bits / log2FromWordCount);
                var random = new Uint16Array(wordsInPassPhrase);
                var passPhrase;

                crypto.getRandomValues(random);

                var i = 0,
                    index,
                    words = [];

                for (; i < wordsInPassPhrase; i++) {
                    index = random[i] % wordCount;
                    words.push(wordList[index]);
                }

                passPhrase = words.join(' ');

                crypto.getRandomValues(random);

                return passPhrase;
            };
        }]);
})();

(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('accountService', ['storageService', '$q', function (storageService, $q) {
            var stateCache;

            function removeByIndex(state, index) {
                state.accounts.splice(index, 1);

                return state;
            }

            function getState() {
                if (angular.isUndefined(stateCache)) {
                    return storageService.loadState().then(function (state) {
                        state = state || {};
                        if (!state.accounts)
                            state.accounts = [];

                        stateCache = state;

                        return stateCache;
                    });
                }

                return $q.when(stateCache);
            }

            this.addAccount = function (accountInfo) {
                return getState()
                    .then(function (state) {
                        state.accounts.push(accountInfo);

                        return state;
                    })
                    .then(storageService.saveState);
            };

            this.removeAccountByIndex = function (index) {
                return getState()
                    .then(function (state) {
                        return removeByIndex(state, index);
                    })
                    .then(storageService.saveState);
            };

            this.removeAccount = function (account) {
                return getState()
                    .then(function (state) {
                        var index = _.findIndex(state.accounts, {
                            address: account.address
                        });
                        return removeByIndex(state, index);
                    })
                    .then(storageService.saveState);
            };

            this.getAccounts = function () {
                return getState()
                    .then(function (state) {
                        return state.accounts;
                    });
            };
        }]);
})();

(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('addressService', ['constants.address', function (constants) {
            this.cleanupOptionalPrefix = function(displayAddress) {
                if (displayAddress.length <= 30) {
                    // Don't change aliases
                    return displayAddress;
                }

                var address = displayAddress,
                    prefixLen = constants.ADDRESS_PREFIX.length;

                if (address.length > constants.RAW_ADDRESS_LENGTH || address.startsWith(constants.ADDRESS_PREFIX)) {
                    address = address.substr(prefixLen, address.length - prefixLen);
                }

                return address;
            };

            this.validateAddress = function(address) {
                var cleanAddress = this.cleanupOptionalPrefix(address);
                return constants.MAINNET_ADDRESS_REGEXP.test(cleanAddress);
            };
        }]);
})();

/**
 * @requires {blake2b-256.js}
 * @requires {Base58.js}
 */
(function() {
    'use strict';

    angular
        .module('waves.core.services')
        .service('cryptoService', ['constants.network', '$window', function(constants, window) {

            // private version of getNetworkId byte in order to avoid circular dependency
            // between cryptoService and utilityService
            var getNetworkIdByte = function() {
                return constants.NETWORK_CODE.charCodeAt(0) & 0xFF;
            };

            var appendUint8Arrays = function(array1, array2) {
                var tmp = new Uint8Array(array1.length + array2.length);
                tmp.set(array1, 0);
                tmp.set(array2, array1.length);
                return tmp;
            };

            var appendNonce = function (originalSeed) {
                // change this is when nonce increment gets introduced
                var nonce = new Uint8Array(converters.int32ToBytes(constants.INITIAL_NONCE, true));

                return appendUint8Arrays(nonce, originalSeed);
            };

            // sha256 accepts messageBytes as Uint8Array or Array
            var sha256 = function (message) {
                var bytes;
                if (typeof(message) == 'string')
                    bytes = converters.stringToByteArray(message);
                else
                    bytes = message;

                var wordArray = converters.byteArrayToWordArrayEx(new Uint8Array(bytes));
                var resultWordArray = CryptoJS.SHA256(wordArray);

                return converters.wordArrayToByteArrayEx(resultWordArray);
            };

            var prepareKey = function (key) {
                var rounds = 1000;
                var digest = key;
                for (var i = 0; i < rounds; i++) {
                    digest = converters.byteArrayToHexString(sha256(digest));
                }

                return digest;
            };

            // blake2b 256 hash function
            this.blake2b = function (input) {
                return blake2b(input, null, 32);
            };

            // keccak 256 hash algorithm
            this.keccak = function(messageBytes) {
                // jscs:disable requireCamelCaseOrUpperCaseIdentifiers
                return keccak_256.array(messageBytes);
                // jscs:enable requireCamelCaseOrUpperCaseIdentifiers
            };

            this.sha256 = sha256;

            this.hashChain = function(noncedSecretPhraseBytes) {
                return this.keccak(this.blake2b(new Uint8Array(noncedSecretPhraseBytes)));
            };

            // Base68 encoding/decoding implementation
            this.base58 = {
                encode: function (buffer) {
                    return Base58.encode(buffer);
                },
                decode: function (string) {
                    return Base58.decode(string);
                }
            };

            this.buildAccountSeedHash = function(seedBytes) {
                var data = appendNonce(seedBytes);
                var seedHash = this.hashChain(data);

                return sha256(Array.prototype.slice.call(seedHash));
            };

            this.buildKeyPair = function(seedBytes) {
                var accountSeedHash = this.buildAccountSeedHash(seedBytes);
                var p = axlsign.generateKeyPair(accountSeedHash);

                return {
                    public: this.base58.encode(p.public),
                    private: this.base58.encode(p.private)
                };
            };

            this.buildPublicKey = function (seedBytes) {
                return this.buildKeyPair(seedBytes).public;
            };

            this.buildPrivateKey = function (seedBytes) {
                return this.buildKeyPair(seedBytes).private;
            };

            this.buildRawAddress = function (encodedPublicKey) {
                var publicKey = this.base58.decode(encodedPublicKey);
                var publicKeyHash = this.hashChain(publicKey);

                var prefix = new Uint8Array(2);
                prefix[0] = constants.ADDRESS_VERSION;
                prefix[1] = getNetworkIdByte();

                var unhashedAddress = appendUint8Arrays(prefix, publicKeyHash.slice(0, 20));
                var addressHash = this.hashChain(unhashedAddress).slice(0, 4);

                return this.base58.encode(appendUint8Arrays(unhashedAddress, addressHash));
            };

            this.buildRawAddressFromSeed = function (secretPhrase) {
                var publicKey = this.getPublicKey(secretPhrase);

                return this.buildRawAddress(publicKey);
            };

            //Returns publicKey built from string
            this.getPublicKey = function(secretPhrase) {
                return this.buildPublicKey(converters.stringToByteArray(secretPhrase));
            };

            //Returns privateKey built from string
            this.getPrivateKey = function(secretPhrase) {
                return this.buildPrivateKey(converters.stringToByteArray(secretPhrase));
            };

            //Returns key pair built from string
            this.getKeyPair = function (secretPhrase) {
                return this.buildKeyPair(converters.stringToByteArray(secretPhrase));
            };

            // function accepts buffer with private key and an array with dataToSign
            // returns buffer with signed data
            // 64 randoms bytes are added to the signature
            // method falls back to deterministic signatures if crypto object is not supported
            this.nonDeterministicSign = function(privateKey, dataToSign) {
                var crypto = window.crypto || window.msCrypto;
                var random;
                if (crypto) {
                    random = new Uint8Array(64);
                    crypto.getRandomValues(random);
                }

                var signature = axlsign.sign(privateKey, new Uint8Array(dataToSign), random);

                return this.base58.encode(signature);
            };

            // function accepts buffer with private key and an array with dataToSign
            // returns buffer with signed data
            this.deterministicSign = function(privateKey, dataToSign) {
                var signature = axlsign.sign(privateKey, new Uint8Array(dataToSign));

                return this.base58.encode(signature);
            };

            this.verify = function(senderPublicKey, dataToSign, signatureBytes) {
                return axlsign.verify(senderPublicKey, dataToSign, signatureBytes);
            };
            
            // function returns base58 encoded shared key from base58 encoded a private
            // and b public keys
            this.getSharedKey = function (aEncodedPrivateKey, bEncodedPublicKey) {
                var aPrivateKey = this.base58.decode(aEncodedPrivateKey);
                var bPublicKey = this.base58.decode(bEncodedPublicKey);
                var sharedKey = axlsign.sharedKey(aPrivateKey, bPublicKey);

                return this.base58.encode(sharedKey);
            };

            // function can be used for sharedKey preparation, as recommended in: https://github.com/wavesplatform/curve25519-js
            this.prepareKey = function (key) {
                return prepareKey(key);
            };

            this.encryptWalletSeed = function (seed, key) {
                var aesKey = prepareKey(key);

                return CryptoJS.AES.encrypt(seed, aesKey);
            };

            this.decryptWalletSeed = function (cipher, key, checksum) {
                var aesKey = prepareKey(key);
                var data = CryptoJS.AES.decrypt(cipher, aesKey);

                var actualChecksum = this.seedChecksum(converters.hexStringToByteArray(data.toString()));
                if (actualChecksum === checksum)
                    return converters.hexStringToString(data.toString());
                else
                    return false;
            };

            this.seedChecksum = function (seed) {
                return converters.byteArrayToHexString(sha256(seed));
            };
        }]);
})();

(function () {
    'use strict';

    function AssetService(signService, validateService, utilityService, cryptoService) {
        function buildId(transactionBytes) {
            var hash = cryptoService.blake2b(new Uint8Array(transactionBytes));
            return cryptoService.base58.encode(hash);
        }

        function buildCreateAssetSignatureData (asset, tokensQuantity, senderPublicKey) {
            return [].concat(
                signService.getAssetIssueTxTypeBytes(),
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getAssetNameBytes(asset.name),
                signService.getAssetDescriptionBytes(asset.description),
                signService.getAssetQuantityBytes(tokensQuantity),
                signService.getAssetDecimalPlacesBytes(asset.decimalPlaces),
                signService.getAssetIsReissuableBytes(asset.reissuable),
                signService.getFeeBytes(asset.fee.toCoins()),
                signService.getTimestampBytes(asset.time)
            );
        }

        this.createAssetIssueTransaction = function (asset, sender) {
            validateService.validateAssetIssue(asset);
            validateService.validateSender(sender);

            asset.time = asset.time || utilityService.getTime();
            asset.reissuable = angular.isDefined(asset.reissuable) ? asset.reissuable : false;
            asset.description = asset.description || '';

            var assetCurrency = Currency.create({
                displayName: asset.name,
                precision: asset.decimalPlaces
            });

            var tokens = new Money(asset.totalTokens, assetCurrency);
            var signatureData = buildCreateAssetSignatureData(asset, tokens.toCoins(), sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                id: buildId(signatureData),
                name: asset.name,
                description: asset.description,
                quantity: tokens.toCoins(),
                decimals: Number(asset.decimalPlaces),
                reissuable: asset.reissuable,
                timestamp: asset.time,
                fee: asset.fee.toCoins(),
                senderPublicKey: sender.publicKey,
                signature: signature
            };
        };

        function buildCreateAssetTransferSignatureData(transfer, senderPublicKey) {
            return [].concat(
                signService.getAssetTransferTxTypeBytes(),
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getAssetIdBytes(transfer.amount.currency.id),
                signService.getFeeAssetIdBytes(transfer.fee.currency.id),
                signService.getTimestampBytes(transfer.time),
                signService.getAmountBytes(transfer.amount.toCoins()),
                signService.getFeeBytes(transfer.fee.toCoins()),
                signService.getRecipientBytes(transfer.recipient),
                signService.getAttachmentBytes(transfer.attachment)
            );
        }

        this.createAssetTransferTransaction = function (transfer, sender) {
            validateService.validateAssetTransfer(transfer);
            validateService.validateSender(sender);

            transfer.time = transfer.time || utilityService.getTime();
            transfer.attachment = transfer.attachment || [];
            transfer.recipient = utilityService.resolveAddressOrAlias(transfer.recipient);

            var signatureData = buildCreateAssetTransferSignatureData(transfer, sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                id: buildId(signatureData),
                recipient: transfer.recipient,
                timestamp: transfer.time,
                assetId: transfer.amount.currency.id,
                amount: transfer.amount.toCoins(),
                fee: transfer.fee.toCoins(),
                feeAssetId: transfer.fee.currency.id,
                senderPublicKey: sender.publicKey,
                signature: signature,
                attachment: cryptoService.base58.encode(transfer.attachment)
            };
        };

        function buildCreateAssetReissueSignatureData(reissue, senderPublicKey) {
            return [].concat(
                signService.getAssetReissueTxTypeBytes(),
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getAssetIdBytes(reissue.totalTokens.currency.id, true),
                signService.getAssetQuantityBytes(reissue.totalTokens.toCoins()),
                signService.getAssetIsReissuableBytes(reissue.reissuable),
                signService.getFeeBytes(reissue.fee.toCoins()),
                signService.getTimestampBytes(reissue.time)
            );
        }

        this.createAssetReissueTransaction = function (reissue, sender) {
            validateService.validateAssetReissue(reissue);
            validateService.validateSender(sender);

            reissue.reissuable = angular.isDefined(reissue.reissuable) ? reissue.reissuable : false;
            reissue.time = reissue.time || utilityService.getTime();

            var signatureData = buildCreateAssetReissueSignatureData(reissue, sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                id: buildId(signatureData),
                assetId: reissue.totalTokens.currency.id,
                quantity: reissue.totalTokens.toCoins(),
                reissuable: reissue.reissuable,
                timestamp: reissue.time,
                fee: reissue.fee.toCoins(),
                senderPublicKey: sender.publicKey,
                signature: signature
            };
        };
    }

    AssetService.$inject = ['signService', 'validateService', 'utilityService', 'cryptoService'];

    angular
        .module('waves.core.services')
        .service('assetService', AssetService);
})();

(function () {
    'use strict';

    function AliasRequestService(signService, utilityService, validateService) {
        function buildCreateAliasSignatureData (alias, senderPublicKey) {
            return [].concat(
                signService.getCreateAliasTxTypeBytes(),
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getAliasBytes(alias.alias),
                signService.getFeeBytes(alias.fee.toCoins()),
                signService.getTimestampBytes(alias.time)
            );
        }

        this.buildCreateAliasRequest = function (alias, sender) {
            validateService.validateSender(sender);

            var currentTimeMillis = utilityService.getTime();
            alias.time = alias.time || currentTimeMillis;

            var signatureData = buildCreateAliasSignatureData(alias, sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                alias: alias.alias,
                timestamp: alias.time,
                fee: alias.fee.toCoins(),
                senderPublicKey: sender.publicKey,
                signature: signature
            };
        };
    }

    AliasRequestService.$inject = ['signService', 'utilityService', 'validateService'];

    angular
        .module('waves.core.services')
        .service('aliasRequestService', AliasRequestService);
})();

(function () {
    'use strict';

    function LeasingRequestService(signService, utilityService, validateService) {
        function buildStartLeasingSignatureData (startLeasing, senderPublicKey) {
            return [].concat(
                signService.getStartLeasingTxTypeBytes(),
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getRecipientBytes(startLeasing.recipient),
                signService.getAmountBytes(startLeasing.amount.toCoins()),
                signService.getFeeBytes(startLeasing.fee.toCoins()),
                signService.getTimestampBytes(startLeasing.time)
            );
        }

        this.buildStartLeasingRequest = function (startLeasing, sender) {
            validateService.validateSender(sender);

            var currentTimeMillis = utilityService.getTime();
            startLeasing.time = startLeasing.time || currentTimeMillis;
            startLeasing.recipient = utilityService.resolveAddressOrAlias(startLeasing.recipient);

            var signatureData = buildStartLeasingSignatureData(startLeasing, sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                recipient: startLeasing.recipient,
                amount: startLeasing.amount.toCoins(),
                timestamp: startLeasing.time,
                fee: startLeasing.fee.toCoins(),
                senderPublicKey: sender.publicKey,
                signature: signature
            };
        };

        function buildCancelLeasingSignatureData (cancelLeasing, senderPublicKey) {
            return [].concat(
                signService.getCancelLeasingTxTypeBytes(),
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getFeeBytes(cancelLeasing.fee.toCoins()),
                signService.getTimestampBytes(cancelLeasing.time),
                signService.getTransactionIdBytes(cancelLeasing.startLeasingTransactionId)
            );
        }

        this.buildCancelLeasingRequest = function (cancelLeasing, sender) {
            validateService.validateSender(sender);

            var currentTimeMillis = utilityService.getTime();
            cancelLeasing.time = cancelLeasing.time || currentTimeMillis;

            var signatureData = buildCancelLeasingSignatureData(cancelLeasing, sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                txId: cancelLeasing.startLeasingTransactionId,
                timestamp: cancelLeasing.time,
                fee: cancelLeasing.fee.toCoins(),
                senderPublicKey: sender.publicKey,
                signature: signature
            };
        };
    }

    LeasingRequestService.$inject = ['signService', 'utilityService', 'validateService'];

    angular
        .module('waves.core.services')
        .service('leasingRequestService', LeasingRequestService);
})();

(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('apiService', ['Restangular', 'cryptoService', function (rest, cryptoService) {
            var blocksApi = rest.all('blocks');

            this.blocks = {
                height: function() {
                    return blocksApi.get('height');
                },
                last: function() {
                    return blocksApi.get('last');
                },
                list: function (startHeight, endHeight) {
                    return blocksApi.one('seq', startHeight).all(endHeight).getList();
                }
            };

            var addressApi = rest.all('addresses');
            var consensusApi = rest.all('consensus');
            this.address = {
                balance: function (address) {
                    return addressApi.one('balance', address).get();
                },
                effectiveBalance: function (address) {
                    return addressApi.one('effectiveBalance', address).get();
                },
                generatingBalance: function (address) {
                    return consensusApi.one('generatingbalance', address).get();
                }
            };

            var transactionApi = rest.all('transactions');

            var request;
            var timer;
            this.transactions = {
                unconfirmed: function () {
                    if (!request) {
                        request = transactionApi.all('unconfirmed').getList();
                    } else {
                        if (!timer) {
                            timer = setTimeout(function () {
                                request = transactionApi.all('unconfirmed').getList();
                                request.finally(function () {
                                    timer = null;
                                });
                            }, 10000);
                        }
                    }
                    return request;
                },
                list: function (address, max) {
                    max = max || 50;
                    return transactionApi.one('address', address).one('limit', max).getList();
                },
                info: function (transactionId) {
                    return transactionApi.one('info', transactionId).get();
                }
            };

            var leasingApi = rest.all('leasing').all('broadcast');
            this.leasing = {
                lease: function (signedStartLeasingTransaction) {
                    return leasingApi.all('lease').post(signedStartLeasingTransaction);
                },
                cancel: function (signedCancelLeasingTransaction) {
                    return leasingApi.all('cancel').post(signedCancelLeasingTransaction);
                }
            };

            var aliasApi = rest.all('alias');
            this.alias = {
                create: function (signedCreateAliasTransaction) {
                    return aliasApi.all('broadcast').all('create').post(signedCreateAliasTransaction);
                },
                getByAddress: function (address) {
                    return aliasApi.all('by-address').get(address).then(function (response) {
                        return response.map(function (alias) {
                            return alias.slice(8);
                        });
                    });
                }
            };

            var assetApi = rest.all('assets');
            var assetBroadcastApi = assetApi.all('broadcast');
            this.assets = {
                balance: function (address, assetId) {
                    var rest = assetApi.all('balance');
                    if (assetId)
                        return rest.all(address).get(assetId);
                    else
                        return rest.get(address);
                },
                issue: function (signedAssetIssueTransaction) {
                    return assetBroadcastApi.all('issue').post(signedAssetIssueTransaction);
                },
                reissue: function (signedAssetReissueTransaction) {
                    return assetBroadcastApi.all('reissue').post(signedAssetReissueTransaction);
                },
                transfer: function (signedAssetTransferTransaction) {
                    return assetBroadcastApi.all('transfer').post(signedAssetTransferTransaction);
                },
                massPay: function (signedTransactions) {
                    return assetBroadcastApi.all('batch-transfer').post(signedTransactions);
                },
                makeAssetNameUnique: function (signedMakeAssetNameUniqueTransaction) {
                    return assetApi
                        .all('broadcast')
                        .all('make-asset-name-unique')
                        .post(signedMakeAssetNameUniqueTransaction);
                },
                isUniqueName: function (assetName) {
                    assetName = cryptoService.base58.encode(converters.stringToByteArray(assetName));
                    return assetApi
                        .all('asset-id-by-unique-name')
                        .get(assetName)
                        .then(function (response) {
                            // FIXME : temporary fix for the API format
                            if (typeof response !== 'object') {
                                response = {assetId: response};
                            }

                            return response.assetId;
                        });
                }
            };
        }]);
})();

(function () {
    'use strict';

    var BASE58_REGEX = new RegExp('^[123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz]{0,}$');

    angular
        .module('waves.core.services')
        .service('utilityService', ['constants.network', 'cryptoService', function (constants, cryptoService) {
            var self = this;

            self.getNetworkIdByte = function () {
                return constants.NETWORK_CODE.charCodeAt(0) & 0xFF;
            };

            // long to big-endian bytes
            self.longToByteArray = function (value) {
                var bytes = new Array(7);
                for (var k = 7; k >= 0; k--) {
                    bytes[k] = value & (255);
                    value = value / 256;
                }

                return bytes;
            };

            // short to big-endian bytes
            self.shortToByteArray = function (value) {
                return converters.int16ToBytes(value, true);
            };

            self.base58StringToByteArray = function (base58String) {
                var decoded = cryptoService.base58.decode(base58String);
                var result = [];
                for (var i = 0; i < decoded.length; ++i) {
                    result.push(decoded[i] & 0xff);
                }

                return result;
            };

            self.stringToByteArrayWithSize = function (string) {
                var bytes = converters.stringToByteArray(string);
                return self.byteArrayWithSize(bytes);
            };

            self.byteArrayWithSize = function (byteArray) {
                var result = self.shortToByteArray(byteArray.length);
                return result.concat(byteArray);
            };

            self.booleanToBytes = function (flag) {
                return flag ? [1] : [0];
            };

            self.endsWithWhitespace = function (value) {
                return /\s+$/g.test(value);
            };

            self.getTime = function() {
                return Date.now();
            };

            self.isValidBase58String = function (input) {
                return BASE58_REGEX.test(input);
            };

            // Add a prefix in case of alias
            self.resolveAddressOrAlias = function (string) {
                if (string.length <= 30) {
                    return 'alias:' + constants.NETWORK_CODE + ':' + string;
                } else {
                    return string;
                }
            };
        }]);
})();

(function() {
    'use strict';

    angular
        .module('waves.core.services')
        .service('chromeStorageService', ['$q', function ($q) {
            var $key = 'WavesAccounts';
            var self = this;

            self.saveState = function (state) {
                var deferred = $q.defer();
                var json = {};
                json[$key] = state;

                chrome.storage.local.set(json, function () {
                    deferred.resolve();
                });

                return deferred.promise;
            };

            self.loadState = function () {
                var deferred = $q.defer();

                self.loadSyncState().then(function (syncState) {
                    if (syncState) {
                        self.saveState(syncState)
                            .then(function () {
                                return self.clearSyncState();
                            })
                            .then(function () {
                                deferred.resolve(syncState);
                            });
                    } else {
                        chrome.storage.local.get($key, function (data) {
                            deferred.resolve(data[$key]);
                        });
                    }
                });

                return deferred.promise;
            };

            self.loadSyncState = function () {
                var deferred = $q.defer();

                chrome.storage.sync.get($key, function (data) {
                    deferred.resolve(data[$key]);
                });

                return deferred.promise;
            };

            self.clearSyncState = function () {
                var deferred = $q.defer();

                chrome.storage.sync.clear(function () {
                    deferred.resolve();
                });

                return deferred.promise;
            };
        }]);
})();

(function() {
    'use strict';

    angular
        .module('waves.core.services')
        .service('html5StorageService', ['constants.network', '$window', '$q', function(constants, window, $q) {
            if (angular.isUndefined(constants.NETWORK_NAME))
                throw new Error('Network name hasn\'t been configured');

            var $key = 'Waves' + constants.NETWORK_NAME;

            this.saveState = function(state) {
                var serialized = angular.toJson(state);

                window.localStorage.setItem($key, serialized);

                return $q.when();
            };

            this.loadState = function() {
                var data;
                var serialized = window.localStorage.getItem($key);

                if (serialized) {
                    data = angular.fromJson(serialized);
                }

                return $q.when(data);
            };

            this.clear = function() {
                window.localStorage.removeItem($key);

                return $q.when();
            };
        }]);
})();

(function() {
    'use strict';

    var STORAGE_STRUCTURE_VERSION = 1;

    angular
        .module('waves.core.services')
        .provider('storageService', [function () {
            function getStorageVersion () {
                return STORAGE_STRUCTURE_VERSION;
            }

            function isLocalStorageEnabled(window) {
                var storage, fail, uid;
                try {
                    uid = String(new Date());
                    (storage = window.localStorage).setItem(uid, uid);
                    fail = storage.getItem(uid) != uid;
                    if (!fail)
                        storage.removeItem(uid);
                    else
                        storage = false;
                }
                catch (exception) {
                }
                return storage;
            }

            this.$get = ['$window', 'chromeStorageService', 'html5StorageService',
                function($window, chromeStorageService, html5StorageService) {
                    var result = isLocalStorageEnabled($window) ? html5StorageService : chromeStorageService;
                    result.getStorageVersion = getStorageVersion;

                    return result;
                }];
        }]);
})();

(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('formattingService', ['$window', '$filter', function (window, $filter) {

            var LOCALE_DATE_FORMATS = {
                'ar-SA': 'dd/MM/yy',
                'bg-BG': 'dd.M.yyyy',
                'ca-ES': 'dd/MM/yyyy',
                'zh-TW': 'yyyy/M/d',
                'cs-CZ': 'd.M.yyyy',
                'da-DK': 'dd-MM-yyyy',
                'de-DE': 'dd.MM.yyyy',
                'el-GR': 'd/M/yyyy',
                'en-US': 'M/d/yyyy',
                'fi-FI': 'd.M.yyyy',
                'fr-FR': 'dd/MM/yyyy',
                'he-IL': 'dd/MM/yyyy',
                'hu-HU': 'yyyy. MM. dd.',
                'is-IS': 'd.M.yyyy',
                'it-IT': 'dd/MM/yyyy',
                'ja-JP': 'yyyy/MM/dd',
                'ko-KR': 'yyyy-MM-dd',
                'nl-NL': 'd-M-yyyy',
                'nb-NO': 'dd.MM.yyyy',
                'pl-PL': 'yyyy-MM-dd',
                'pt-BR': 'd/M/yyyy',
                'ro-RO': 'dd.MM.yyyy',
                'ru-RU': 'dd.MM.yyyy',
                'hr-HR': 'd.M.yyyy',
                'sk-SK': 'd. M. yyyy',
                'sq-AL': 'yyyy-MM-dd',
                'sv-SE': 'yyyy-MM-dd',
                'th-TH': 'd/M/yyyy',
                'tr-TR': 'dd.MM.yyyy',
                'ur-PK': 'dd/MM/yyyy',
                'id-ID': 'dd/MM/yyyy',
                'uk-UA': 'dd.MM.yyyy',
                'be-BY': 'dd.MM.yyyy',
                'sl-SI': 'd.M.yyyy',
                'et-EE': 'd.MM.yyyy',
                'lv-LV': 'yyyy.MM.dd.',
                'lt-LT': 'yyyy.MM.dd',
                'fa-IR': 'MM/dd/yyyy',
                'vi-VN': 'dd/MM/yyyy',
                'hy-AM': 'dd.MM.yyyy',
                'az-Latn-AZ': 'dd.MM.yyyy',
                'eu-ES': 'yyyy/MM/dd',
                'mk-MK': 'dd.MM.yyyy',
                'af-ZA': 'yyyy/MM/dd',
                'ka-GE': 'dd.MM.yyyy',
                'fo-FO': 'dd-MM-yyyy',
                'hi-IN': 'dd-MM-yyyy',
                'ms-MY': 'dd/MM/yyyy',
                'kk-KZ': 'dd.MM.yyyy',
                'ky-KG': 'dd.MM.yy',
                'sw-KE': 'M/d/yyyy',
                'uz-Latn-UZ': 'dd/MM yyyy',
                'tt-RU': 'dd.MM.yyyy',
                'pa-IN': 'dd-MM-yy',
                'gu-IN': 'dd-MM-yy',
                'ta-IN': 'dd-MM-yyyy',
                'te-IN': 'dd-MM-yy',
                'kn-IN': 'dd-MM-yy',
                'mr-IN': 'dd-MM-yyyy',
                'sa-IN': 'dd-MM-yyyy',
                'mn-MN': 'yy.MM.dd',
                'gl-ES': 'dd/MM/yy',
                'kok-IN': 'dd-MM-yyyy',
                'syr-SY': 'dd/MM/yyyy',
                'dv-MV': 'dd/MM/yy',
                'ar-IQ': 'dd/MM/yyyy',
                'zh-CN': 'yyyy/M/d',
                'de-CH': 'dd.MM.yyyy',
                'en-GB': 'dd/MM/yyyy',
                'es-MX': 'dd/MM/yyyy',
                'fr-BE': 'd/MM/yyyy',
                'it-CH': 'dd.MM.yyyy',
                'nl-BE': 'd/MM/yyyy',
                'nn-NO': 'dd.MM.yyyy',
                'pt-PT': 'dd-MM-yyyy',
                'sr-Latn-CS': 'd.M.yyyy',
                'sv-FI': 'd.M.yyyy',
                'az-Cyrl-AZ': 'dd.MM.yyyy',
                'ms-BN': 'dd/MM/yyyy',
                'uz-Cyrl-UZ': 'dd.MM.yyyy',
                'ar-EG': 'dd/MM/yyyy',
                'zh-HK': 'd/M/yyyy',
                'de-AT': 'dd.MM.yyyy',
                'en-AU': 'd/MM/yyyy',
                'es-ES': 'dd/MM/yyyy',
                'fr-CA': 'yyyy-MM-dd',
                'sr-Cyrl-CS': 'd.M.yyyy',
                'ar-LY': 'dd/MM/yyyy',
                'zh-SG': 'd/M/yyyy',
                'de-LU': 'dd.MM.yyyy',
                'en-CA': 'dd/MM/yyyy',
                'es-GT': 'dd/MM/yyyy',
                'fr-CH': 'dd.MM.yyyy',
                'ar-DZ': 'dd-MM-yyyy',
                'zh-MO': 'd/M/yyyy',
                'de-LI': 'dd.MM.yyyy',
                'en-NZ': 'd/MM/yyyy',
                'es-CR': 'dd/MM/yyyy',
                'fr-LU': 'dd/MM/yyyy',
                'ar-MA': 'dd-MM-yyyy',
                'en-IE': 'dd/MM/yyyy',
                'es-PA': 'MM/dd/yyyy',
                'fr-MC': 'dd/MM/yyyy',
                'ar-TN': 'dd-MM-yyyy',
                'en-ZA': 'yyyy/MM/dd',
                'es-DO': 'dd/MM/yyyy',
                'ar-OM': 'dd/MM/yyyy',
                'en-JM': 'dd/MM/yyyy',
                'es-VE': 'dd/MM/yyyy',
                'ar-YE': 'dd/MM/yyyy',
                'en-029': 'MM/dd/yyyy',
                'es-CO': 'dd/MM/yyyy',
                'ar-SY': 'dd/MM/yyyy',
                'en-BZ': 'dd/MM/yyyy',
                'es-PE': 'dd/MM/yyyy',
                'ar-JO': 'dd/MM/yyyy',
                'en-TT': 'dd/MM/yyyy',
                'es-AR': 'dd/MM/yyyy',
                'ar-LB': 'dd/MM/yyyy',
                'en-ZW': 'M/d/yyyy',
                'es-EC': 'dd/MM/yyyy',
                'ar-KW': 'dd/MM/yyyy',
                'en-PH': 'M/d/yyyy',
                'es-CL': 'dd-MM-yyyy',
                'ar-AE': 'dd/MM/yyyy',
                'es-UY': 'dd/MM/yyyy',
                'ar-BH': 'dd/MM/yyyy',
                'es-PY': 'dd/MM/yyyy',
                'ar-QA': 'dd/MM/yyyy',
                'es-BO': 'dd/MM/yyyy',
                'es-SV': 'dd/MM/yyyy',
                'es-HN': 'dd/MM/yyyy',
                'es-NI': 'dd/MM/yyyy',
                'es-PR': 'dd/MM/yyyy',
                'am-ET': 'd/M/yyyy',
                'tzm-Latn-DZ': 'dd-MM-yyyy',
                'iu-Latn-CA': 'd/MM/yyyy',
                'sma-NO': 'dd.MM.yyyy',
                'mn-Mong-CN': 'yyyy/M/d',
                'gd-GB': 'dd/MM/yyyy',
                'en-MY': 'd/M/yyyy',
                'prs-AF': 'dd/MM/yy',
                'bn-BD': 'dd-MM-yy',
                'wo-SN': 'dd/MM/yyyy',
                'rw-RW': 'M/d/yyyy',
                'qut-GT': 'dd/MM/yyyy',
                'sah-RU': 'MM.dd.yyyy',
                'gsw-FR': 'dd/MM/yyyy',
                'co-FR': 'dd/MM/yyyy',
                'oc-FR': 'dd/MM/yyyy',
                'mi-NZ': 'dd/MM/yyyy',
                'ga-IE': 'dd/MM/yyyy',
                'se-SE': 'yyyy-MM-dd',
                'br-FR': 'dd/MM/yyyy',
                'smn-FI': 'd.M.yyyy',
                'moh-CA': 'M/d/yyyy',
                'arn-CL': 'dd-MM-yyyy',
                'ii-CN': 'yyyy/M/d',
                'dsb-DE': 'd. M. yyyy',
                'ig-NG': 'd/M/yyyy',
                'kl-GL': 'dd-MM-yyyy',
                'lb-LU': 'dd/MM/yyyy',
                'ba-RU': 'dd.MM.yy',
                'nso-ZA': 'yyyy/MM/dd',
                'quz-BO': 'dd/MM/yyyy',
                'yo-NG': 'd/M/yyyy',
                'ha-Latn-NG': 'd/M/yyyy',
                'fil-PH': 'M/d/yyyy',
                'ps-AF': 'dd/MM/yy',
                'fy-NL': 'd-M-yyyy',
                'ne-NP': 'M/d/yyyy',
                'se-NO': 'dd.MM.yyyy',
                'iu-Cans-CA': 'd/M/yyyy',
                'sr-Latn-RS': 'd.M.yyyy',
                'si-LK': 'yyyy-MM-dd',
                'sr-Cyrl-RS': 'd.M.yyyy',
                'lo-LA': 'dd/MM/yyyy',
                'km-KH': 'yyyy-MM-dd',
                'cy-GB': 'dd/MM/yyyy',
                'bo-CN': 'yyyy/M/d',
                'sms-FI': 'd.M.yyyy',
                'as-IN': 'dd-MM-yyyy',
                'ml-IN': 'dd-MM-yy',
                'en-IN': 'dd-MM-yyyy',
                'or-IN': 'dd-MM-yy',
                'bn-IN': 'dd-MM-yy',
                'tk-TM': 'dd.MM.yy',
                'bs-Latn-BA': 'd.M.yyyy',
                'mt-MT': 'dd/MM/yyyy',
                'sr-Cyrl-ME': 'd.M.yyyy',
                'se-FI': 'd.M.yyyy',
                'zu-ZA': 'yyyy/MM/dd',
                'xh-ZA': 'yyyy/MM/dd',
                'tn-ZA': 'yyyy/MM/dd',
                'hsb-DE': 'd. M. yyyy',
                'bs-Cyrl-BA': 'd.M.yyyy',
                'tg-Cyrl-TJ': 'dd.MM.yy',
                'sr-Latn-BA': 'd.M.yyyy',
                'smj-NO': 'dd.MM.yyyy',
                'rm-CH': 'dd/MM/yyyy',
                'smj-SE': 'yyyy-MM-dd',
                'quz-EC': 'dd/MM/yyyy',
                'quz-PE': 'dd/MM/yyyy',
                'hr-BA': 'd.M.yyyy.',
                'sr-Latn-ME': 'd.M.yyyy',
                'sma-SE': 'yyyy-MM-dd',
                'en-SG': 'd/M/yyyy',
                'ug-CN': 'yyyy-M-d',
                'sr-Cyrl-BA': 'd.M.yyyy',
                'es-US': 'M/d/yyyy'
            };

            var LANG = window.navigator.userLanguage || window.navigator.language;
            var LOCALE_DATE_FORMAT = LOCALE_DATE_FORMATS[LANG] || 'dd/MM/yyyy';
            var settings = {
                '24_hour_format': '1'
            };

            this.formatTimestamp = function (timestamp, dateOnly, isAbsoluteTime) {
                var date;
                if (typeof timestamp == 'object') {
                    date = timestamp;
                } else if (isAbsoluteTime) {
                    date = new Date(timestamp);
                } else {
                    date = new Date(timestamp);
                }

                var format = LOCALE_DATE_FORMAT;
                if (!dateOnly) {
                    var timeFormat = 'H:mm:ss';

                    if (settings['24_hour_format'] === '0')
                        timeFormat = 'h:mm:ss a';

                    format += ' ' + timeFormat;
                }

                return $filter('date')(date, format);
            };
        }]);
})();

/**
 * @author Björn Wenzel
 */
(function () {
    'use strict';
    angular.module('waves.core.filter')
        .filter('formatting', ['formattingService', function (formattingService) {
            return function(timestamp, dateOnly) {
                if (angular.isUndefined(dateOnly)) {
                    dateOnly = false;
                }

                return formattingService.formatTimestamp(timestamp, dateOnly);
            };
        }]);
})();

(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('coinomatCurrencyMappingService', [function () {
            function unsupportedCurrency(currency) {
                throw new Error('Unsupported currency: ' + currency.displayName);
            }

            /**
             * Currency codes for Waves Platform
             * @param {Currency} currency
             * @returns {string} currency code
             */
            this.platformCurrencyCode = function (currency) {
                switch (currency.id) {
                    case Currency.BTC.id:
                        return 'WBTC';

                    case Currency.WAVES.id:
                        return 'WAVES';

                    case Currency.ETH.id:
                        return 'WETH';

                    case Currency.LTC.id:
                        return 'WLTC';

                    case Currency.ZEC.id:
                        return 'WZEC';

                    case Currency.BCH.id:
                        return 'WBCH';
                }

                unsupportedCurrency(currency);
            };

            /**
             * Currency codes for Coinomat gateway
             * @param {Currency} currency
             * @returns {string} currency code
             */
            this.gatewayCurrencyCode = function (currency) {
                switch (currency.id) {
                    case Currency.BTC.id:
                        return 'BTC';

                    case Currency.WAVES.id:
                        return 'WAVES';

                    case Currency.ETH.id:
                        return 'ETH';

                    case Currency.LTC.id:
                        return 'LTC';

                    case Currency.ZEC.id:
                        return 'ZEC';

                    case Currency.BCH.id:
                        return 'BCH';
                }

                unsupportedCurrency(currency);
            };
        }]);
})();

(function () {
    'use strict';

    var LANGUAGE = 'ru_RU';

    function ensureTunnelCreated(response) {
        if (!response.ok) {
            console.log(response);
            throw new Error('Failed to create tunnel: ' + response.error);
        }
    }

    function ensureTunnelObtained(response) {
        if (!response.tunnel) {
            console.log(response);
            throw new Error('Failed to get tunnel: ' + response.error);
        }
    }

    function CoinomatService(rest, mappingService) {
        var apiRoot = rest.all('api').all('v1');

        /* jscs:disable requireCamelCaseOrUpperCaseIdentifiers */
        function loadPaymentDetails(currencyCodeFrom, currencyCodeTo, recipientAddress) {
            return apiRoot.get('create_tunnel.php', {
                currency_from: currencyCodeFrom,
                currency_to: currencyCodeTo,
                wallet_to: recipientAddress
            }).then(function (response) {
                ensureTunnelCreated(response);

                return {
                    id: response.tunnel_id,
                    k1: response.k1,
                    k2: response.k2
                };
            }).then(function (tunnel) {
                return apiRoot.get('get_tunnel.php', {
                    xt_id: tunnel.id,
                    k1: tunnel.k1,
                    k2: tunnel.k2,
                    history: 0,
                    lang: LANGUAGE
                });
            }).then(function (response) {
                ensureTunnelObtained(response);

                // here only BTC wallet is returned
                // probably for other currencies more requisites are required
                return {
                    address: response.tunnel.wallet_from,
                    attachment: response.tunnel.attachment
                };
            });
        }
        /* jscs:enable requireCamelCaseOrUpperCaseIdentifiers */

        this.getDepositDetails = function (sourceCurrency, targetCurrency, wavesRecipientAddress) {
            var gatewayCurrencyCode = mappingService.gatewayCurrencyCode(sourceCurrency);
            var platformCurrencyCode = mappingService.platformCurrencyCode(targetCurrency);

            return loadPaymentDetails(gatewayCurrencyCode, platformCurrencyCode, wavesRecipientAddress);
        };

        this.getWithdrawDetails = function (currency, recipientAddress) {
            var gatewayCurrencyCode = mappingService.gatewayCurrencyCode(currency);
            var platformCurrencyCode = mappingService.platformCurrencyCode(currency);

            return loadPaymentDetails(platformCurrencyCode, gatewayCurrencyCode, recipientAddress);
        };

        this.getWithdrawRate = function (currency) {
            var gatewayCurrencyCode = mappingService.gatewayCurrencyCode(currency);
            var platformCurrencyCode = mappingService.platformCurrencyCode(currency);

            return apiRoot.get('get_xrate.php', {
                f: platformCurrencyCode,
                t: gatewayCurrencyCode,
                lang: LANGUAGE
            });
        };
    }

    CoinomatService.$inject = ['CoinomatRestangular', 'coinomatCurrencyMappingService'];

    angular
        .module('waves.core.services')
        .service('coinomatService', CoinomatService);
})();

(function () {
    'use strict';

    function CoinomatFiatService(rest, currencyMappingService) {
        var apiRoot = rest.all('api').all('v2').all('indacoin');

        this.getLimits = function (address, fiatCurrency, cryptoCurrency) {
            return apiRoot.get('limits.php', {
                address: address,
                fiat: fiatCurrency,
                crypto: currencyMappingService.gatewayCurrencyCode(cryptoCurrency)
            });
        };

        this.getRate = function (address, fiatAmount, fiatCurrency, cryptoCurrency) {
            return apiRoot.get('rate.php', {
                address: address,
                fiat: fiatCurrency,
                amount: fiatAmount,
                crypto: currencyMappingService.gatewayCurrencyCode(cryptoCurrency)
            });
        };

        this.getMerchantUrl = function (address, fiatAmount, fiatCurrency, cryptoCurrency) {
            return apiRoot.all('buy.php').getRequestedUrl() +
                '?address=' + address +
                '&fiat=' + fiatCurrency +
                '&amount=' + fiatAmount +
                '&crypto=' + currencyMappingService.gatewayCurrencyCode(cryptoCurrency);
        };
    }

    CoinomatFiatService.$inject = ['CoinomatRestangular', 'coinomatCurrencyMappingService'];

    angular
        .module('waves.core.services')
        .service('coinomatFiatService', CoinomatFiatService);
})();

(function () {
    'use strict';

    var WAVES_ASSET_ID = 'WAVES',
        WAVES_PRECISION = 8;

    function denormalizeId(id) {
        return id === WAVES_ASSET_ID ? '' : id;
    }

    function normalizeId(id) {
        return id ? id : WAVES_ASSET_ID;
    }

    function MatcherApiService(rest, utilityService, cryptoService, validateService) {
        var apiRoot = rest.all('matcher');
        var orderbookRoot = apiRoot.all('orderbook');

        this.createOrder = function (signedOrderRequest) {
            return orderbookRoot.post(signedOrderRequest);
        };

        this.cancelOrder = function (firstAssetId, secondAssetId, signedCancelRequest) {
            return orderbookRoot
                .all(normalizeId(firstAssetId))
                .all(normalizeId(secondAssetId))
                .all('cancel')
                .post(signedCancelRequest);
        };

        this.deleteOrder = function (firstAssetId, secondAssetId, signedCancelRequest) {
            return orderbookRoot
                .all(normalizeId(firstAssetId))
                .all(normalizeId(secondAssetId))
                .all('delete')
                .post(signedCancelRequest);
        };

        this.orderStatus = function (firstAssetId, secondAssetId, orderId) {
            return orderbookRoot
                .all(normalizeId(firstAssetId))
                .all(normalizeId(secondAssetId))
                .get(orderId);
        };

        this.loadMatcherKey = function () {
            return apiRoot.get('');
        };

        this.loadOrderbook = function (firstAssetId, secondAssetId) {
            return orderbookRoot.all(normalizeId(firstAssetId)).get(normalizeId(secondAssetId))
                .then(function (response) {
                    response.pair.amountAsset = denormalizeId(response.pair.amountAsset);
                    response.pair.priceAsset = denormalizeId(response.pair.priceAsset);

                    return response;
                });
        };

        function buildLoadUserOrdersSignature(timestamp, sender) {
            validateService.validateSender(sender);

            var publicKeyBytes = utilityService.base58StringToByteArray(sender.publicKey),
                timestampBytes = utilityService.longToByteArray(timestamp),
                signatureData = [].concat(publicKeyBytes, timestampBytes),

                privateKeyBytes = cryptoService.base58.decode(sender.privateKey);

            return cryptoService.nonDeterministicSign(privateKeyBytes, signatureData);
        }

        this.loadUserOrders = function (amountAsset, priceAsset, sender) {
            var timestamp = Date.now(),
                signature = buildLoadUserOrdersSignature(timestamp, sender);

            return orderbookRoot
                .all(normalizeId(amountAsset))
                .all(normalizeId(priceAsset))
                .all('publicKey')
                .get(sender.publicKey, {}, {
                    Timestamp: timestamp,
                    Signature: signature
                });
        };

        this.loadAllMarkets = function () {
            return orderbookRoot.get('').then(function (response) {
                var pairs = [];
                _.forEach(response.markets, function (market) {
                    var id = normalizeId(market.amountAsset) + '/' + normalizeId(market.priceAsset);
                    var pair = {
                        id: id,
                        amountAssetInfo: market.amountAssetInfo,
                        amountAsset: Currency.create({
                            id: denormalizeId(market.amountAsset),
                            displayName: market.amountAssetName,
                            precision: market.amountAssetInfo ? market.amountAssetInfo.decimals : WAVES_PRECISION
                        }),
                        priceAssetInfo: market.priceAssetInfo,
                        priceAsset: Currency.create({
                            id: denormalizeId(market.priceAsset),
                            displayName: market.priceAssetName,
                            precision: market.priceAssetInfo ? market.priceAssetInfo.decimals : WAVES_PRECISION
                        }),
                        created: market.created
                    };
                    pairs.push(pair);
                });

                return pairs;
            });
        };

        this.getTradableBalance = function (amountAsset, priceAsset, address) {
            var normAmountAsset = normalizeId(amountAsset),
                normPriceAsset = normalizeId(priceAsset);

            return orderbookRoot
                .all(normAmountAsset)
                .all(normPriceAsset)
                .all('tradableBalance')
                .get(address)
                .then(function (response) {
                    var result = {};
                    result[denormalizeId(normAmountAsset)] = response[normAmountAsset];
                    result[denormalizeId(normPriceAsset)] = response[normPriceAsset];
                    return result;
                });
        };
    }

    MatcherApiService.$inject = ['MatcherRestangular', 'utilityService', 'cryptoService', 'validateService'];

    angular
        .module('waves.core.services')
        .service('matcherApiService', MatcherApiService);
})();

(function () {
    'use strict';

    var MINUTE = 60 * 1000,
        DEFAULT_FRAME = 30,
        DEFAULT_LIMIT = 50;

    function serializeId(id) {
        return id === '' ? 'WAVES' : id;
    }

    function DatafeedApiService(rest) {
        var self = this,
            apiRoot = rest.all('api');

        self.getSymbols = function () {
            return apiRoot.get('symbols');
        };

        self.getCandles = function (pair, from, to, frame) {
            frame = frame || DEFAULT_FRAME;
            to = to || Date.now();
            from = from || to - 50 * frame * MINUTE;

            return apiRoot
                .all('candles')
                .all(serializeId(pair.amountAsset.id))
                .all(serializeId(pair.priceAsset.id))
                .all(frame)
                .all(from)
                .get(to);
        };

        self.getLastCandles = function (pair, limit, frame) {
            frame = frame || DEFAULT_FRAME;
            limit = limit || DEFAULT_LIMIT;

            return apiRoot
                .all('candles')
                .all(serializeId(pair.amountAsset.id))
                .all(serializeId(pair.priceAsset.id))
                .all(frame)
                .get(limit);
        };

        self.getTrades = function (pair, limit) {
            limit = limit || DEFAULT_LIMIT;

            return apiRoot
                .all('trades')
                .all(serializeId(pair.amountAsset.id))
                .all(serializeId(pair.priceAsset.id))
                .get(limit);
        };

        self.getTradesByAddress = function (pair, address, limit) {
            limit = limit || DEFAULT_LIMIT;

            return apiRoot
                .all('trades')
                .all(serializeId(pair.amountAsset.id))
                .all(serializeId(pair.priceAsset.id))
                .all(address)
                .get(limit);
        };
    }

    DatafeedApiService.$inject = ['DatafeedRestangular'];

    angular
        .module('waves.core.services')
        .service('datafeedApiService', DatafeedApiService);
})();

(function () {
    'use strict';

    var SELL_ORDER_TYPE = 'sell';

    function MatcherRequestService(signService, utilityService, validateService) {
        function buildCreateOrderSignatureData(order, senderPublicKey) {
            return [].concat(
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getPublicKeyBytes(order.matcherKey),
                signService.getAssetIdBytes(order.price.amountAsset.id),
                signService.getAssetIdBytes(order.price.priceAsset.id),
                signService.getOrderTypeBytes(order.orderType === SELL_ORDER_TYPE),
                signService.getAmountBytes(order.price.toBackendPrice()),
                signService.getAmountBytes(order.amount.toCoins()),
                signService.getTimestampBytes(order.time),
                signService.getTimestampBytes(order.expiration),
                signService.getFeeBytes(order.fee.toCoins())
            );
        }

        this.buildCreateOrderRequest = function (order, sender) {
            validateService.validateSender(sender);

            var currentTimeMillis = utilityService.getTime();
            order.time = order.time || currentTimeMillis;

            var date = new Date(currentTimeMillis);
            order.expiration = order.expiration || date.setDate(date.getDate() + 20);

            var signatureData = buildCreateOrderSignatureData(order, sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                orderType: order.orderType,
                assetPair: {
                    amountAsset: order.price.amountAsset.id,
                    priceAsset: order.price.priceAsset.id
                },
                price: order.price.toBackendPrice(),
                amount: order.amount.toCoins(),
                timestamp: order.time,
                expiration: order.expiration,
                matcherFee: order.fee.toCoins(),
                matcherPublicKey: order.matcherKey,
                senderPublicKey: sender.publicKey,
                signature: signature
            };
        };

        function buildCancelOrderSignatureData(orderId, senderPublicKey) {
            return [].concat(
                signService.getPublicKeyBytes(senderPublicKey),
                signService.getOrderIdBytes(orderId)
            );
        }

        this.buildCancelOrderRequest = function (orderId, sender) {
            validateService.validateSender(sender);

            if (!orderId) {
                throw new Error('orderId hasn\'t been set');
            }

            var signatureData = buildCancelOrderSignatureData(orderId, sender.publicKey);
            var signature = signService.buildSignature(signatureData, sender.privateKey);

            return {
                sender: sender.publicKey,
                orderId: orderId,
                signature: signature
            };
        };
    }

    MatcherRequestService.$inject = ['signService', 'utilityService', 'validateService'];

    angular
        .module('waves.core.services')
        .service('matcherRequestService', MatcherRequestService);
})();

var OrderPrice = (function () {

    var MATCHER_SCALE = 1e8;

    function OrderPrice(price, pair) {
        this.amountAsset = pair.amountAsset;
        this.priceAsset = pair.priceAsset;
        this.price = roundToPriceAsset(price, pair);
    }

    OrderPrice.prototype.toTokens = function () {
        return this.price.toNumber();
    };

    OrderPrice.prototype.toCoins = function () {
        return this.toTokens() * Math.pow(10, this.priceAsset.precision - this.amountAsset.precision);
    };

    OrderPrice.prototype.toBackendPrice = function () {
        return Math.round(this.toCoins() * MATCHER_SCALE);
    };

    function roundToPriceAsset(price, pair) {
        return new Decimal(new Decimal(price).toFixed(pair.priceAsset.precision, Decimal.ROUND_FLOOR));
    }

    function normalizePrice(price, pair) {
        return new Decimal(price)
            .div(MATCHER_SCALE)
            .div(Math.pow(10, pair.priceAsset.precision - pair.amountAsset.precision));
    }

    return {
        fromTokens: function (price, pair) {
            return new OrderPrice(price, pair);
        },

        fromBackendPrice: function (price, pair) {
            var normalizedPrice = normalizePrice(price, pair);

            return new OrderPrice(normalizedPrice, pair);
        }
    };
})();

(function () {
    'use strict';

    function SignService(txConstants, featureConstants, cryptoService, utilityService) {
        var self = this;

        // Transaction types

        self.getAssetIssueTxTypeBytes = function () {
            return [txConstants.ASSET_ISSUE_TRANSACTION_TYPE];
        };

        self.getAssetReissueTxTypeBytes = function () {
            return [txConstants.ASSET_REISSUE_TRANSACTION_TYPE];
        };

        self.getAssetTransferTxTypeBytes = function () {
            return [txConstants.ASSET_TRANSFER_TRANSACTION_TYPE];
        };

        self.getStartLeasingTxTypeBytes = function () {
            return [txConstants.START_LEASING_TRANSACTION_TYPE];
        };

        self.getCancelLeasingTxTypeBytes = function () {
            return [txConstants.CANCEL_LEASING_TRANSACTION_TYPE];
        };

        self.getCreateAliasTxTypeBytes = function () {
            return [txConstants.CREATE_ALIAS_TRANSACTION_TYPE];
        };

        // Keys

        self.getPublicKeyBytes = function (publicKey) {
            return utilityService.base58StringToByteArray(publicKey);
        };

        self.getPrivateKeyBytes = function (privateKey) {
            return cryptoService.base58.decode(privateKey);
        };

        // Data fields

        self.getNetworkBytes = function () {
            return [utilityService.getNetworkIdByte()];
        };

        self.getTransactionIdBytes = function (tx) {
            return utilityService.base58StringToByteArray(tx);
        };

        self.getRecipientBytes = function (recipient) {
            if (recipient.slice(0, 6) === 'alias:') {
                return [].concat(
                    [featureConstants.ALIAS_VERSION],
                    [utilityService.getNetworkIdByte()],
                    utilityService.stringToByteArrayWithSize(recipient.slice(8)) // Remove leading 'asset:W:'
                );
            } else {
                return utilityService.base58StringToByteArray(recipient);
            }
        };

        self.getAssetIdBytes = function (assetId, mandatory) {
            if (mandatory) {
                return utilityService.base58StringToByteArray(assetId);
            } else {
                return assetId ? [1].concat(utilityService.base58StringToByteArray(assetId)) : [0];
            }
        };

        self.getAssetNameBytes = function (assetName) {
            return utilityService.stringToByteArrayWithSize(assetName);
        };

        self.getAssetDescriptionBytes = function (assetDescription) {
            return utilityService.stringToByteArrayWithSize(assetDescription);
        };

        self.getAssetQuantityBytes = function (assetQuantity) {
            return utilityService.longToByteArray(assetQuantity);
        };

        self.getAssetDecimalPlacesBytes = function (assetDecimalPlaces) {
            return [assetDecimalPlaces];
        };

        self.getAssetIsReissuableBytes = function (assetIsReissuable) {
            return utilityService.booleanToBytes(assetIsReissuable);
        };

        self.getAmountBytes = function (amount) {
            return utilityService.longToByteArray(amount);
        };

        self.getFeeAssetIdBytes = function (feeAssetId) {
            return self.getAssetIdBytes(feeAssetId);
        };

        self.getFeeBytes = function (fee) {
            return utilityService.longToByteArray(fee);
        };

        self.getTimestampBytes = function (timestamp) {
            return utilityService.longToByteArray(timestamp);
        };

        self.getAttachmentBytes = function (attachment) {
            return utilityService.byteArrayWithSize(attachment);
        };

        self.getAliasBytes = function (alias) {
            return utilityService.byteArrayWithSize([].concat(
                [featureConstants.ALIAS_VERSION],
                [utilityService.getNetworkIdByte()],
                utilityService.stringToByteArrayWithSize(alias)
            ));
        };

        self.getOrderTypeBytes = function (orderType) {
            return utilityService.booleanToBytes(orderType);
        };

        self.getOrderIdBytes = function (orderId) {
            return utilityService.base58StringToByteArray(orderId);
        };

        // Signatures

        self.buildSignature = function (bytes, privateKey) {
            var privateKeyBytes = self.getPrivateKeyBytes(privateKey);
            return cryptoService.nonDeterministicSign(privateKeyBytes, bytes);
        };
    }

    SignService.$inject = ['constants.transactions', 'constants.features', 'cryptoService', 'utilityService'];

    angular
        .module('waves.core.services')
        .service('signService', SignService);
})();

(function () {
    'use strict';

    angular
        .module('waves.core.services')
        .service('validateService', function () {
            var self = this;

            self.validateSender = function (sender) {
                if (!sender) {
                    throw new Error('Sender hasn\'t been set');
                }

                if (!sender.publicKey) {
                    throw new Error('Sender account public key hasn\'t been set');
                }

                if (!sender.privateKey) {
                    throw new Error('Sender account private key hasn\'t been set');
                }
            };

            self.validateAssetIssue = function (issue) {
                if (angular.isUndefined(issue.name)) {
                    throw new Error('Asset name hasn\'t been set');
                }

                if (angular.isUndefined(issue.totalTokens)) {
                    throw new Error('Total tokens amount hasn\'t been set');
                }

                if (angular.isUndefined(issue.decimalPlaces)) {
                    throw new Error('Token decimal places amount hasn\'t been set');
                }

                if (issue.fee.currency !== Currency.WAVES) {
                    throw new Error('Transaction fee must be nominated in Waves');
                }
            };

            self.validateAssetTransfer = function (transfer) {
                if (angular.isUndefined(transfer.recipient)) {
                    throw new Error('Recipient account hasn\'t been set');
                }

                if (angular.isUndefined(transfer.fee)) {
                    throw new Error('Transaction fee hasn\'t been set');
                }

                if (angular.isUndefined(transfer.amount)) {
                    throw new Error('Transaction amount hasn\'t been set');
                }
            };

            self.validateAssetReissue = function (reissue) {
                if (reissue.totalTokens.currency === Currency.WAVES) {
                    throw new Error('Reissuing Waves is not allowed.');
                }

                if (angular.isUndefined(reissue.totalTokens)) {
                    throw new Error('Total tokens amount hasn\'t been set');
                }

                if (angular.isUndefined(reissue.fee)) {
                    throw new Error('Transaction fee hasn\'t been set');
                }

                if (reissue.fee.currency !== Currency.WAVES) {
                    throw new Error('Transaction fee must be nominated in Waves');
                }
            };
        });
})();
