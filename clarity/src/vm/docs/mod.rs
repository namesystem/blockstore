// Copyright (C) 2013-2020 Blockstack PBC, a public benefit corporation
// Copyright (C) 2020 Stacks Open Internet Foundation
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use super::types::signatures::{FunctionArgSignature, FunctionReturnsSignature};
use crate::vm::analysis::type_checker::v2_1::natives::SimpleNativeFunction;
use crate::vm::analysis::type_checker::v2_1::TypedNativeFunction;
use crate::vm::costs::ExecutionCost;
use crate::vm::functions::define::DefineFunctions;
use crate::vm::functions::NativeFunctions;
use crate::vm::types::signatures::ASCII_40;
use crate::vm::types::{FixedFunction, FunctionType, SequenceSubtype, StringSubtype, Value};
use crate::vm::variables::NativeVariables;
use crate::vm::ClarityVersion;

pub mod contracts;

#[derive(Serialize)]
struct ReferenceAPIs {
    functions: Vec<FunctionAPI>,
    keywords: Vec<KeywordAPI>,
}

#[derive(Serialize, Clone)]
pub struct KeywordAPI {
    pub name: &'static str,
    pub snippet: &'static str,
    pub output_type: &'static str,
    pub description: &'static str,
    pub example: &'static str,
    /// The version where this keyword was first introduced.
    pub min_version: ClarityVersion,
    /// The version where this keyword was disabled.
    pub max_version: Option<ClarityVersion>,
}

#[derive(Serialize, Clone)]
struct SimpleKeywordAPI {
    name: &'static str,
    snippet: &'static str,
    output_type: &'static str,
    description: &'static str,
    example: &'static str,
}

#[derive(Serialize)]
pub struct FunctionAPI {
    pub name: String,
    pub snippet: String,
    pub input_type: String,
    pub output_type: String,
    pub signature: String,
    pub description: String,
    pub example: String,
    /// The version where this keyword was first introduced.
    pub min_version: ClarityVersion,
    /// The version where this keyword was disabled.
    pub max_version: Option<ClarityVersion>,
}

pub struct SimpleFunctionAPI {
    name: Option<&'static str>,
    snippet: &'static str,
    signature: &'static str,
    description: &'static str,
    example: &'static str,
}

struct SpecialAPI {
    output_type: &'static str,
    snippet: &'static str,
    input_type: &'static str,
    signature: &'static str,
    description: &'static str,
    example: &'static str,
}

pub struct DefineAPI {
    output_type: &'static str,
    snippet: &'static str,
    input_type: &'static str,
    signature: &'static str,
    description: &'static str,
    example: &'static str,
}

const BLOCK_HEIGHT: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "block-height",
    snippet: "block-height",
    output_type: "uint",
    description: "Returns the current block height of the Stacks blockchain in Clarity 1 and 2.
Upon activation of epoch 3.0, `block-height` will return the same value as `tenure-height`.
In Clarity 3, `block-height` is removed and has been replaced with `stacks-block-height`.",
    example:
        "(> block-height u1000) ;; returns true if the current block-height has passed 1000 blocks.",
};

const BURN_BLOCK_HEIGHT: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "burn-block-height",
    snippet: "burn-block-height",
    output_type: "uint",
    description: "Returns the current block height of the underlying burn blockchain.",
    example: "(> burn-block-height u832000) ;; returns true if the current height of the underlying burn blockchain has passed 832,000 blocks.",
};

const CONTRACT_CALLER_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "contract-caller",
    snippet: "contract-caller",
    output_type: "principal",
    description: "Returns the caller of the current contract context. If this contract is the first one called by a signed transaction,
the caller will be equal to the signing principal. If `contract-call?` was used to invoke a function from a new contract, `contract-caller`
changes to the _calling_ contract's principal. If `as-contract` is used to change the `tx-sender` context, `contract-caller` _also_ changes
to the same contract principal.",
    example: "(print contract-caller) ;; Will print out a Stacks address of the transaction sender",
};

const STACKS_BLOCK_HEIGHT_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "stacks-block-height",
    snippet: "stacks-block-height",
    output_type: "uint",
    description: "Returns the current block height of the Stacks blockchain.",
    example:
        "(<= stacks-block-height u500000) ;; returns true if the current block-height has not passed 500,000 blocks.",
};

const TENURE_HEIGHT_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "tenure-height",
    snippet: "tenure-height",
    output_type: "uint",
    description: "Returns the number of tenures that have passed.
At the start of epoch 3.0, `tenure-height` will return the same value as `block-height`, then it will continue to increase as each tenures passes.",
    example:
        "(< tenure-height u140000) ;; returns true if the current tenure-height has passed 140,000 blocks.",
};

const TX_SENDER_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "tx-sender",
    snippet: "tx-sender",
    output_type: "principal",
    description: "Returns the original sender of the current transaction, or if `as-contract` was called to modify the sending context, it returns that
contract principal.",
    example: "(print tx-sender) ;; Will print out a Stacks address of the transaction sender",
};

const TX_SPONSOR_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "tx-sponsor?",
    snippet: "tx-sponsor?",
    output_type: "optional principal",
    description: "Returns the sponsor of the current transaction if there is a sponsor, otherwise returns None.",
    example: "(print tx-sponsor?) ;; Will print out an optional value containing the Stacks address of the transaction sponsor",
};

const TOTAL_LIQUID_USTX_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "stx-liquid-supply",
    snippet: "stx-liquid-supply",
    output_type: "uint",
    description: "Returns the total number of micro-STX (uSTX) that are liquid in the system as of this block.",
    example: "(print stx-liquid-supply) ;; Will print out the total number of liquid uSTX",
};

const REGTEST_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "is-in-regtest",
    snippet: "is-in-regtest",
    output_type: "bool",
    description: "Returns whether or not the code is running in a regression test",
    example:
        "(print is-in-regtest) ;; Will print 'true' if the code is running in a regression test",
};

const MAINNET_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "is-in-mainnet",
    snippet: "is-in-mainnet",
    output_type: "bool",
    description: "Returns a boolean indicating whether or not the code is running on the mainnet",
    example: "(print is-in-mainnet) ;; Will print 'true' if the code is running on the mainnet",
};

const CHAINID_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "chain-id",
    snippet: "chain-id",
    output_type: "uint",
    description: "Returns the 32-bit chain ID of the blockchain running this transaction",
    example: "(print chain-id) ;; Will print 'u1' if the code is running on mainnet, and 'u2147483648' on testnet, and other values on different chains.",
};

const NONE_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "none",
    snippet: "none",
    output_type: "(optional ?)",
    description: "Represents the _none_ option indicating no value for a given optional (analogous to a null value).",
    example: "
(define-public (only-if-positive (a int))
  (if (> a 0)
      (some a)
      none))
(only-if-positive 4) ;; Returns (some 4)
(only-if-positive (- 3)) ;; Returns none
",
};

const TRUE_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "true",
    snippet: "true",
    output_type: "bool",
    description: "Boolean true constant.",
    example: "
(and true false) ;; Evaluates to false
(or false true)  ;; Evaluates to true
",
};

const FALSE_KEYWORD: SimpleKeywordAPI = SimpleKeywordAPI {
    name: "false",
    snippet: "false",
    output_type: "bool",
    description: "Boolean false constant.",
    example: "
(and true false) ;; Evaluates to false
(or false true)  ;; Evaluates to true
",
};

const TO_UINT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "to-uint ${1:int}",
    signature: "(to-uint i)",
    description: "Tries to convert the `int` argument to a `uint`. Will cause a runtime error and abort if the supplied argument is negative.",
    example: "(to-uint 238) ;; Returns u238"
};

const TO_INT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "to-int ${1:uint}",
    signature: "(to-int u)",
    description: "Tries to convert the `uint` argument to an `int`. Will cause a runtime error and abort if the supplied argument is >= `pow(2, 127)`",
    example: "(to-int u238) ;; Returns 238"
};

const BUFF_TO_INT_LE_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "buff-to-int-le ${1:buff}",
    signature: "(buff-to-int-le (buff 16))",
    description: "Converts a byte buffer to a signed integer use a little-endian encoding.
The byte buffer can be up to 16 bytes in length. If there are fewer than 16 bytes, as
this function uses a little-endian encoding, the input behaves as if it is
zero-padded on the _right_.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(buff-to-int-le 0x01) ;; Returns 1
(buff-to-int-le 0x01000000000000000000000000000000) ;; Returns 1
(buff-to-int-le 0xffffffffffffffffffffffffffffffff) ;; Returns -1
(buff-to-int-le 0x) ;; Returns 0
"#,
};

const BUFF_TO_UINT_LE_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "buff-to-uint-le ${1:buff}",
    signature: "(buff-to-uint-le (buff 16))",
    description: "Converts a byte buffer to an unsigned integer use a little-endian encoding.
The byte buffer can be up to 16 bytes in length. If there are fewer than 16 bytes, as
this function uses a little-endian encoding, the input behaves as if it is
zero-padded on the _right_.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(buff-to-uint-le 0x01) ;; Returns u1
(buff-to-uint-le 0x01000000000000000000000000000000) ;; Returns u1
(buff-to-uint-le 0xffffffffffffffffffffffffffffffff) ;; Returns u340282366920938463463374607431768211455
(buff-to-uint-le 0x) ;; Returns u0
"#,
};

const BUFF_TO_INT_BE_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "buff-to-int-be ${1:buff}",
    signature: "(buff-to-int-be (buff 16))",
    description: "Converts a byte buffer to a signed integer use a big-endian encoding.
The byte buffer can be up to 16 bytes in length. If there are fewer than 16 bytes, as
this function uses a big-endian encoding, the input behaves as if it is
zero-padded on the _left_.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(buff-to-int-be 0x01) ;; Returns 1
(buff-to-int-be 0x00000000000000000000000000000001) ;; Returns 1
(buff-to-int-be 0xffffffffffffffffffffffffffffffff) ;; Returns -1
(buff-to-int-be 0x) ;; Returns 0
"#,
};

const BUFF_TO_UINT_BE_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "buff-to-uint-be ${1:buff}",
    signature: "(buff-to-uint-be (buff 16))",
    description: "Converts a byte buffer to an unsigned integer use a big-endian encoding.
The byte buffer can be up to 16 bytes in length. If there are fewer than 16 bytes, as
this function uses a big-endian encoding, the input behaves as if it is
zero-padded on the _left_.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(buff-to-uint-be 0x01) ;; Returns u1
(buff-to-uint-be 0x00000000000000000000000000000001) ;; Returns u1
(buff-to-uint-be 0xffffffffffffffffffffffffffffffff) ;; Returns u340282366920938463463374607431768211455
(buff-to-uint-be 0x) ;; Returns u0
"#,
};

const IS_STANDARD_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "is-standard ${1:principal}",
    signature: "(is-standard standard-or-contract-principal)",
    description: "Tests whether `standard-or-contract-principal` _matches_ the current network
type, and therefore represents a principal that can spend tokens on the current
network type. That is, the network is either of type `mainnet`, or `testnet`.
Only `SPxxxx` and `SMxxxx` _c32check form_ addresses can spend tokens on
a mainnet, whereas only `STxxxx` and `SNxxxx` _c32check forms_ addresses can spend
tokens on a testnet. All addresses can _receive_ tokens, but only principal
_c32check form_ addresses that match the network type can _spend_ tokens on the
network.  This method will return `true` if and only if the principal matches
the network type, and false otherwise.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(is-standard 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6) ;; returns true on testnet and false on mainnet
(is-standard 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6.foo) ;; returns true on testnet and false on mainnet
(is-standard 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY) ;; returns true on mainnet and false on testnet
(is-standard 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.foo) ;; returns true on mainnet and false on testnet
(is-standard 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR) ;; returns false on both mainnet and testnet
"#,
};

const PRINCPIPAL_DESTRUCT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "principal-destruct? ${1:principal-address}",
    signature: "(principal-destruct? principal-address)",
    description:  "A principal value represents either a set of keys, or a smart contract.
The former, called a _standard principal_,
is encoded as a `(buff 1)` *version byte*, indicating the type of account
and the type of network that this principal can spend tokens on,
and a `(buff 20)` *public key hash*, characterizing the principal's unique identity.
The latter, a _contract principal_, is encoded as a standard principal concatenated with
a `(string-ascii 40)` *contract name* that identifies the code body.

`principal-destruct?` will decompose a principal into its component parts: either`{version-byte, hash-bytes}`
for standard principals, or `{version-byte, hash-bytes, name}` for contract principals.

This method returns a `Response` that wraps this data as a tuple.

If the version byte of `principal-address` matches the network (see `is-standard`), then this method
returns the pair as its `ok` value.

If the version byte of `principal-address` does not match the network, then this method
returns the pair as its `err` value.

In both cases, the value itself is a tuple containing three fields: a `version` value as a `(buff 1)`,
a `hash-bytes` value as a `(buff 20)`, and a `name` value as an `(optional (string-ascii 40))`.  The `name`
field will only be `(some ..)` if the principal is a contract principal.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(principal-destruct? 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6) ;; Returns (ok (tuple (hash-bytes 0x164247d6f2b425ac5771423ae6c80c754f7172b0) (name none) (version 0x1a)))
(principal-destruct? 'STB44HYPYAT2BB2QE513NSP81HTMYWBJP02HPGK6.foo) ;; Returns (ok (tuple (hash-bytes 0x164247d6f2b425ac5771423ae6c80c754f7172b0) (name (some "foo")) (version 0x1a)))
(principal-destruct? 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY) ;; Returns (err (tuple (hash-bytes 0xfa6bf38ed557fe417333710d6033e9419391a320) (name none) (version 0x16)))
(principal-destruct? 'SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.foo) ;; Returns (err (tuple (hash-bytes 0xfa6bf38ed557fe417333710d6033e9419391a320) (name (some "foo")) (version 0x16)))
"#,
};

const STRING_TO_INT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "string-to-int? ${1:string}",
    signature: "(string-to-int? (string-ascii|string-utf8))",
    description: "Converts a string, either `string-ascii` or `string-utf8`, to an optional-wrapped signed integer.
If the input string does not represent a valid integer, then the function returns `none`. Otherwise it returns
an integer wrapped in `some`.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(string-to-int? "1") ;; Returns (some 1)
(string-to-int? u"-1") ;; Returns (some -1)
(string-to-int? "a") ;; Returns none
"#,
};

const STRING_TO_UINT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "string-to-uint? ${1:string}",
    signature: "(string-to-uint? (string-ascii|string-utf8))",
    description:
        "Converts a string, either `string-ascii` or `string-utf8`, to an optional-wrapped unsigned integer.
If the input string does not represent a valid integer, then the function returns `none`. Otherwise it returns
an unsigned integer wrapped in `some`.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(string-to-uint? "1") ;; Returns (some u1)
(string-to-uint? u"1") ;; Returns (some u1)
(string-to-uint? "a") ;; Returns none
"#,
};

const INT_TO_ASCII_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "int-to-ascii ${1:num}",
    signature: "(int-to-ascii (int|uint))",
    description: "Converts an integer, either `int` or `uint`, to a `string-ascii` string-value representation.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(int-to-ascii 1) ;; Returns "1"
(int-to-ascii u1) ;; Returns "1"
(int-to-ascii -1) ;; Returns "-1"
"#,
};

const INT_TO_UTF8_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "int-to-utf8 ${1:num}",
    signature: "(int-to-utf8 (int|uint))",
    description: "Converts an integer, either `int` or `uint`, to a `string-utf8` string-value representation.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(int-to-utf8 1) ;; Returns u"1"
(int-to-utf8 u1) ;; Returns u"1"
(int-to-utf8 -1) ;; Returns u"-1"
"#,
};

const ADD_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some("+ (add)"),
    snippet: "+ ${1:expr-1} ${2:expr-2}",
    signature: "(+ i1 i2...)",
    description: "Adds a variable number of integer inputs and returns the result. In the event of an _overflow_, throws a runtime error.",
    example: "(+ 1 2 3) ;; Returns 6"
};

const SUB_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some("- (subtract)"),
    snippet: "- ${1:expr-1} ${2:expr-2}",
    signature: "(- i1 i2...)",
    description: "Subtracts a variable number of integer inputs and returns the result. In the event of an _underflow_, throws a runtime error.",
    example: "(- 2 1 1) ;; Returns 0
(- 0 3) ;; Returns -3
"
};

const DIV_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some("/ (divide)"),
    snippet: "/ ${1:expr-1} ${2:expr-2}",
    signature: "(/ i1 i2...)",
    description: "Integer divides a variable number of integer inputs and returns the result. In the event of division by zero, throws a runtime error.",
    example: "(/ 2 3) ;; Returns 0
(/ 5 2) ;; Returns 2
(/ 4 2 2) ;; Returns 1
"
};

const MUL_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some("* (multiply)"),
    snippet: "* ${1:expr-1} ${2:expr-2}",
    signature: "(* i1 i2...)",
    description: "Multiplies a variable number of integer inputs and returns the result. In the event of an _overflow_, throws a runtime error.",
    example: "(* 2 3) ;; Returns 6
(* 5 2) ;; Returns 10
(* 2 2 2) ;; Returns 8
"
};

const MOD_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "mod ${1:expr-1} ${2:expr-2}",
    signature: "(mod i1 i2)",
    description: "Returns the integer remainder from integer dividing `i1` by `i2`. In the event of a division by zero, throws a runtime error.",
    example: "(mod 2 3) ;; Returns 2
(mod 5 2) ;; Returns 1
(mod 7 1) ;; Returns 0
"
};

const POW_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "pow ${1:expr-1} ${2:expr-2}",
    signature: "(pow i1 i2)",
    description: "Returns the result of raising `i1` to the power of `i2`. In the event of an _overflow_, throws a runtime error.
Note: Corner cases are handled with the following rules:
  * if both `i1` and `i2` are `0`, return `1`
  * if `i1` is `1`, return `1`
  * if `i1` is `0`, return `0`
  * if `i2` is `1`, return `i1`
  * if `i2` is negative or greater than `u32::MAX`, throw a runtime error",
    example: "(pow 2 3) ;; Returns 8
(pow 2 2) ;; Returns 4
(pow 7 1) ;; Returns 7
"
};

const SQRTI_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "sqrti ${1:expr-1}",
    signature: "(sqrti n)",
    description: "Returns the largest integer that is less than or equal to the square root of `n`.
Fails on a negative numbers.
",
    example: "(sqrti u11) ;; Returns u3
(sqrti 1000000) ;; Returns 1000
(sqrti u1) ;; Returns u1
(sqrti 0) ;; Returns 0
",
};

const LOG2_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "log2 ${1:expr-1}",
    signature: "(log2 n)",
    description:
        "Returns the power to which the number 2 must be raised to obtain the value `n`, rounded
down to the nearest integer. Fails on a negative numbers.
",
    example: "(log2 u8) ;; Returns u3
(log2 8) ;; Returns 3
(log2 u1) ;; Returns u0
(log2 1000) ;; Returns 9
",
};

const XOR_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "xor ${1:expr-1} ${2:expr-2}",
    signature: "(xor i1 i2)",
    description: "Returns the result of bitwise exclusive or'ing `i1` with `i2`.",
    example: "(xor 1 2) ;; Returns 3
(xor 120 280) ;; Returns 352
",
};

const BITWISE_XOR_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "bit-xor ${1:expr-1} ${2:expr-2}",
    signature: "(bit-xor i1 i2...)",
    description:
        "Returns the result of bitwise exclusive or'ing a variable number of integer inputs.",
    example: "(bit-xor 1 2) ;; Returns 3
(bit-xor 120 280) ;; Returns 352
(bit-xor -128 64) ;; Returns -64
(bit-xor u24 u4) ;; Returns u28
(bit-xor 1 2 4 -1) ;; Returns -8
",
};

const BITWISE_AND_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "bit-and ${1:expr-1} ${2:expr-2}",
    signature: "(bit-and i1 i2...)",
    description: "Returns the result of bitwise and'ing a variable number of integer inputs.",
    example: "(bit-and 24 16) ;; Returns 16
(bit-and 28 24 -1) ;; Returns 24
(bit-and u24 u16) ;; Returns u16
(bit-and -128 -64) ;; Returns -128
(bit-and 28 24 -1) ;; Returns 24
",
};

const BITWISE_OR_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "bit-or ${1:expr-1} ${2:expr-2}",
    signature: "(bit-or i1 i2...)",
    description:
        "Returns the result of bitwise inclusive or'ing a variable number of integer inputs.",
    example: "(bit-or 4 8) ;; Returns 12
(bit-or 1 2 4) ;; Returns 7
(bit-or 64 -32 -16) ;; Returns -16
(bit-or u2 u4 u32) ;; Returns u38
",
};

const BITWISE_NOT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "bit-not ${1:expr-1}",
    signature: "(bit-not i1)",
    description: "Returns the one's compliement (sometimes also called the bitwise compliment or not operator) of `i1`, effectively reversing the bits in `i1`.
In other words, every bit that is `1` in `ì1` will be `0` in the result.  Conversely, every bit that is `0` in `i1` will be `1` in the result.
",
    example: "(bit-not 3) ;; Returns -4
(bit-not u128) ;; Returns u340282366920938463463374607431768211327
(bit-not 128) ;; Returns -129
(bit-not -128) ;; Returns 127
"
};

const BITWISE_LEFT_SHIFT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "bit-shift-left ${1:expr-1} ${2:expr-2}",
    signature: "(bit-shift-left i1 shamt)",
    description: "Shifts all the bits in `i1` to the left by the number of places specified in `shamt` modulo 128 (the bit width of Clarity integers).

Note that there is a deliberate choice made to ignore arithmetic overflow for this operation.  In use cases where overflow should be detected, developers
should use `*`, `/`, and `pow` instead of the shift operators.
",
    example: "(bit-shift-left 2 u1) ;; Returns 4
(bit-shift-left 16 u2) ;; Returns 64
(bit-shift-left -64 u1) ;; Returns -128
(bit-shift-left u4 u2) ;; Returns u16
(bit-shift-left 123 u9999999999) ;; Returns -170141183460469231731687303715884105728
(bit-shift-left u123 u9999999999) ;; Returns u170141183460469231731687303715884105728
(bit-shift-left -1 u7) ;; Returns -128
(bit-shift-left -1 u128) ;; Returns -1
"
};

const BITWISE_RIGHT_SHIFT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "bit-shift-right ${1:expr-1} ${2:expr-2}",
    signature: "(bit-shift-right i1 shamt)",
    description: "Shifts all the bits in `i1` to the right by the number of places specified in `shamt` modulo 128 (the bit width of Clarity integers).
When `i1` is a `uint` (unsigned), new bits are filled with zeros. When `i1` is an `int` (signed), the sign is preserved, meaning that new bits are filled with the value of the previous sign-bit.

Note that there is a deliberate choice made to ignore arithmetic overflow for this operation. In use cases where overflow should be detected, developers should use `*`, `/`, and `pow` instead of the shift operators.
",
    example: "(bit-shift-right 2 u1) ;; Returns 1
(bit-shift-right 128 u2) ;; Returns 32
(bit-shift-right -64 u1) ;; Returns -32
(bit-shift-right u128 u2) ;; Returns u32
(bit-shift-right 123 u9999999999) ;; Returns 0
(bit-shift-right u123 u9999999999) ;; Returns u0
(bit-shift-right -128 u7) ;; Returns -1
(bit-shift-right -256 u1) ;; Returns -128
(bit-shift-right 5 u2) ;; Returns 1
(bit-shift-right -5 u2) ;; Returns -2
"
};

const AND_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "and ${1:expr-1} ${2:expr-2}",
    signature: "(and b1 b2 ...)",
    description: "Returns `true` if all boolean inputs are `true`. Importantly, the supplied arguments are
evaluated in-order and lazily. Lazy evaluation means that if one of the arguments returns `false`, the function
short-circuits, and no subsequent arguments are evaluated.
",
    example: "(and true false) ;; Returns false
(and (is-eq (+ 1 2) 1) (is-eq 4 4)) ;; Returns false
(and (is-eq (+ 1 2) 3) (is-eq 4 4)) ;; Returns true
"
};

const OR_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "or ${1:expr-1} ${2:expr-2}",
    signature: "(or b1 b2 ...)",
    description: "Returns `true` if any boolean inputs are `true`. Importantly, the supplied arguments are
evaluated in-order and lazily. Lazy evaluation means that if one of the arguments returns `true`, the function
short-circuits, and no subsequent arguments are evaluated.",
    example: "(or true false) ;; Returns true
(or (is-eq (+ 1 2) 1) (is-eq 4 4)) ;; Returns true
(or (is-eq (+ 1 2) 1) (is-eq 3 4)) ;; Returns false
(or (is-eq (+ 1 2) 3) (is-eq 4 4)) ;; Returns true
"
};

const NOT_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "not ${1:expr-1}",
    signature: "(not b1)",
    description: "Returns the inverse of the boolean input.",
    example: "(not true) ;; Returns false
(not (is-eq 1 2)) ;; Returns true
",
};

const GEQ_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some(">= (greater than or equal)"),
    snippet: ">= ${1:expr-1} ${2:expr-2}",
    signature: "(>= i1 i2)",
    description: "Compares two integers, returning `true` if `i1` is greater than or equal to `i2` and `false` otherwise.
i1 and i2 must be of the same type. Starting with Stacks 1.0, the `>=`-comparable types are `int` and `uint`. Starting with Stacks 2.1,
the `>=`-comparable types are expanded to include `string-ascii`, `string-utf8` and `buff`.
    ",
    example: r#"(>= 1 1) ;; Returns true
(>= 5 2) ;; Returns true
(>= "baa" "aaa") ;; Returns true
(>= "aaa" "aa") ;; Returns true
(>= 0x02 0x01) ;; Returns true
(>= 5 u2) ;; Throws type error
"#
};

const LEQ_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some("<= (less than or equal)"),
    snippet: "<= ${1:expr-1} ${2:expr-2}",
    signature: "(<= i1 i2)",
    description: "Compares two integers, returning true if `i1` is less than or equal to `i2` and `false` otherwise.
i1 and i2 must be of the same type. Starting with Stacks 1.0, the `<=`-comparable types are `int` and `uint`. Starting with Stacks 2.1,
the `<=`-comparable types are expanded to include `string-ascii`, `string-utf8` and `buff`.",
    example: r#"(<= 1 1) ;; Returns true
(<= 5 2) ;; Returns false
(<= "aaa" "baa") ;; Returns true
(<= "aa" "aaa") ;; Returns true
(<= 0x01 0x02) ;; Returns true
(<= 5 u2) ;; Throws type error
"#
};

const GREATER_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some("> (greater than)"),
    snippet: "> ${1:expr-1} ${2:expr-2}",
    signature: "(> i1 i2)",
    description:
        "Compares two integers, returning `true` if `i1` is greater than `i2` and false otherwise.
i1 and i2 must be of the same type. Starting with Stacks 1.0, the `>`-comparable types are `int` and `uint`. Starting with Stacks 2.1,
the `>`-comparable types are expanded to include `string-ascii`, `string-utf8` and `buff`.",
    example: r#"(> 1 2) ;; Returns false
(> 5 2) ;; Returns true
(> "baa" "aaa") ;; Returns true
(> "aaa" "aa") ;; Returns true
(> 0x02 0x01) ;; Returns true
(> 5 u2) ;; Throws type error
"#,
};

const LESS_API: SimpleFunctionAPI = SimpleFunctionAPI {
    name: Some("< (less than)"),
    snippet: "< ${1:expr-1} ${2:expr-2}",
    signature: "(< i1 i2)",
    description:
        "Compares two integers, returning `true` if `i1` is less than `i2` and `false` otherwise.
i1 and i2 must be of the same type. Starting with Stacks 1.0, the `<`-comparable types are `int` and `uint`. Starting with Stacks 2.1,
the `<`-comparable types are expanded to include `string-ascii`, `string-utf8` and `buff`.",
    example: r#"(< 1 2) ;; Returns true
(< 5 2) ;; Returns false
(< "aaa" "baa") ;; Returns true
(< "aa" "aaa") ;; Returns true
(< 0x01 0x02) ;; Returns true
(< 5 u2) ;; Throws type error
"#,
};

pub fn get_input_type_string(function_type: &FunctionType) -> String {
    match function_type {
        FunctionType::Variadic(ref in_type, _) => format!("{}, ...", in_type),
        FunctionType::Fixed(FixedFunction { ref args, .. }) => {
            let in_types: Vec<String> = args.iter().map(|x| format!("{}", x.signature)).collect();
            in_types.join(", ")
        }
        FunctionType::UnionArgs(ref in_types, _) => {
            let in_types: Vec<String> = in_types.iter().map(|x| format!("{}", x)).collect();
            in_types.join(" | ")
        }
        FunctionType::ArithmeticVariadic => "int, ... | uint, ...".to_string(),
        FunctionType::ArithmeticUnary => "int | uint".to_string(),
        FunctionType::ArithmeticBinary | FunctionType::ArithmeticComparison => {
            "int, int | uint, uint | string-ascii, string-ascii | string-utf8, string-utf8 | buff, buff".to_string()
        },
        FunctionType::Binary(ref left_sig, ref right_sig, _) => {
            let mut in_types: Vec<String> = Vec::new();
            match left_sig {
                FunctionArgSignature::Single(left) => {
                    match right_sig {
                        FunctionArgSignature::Single(right) => {
                            in_types.push(format!("{}, {}", left, right));
                        },
                        FunctionArgSignature::Union(right_types) => {
                            for right in right_types.iter() {
                                in_types.push(format!("{}, {}", left, right));
                            }
                        }
                    }
                },
                FunctionArgSignature::Union(left_types) => {
                    for left in left_types.iter() {
                        match right_sig {
                            FunctionArgSignature::Single(right) => {
                                in_types.push(format!("{}, {}", left, right));
                            },
                            FunctionArgSignature::Union(right_types) => {
                                for right in right_types.iter() {
                                    in_types.push(format!("{}, {}", left, right));
                                }
                            }
                        }
                    }
                }
            }
            in_types.join(" | ")
        }
    }
}

#[allow(clippy::panic)]
pub fn get_output_type_string(function_type: &FunctionType) -> String {
    match function_type {
        FunctionType::Variadic(_, ref out_type) => format!("{}", out_type),
        FunctionType::Fixed(FixedFunction { ref returns, .. }) => format!("{}", returns),
        FunctionType::UnionArgs(_, ref out_type) => format!("{}", out_type),
        FunctionType::ArithmeticVariadic
        | FunctionType::ArithmeticUnary
        | FunctionType::ArithmeticBinary => "int | uint".to_string(),
        FunctionType::ArithmeticComparison => "bool".to_string(),
        FunctionType::Binary(left, right, ref out_sig) => match out_sig {
            FunctionReturnsSignature::Fixed(out_type) => format!("{}", out_type),
            FunctionReturnsSignature::TypeOfArgAtPosition(pos) => {
                let arg_sig = match pos {
                    0 => left,
                    1 => right,
                    _ => panic!("Index out of range: TypeOfArgAtPosition for FunctionType::Binary can only handle two arguments, zero-indexed (0 or 1).")
                };

                match arg_sig {
                    FunctionArgSignature::Single(arg_type) => arg_type.to_string(),
                    FunctionArgSignature::Union(arg_types) => arg_types
                        .iter()
                        .map(ToString::to_string)
                        .collect::<Vec<_>>()
                        .join(" | "),
                }
            }
        },
    }
}

pub fn get_signature(function_name: &str, function_type: &FunctionType) -> Option<String> {
    if let FunctionType::Fixed(FixedFunction { ref args, .. }) = function_type {
        let in_names: Vec<String> = args.iter().map(|x| x.name.to_string()).collect();
        let arg_examples = in_names.join(" ");
        Some(format!(
            "({}{}{})",
            function_name,
            if arg_examples.is_empty() { "" } else { " " },
            arg_examples
        ))
    } else {
        None
    }
}

#[allow(clippy::expect_used)]
#[allow(clippy::panic)]
fn make_for_simple_native(
    api: &SimpleFunctionAPI,
    function: &NativeFunctions,
    name: String,
) -> FunctionAPI {
    let (input_type, output_type) = {
        if let TypedNativeFunction::Simple(SimpleNativeFunction(function_type)) =
            TypedNativeFunction::type_native_function(function)
                .expect("Failed to type a native function")
        {
            let input_type = get_input_type_string(&function_type);
            let output_type = get_output_type_string(&function_type);
            (input_type, output_type)
        } else {
            panic!(
                "Attempted to auto-generate docs for non-simple native function: {:?}",
                name
            )
        }
    };

    FunctionAPI {
        name: api.name.map_or(name, |x| x.to_string()),
        snippet: api.snippet.to_string(),
        input_type,
        output_type,
        signature: api.signature.to_string(),
        description: api.description.to_string(),
        example: api.example.to_string(),
        min_version: function.get_min_version(),
        max_version: function.get_max_version(),
    }
}

const EQUALS_API: SpecialAPI = SpecialAPI {
    input_type: "A, A, ...",
    snippet: "is-eq ${1:expr-1} ${2:expr-2}",
    output_type: "bool",
    signature: "(is-eq v1 v2...)",
    description: "Compares the inputted values, returning `true` if they are all equal. Note that
_unlike_ the `(and ...)` function, `(is-eq ...)` will _not_ short-circuit. All values supplied to
is-eq _must_ be the same type.",
    example: "(is-eq 1 1) ;; Returns true
(is-eq true false) ;; Returns false
(is-eq \"abc\" 234 234) ;; Throws type error
(is-eq \"abc\" \"abc\") ;; Returns true
(is-eq 0x0102 0x0102) ;; Returns true
",
};

const IF_API: SpecialAPI = SpecialAPI {
    input_type: "bool, A, A",
    snippet: "if ${1:condition} ${2:expr-if-true} ${3:expr-if-false}",
    output_type: "A",
    signature: "(if bool1 expr1 expr2)",
    description: "The `if` function admits a boolean argument and two expressions
which must return the same type. In the case that the boolean input is `true`, the
`if` function evaluates and returns `expr1`. If the boolean input is `false`, the
`if` function evaluates and returns `expr2`.",
    example: "(if true 1 2) ;; Returns 1
(if (> 1 2) 1 2) ;; Returns 2",
};

const LET_API: SpecialAPI = SpecialAPI {
    input_type: "((name1 AnyType) (name2 AnyType) ...), AnyType, ... A",
    snippet: "let ((${1:name-1} ${2:val-1})) ${3:expr-1}",
    output_type: "A",
    signature: "(let ((name1 expr1) (name2 expr2) ...) expr-body1 expr-body2 ... expr-body-last)",
    description: "The `let` function accepts a list of `variable name` and `expression` pairs,
evaluating each expression and _binding_ it to the corresponding variable name.
`let` bindings are sequential: when a `let` binding is evaluated, it may refer to prior binding.
The _context_ created by this set of bindings is used for evaluating its body expressions.
The let expression returns the value of the last such body expression.

Note: intermediary statements returning a response type must be checked",
    example: "(let ((a 2) (b (+ 5 6 7))) (print a) (print b) (+ a b)) ;; Returns 20
(let ((a 5) (c (+ a 1)) (d (+ c 1)) (b (+ a c d))) (print a) (print b) (+ a b)) ;; Returns 23",
};

const FETCH_VAR_API: SpecialAPI = SpecialAPI {
    input_type: "VarName",
    snippet: "var-get ${1:var}",
    output_type: "A",
    signature: "(var-get var-name)",
    description: "The `var-get` function looks up and returns an entry from a contract's data map.
The value is looked up using `var-name`.",
    example: "(define-data-var cursor int 6)
(var-get cursor) ;; Returns 6",
};

const SET_VAR_API: SpecialAPI = SpecialAPI {
    input_type: "VarName, AnyType",
    snippet: "var-set ${1:var} ${2:value}",
    output_type: "bool",
    signature: "(var-set var-name expr1)",
    description: "The `var-set` function sets the value associated with the input variable to the
inputted value. The function always returns `true`.",
    example: "
(define-data-var cursor int 6)
(var-get cursor) ;; Returns 6
(var-set cursor (+ (var-get cursor) 1)) ;; Returns true
(var-get cursor) ;; Returns 7",
};

const MAP_API: SpecialAPI = SpecialAPI {
    input_type: "Function(A, B, ..., N) -> X, sequence_A, sequence_B, ..., sequence_N",
    snippet: "map ${1:func} ${2:sequence}",
    output_type: "(list X)",
    signature: "(map func sequence_A sequence_B ... sequence_N)",
    description: "The `map` function applies the function `func` to each corresponding element of the input sequences,
and outputs a _list_ of the same type containing the outputs from those function applications.
Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`,
for which the corresponding element types are, respectively, `A`, `(buff 1)`, `(string-ascii 1)` and `(string-utf8 1)`.
The `func` argument must be a literal function name.

Note: no matter what kind of sequences the inputs are, the output is always a list.",
    example: r#"
(map not (list true false true false)) ;; Returns (false true false true)
(map + (list 1 2 3) (list 1 2 3) (list 1 2 3)) ;; Returns (3 6 9)
(define-private (a-or-b (char (string-utf8 1))) (if (is-eq char u"a") u"a" u"b"))
(map a-or-b u"aca") ;; Returns (u"a" u"b" u"a")
(define-private (zero-or-one (char (buff 1))) (if (is-eq char 0x00) 0x00 0x01))
(map zero-or-one 0x000102) ;; Returns (0x00 0x01 0x01)
"#,
};

const FILTER_API: SpecialAPI = SpecialAPI {
    input_type: "Function(A) -> bool, sequence_A",
    snippet: "filter ${1:func} ${2:sequence}",
    output_type: "sequence_A",
    signature: "(filter func sequence)",
    description: "The `filter` function applies the input function `func` to each element of the
input sequence, and returns the same sequence with any elements removed for which `func` returned `false`.
Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`,
for which the corresponding element types are, respectively, `A`, `(buff 1)`, `(string-ascii 1)` and `(string-utf8 1)`.
The `func` argument must be a literal function name.
",
    example: r#"
(filter not (list true false true false)) ;; Returns (false false)
(define-private (is-a (char (string-utf8 1))) (is-eq char u"a"))
(filter is-a u"acabd") ;; Returns u"aa"
(define-private (is-zero (char (buff 1))) (is-eq char 0x00))
(filter is-zero 0x00010002) ;; Returns 0x0000
"#,
};

const FOLD_API: SpecialAPI = SpecialAPI {
    input_type: "Function(A, B) -> B, sequence_A, B",
    snippet: "fold ${1:func} ${2:sequence} ${3:initial-value}",
    output_type: "B",
    signature: "(fold func sequence_A initial_B)",
    description: "The `fold` function condenses `sequence_A` into a value of type
`B` by recursively applies the function `func` to each element of the
input sequence _and_ the output of a previous application of `func`.

`fold` uses `initial_B` in the initial application of `func`, along with the
first element of `sequence_A`. The resulting value of type `B` is used for the
next application of `func`, along with the next element of `sequence_A` and so
on. `fold` returns the last value of type `B` returned by these successive
applications `func`.

Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`,
for which the corresponding element types are, respectively, `A`, `(buff 1)`, `(string-ascii 1)` and `(string-utf8 1)`.
The `func` argument must be a literal function name.
",
    example: r#"
(fold * (list 2 2 2) 1) ;; Returns 8
(fold * (list 2 2 2) 0) ;; Returns 0
;; calculates (- 11 (- 7 (- 3 2)))
(fold - (list 3 7 11) 2) ;; Returns 5
(define-private (concat-string (a (string-ascii 20)) (b (string-ascii 20))) (unwrap-panic (as-max-len? (concat a b) u20)))
(fold concat-string "cdef" "ab")   ;; Returns "fedcab"
(fold concat-string (list "cd" "ef") "ab")   ;; Returns "efcdab"
(define-private (concat-buff (a (buff 20)) (b (buff 20))) (unwrap-panic (as-max-len? (concat a b) u20)))
(fold concat-buff 0x03040506 0x0102)   ;; Returns 0x060504030102
"#,
};

const CONCAT_API: SpecialAPI = SpecialAPI {
    input_type: "sequence_A, sequence_A",
    snippet: "concat ${1:sequence-1} ${2:sequence-2}",
    output_type: "sequence_A",
    signature: "(concat sequence1 sequence2)",
    description: "The `concat` function takes two sequences of the same type,
and returns a concatenated sequence of the same type, with the resulting
sequence_len = sequence1_len + sequence2_len.
Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`.
",
    example: r#"
(concat (list 1 2) (list 3 4)) ;; Returns (1 2 3 4)
(concat "hello " "world") ;; Returns "hello world"
(concat 0x0102 0x0304) ;; Returns 0x01020304
"#,
};

const APPEND_API: SpecialAPI = SpecialAPI {
    input_type: "list A, A",
    snippet: "append ${1:list} ${2:element}",
    output_type: "list",
    signature: "(append (list 1 2 3 4) 5)",
    description: "The `append` function takes a list and another value with the same entry type,
and outputs a list of the same type with max_len += 1.",
    example: "(append (list 1 2 3 4) 5) ;; Returns (1 2 3 4 5)",
};

const ASSERTS_MAX_LEN_API: SpecialAPI = SpecialAPI {
    input_type: "sequence_A, uint",
    snippet: "as-max-len? ${1:sequence} ${2:max-len}",
    output_type: "(optional sequence_A)",
    signature: "(as-max-len? sequence max_length)",
    description:
        "The `as-max-len?` function takes a sequence argument and a uint-valued, literal length argument.
The function returns an optional type. If the input sequence length is less than
or equal to the supplied max_length, this returns `(some sequence)`, otherwise it returns `none`.
Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`.
",
    example: r#"
(as-max-len? (list 2 2 2) u3) ;; Returns (some (2 2 2))
(as-max-len? (list 1 2 3) u2) ;; Returns none
(as-max-len? "hello" u10) ;; Returns (some "hello")
(as-max-len? 0x010203 u10) ;; Returns (some 0x010203)
"#,
};

const LEN_API: SpecialAPI = SpecialAPI {
    input_type: "sequence_A",
    snippet: "len ${1:sequence}",
    output_type: "uint",
    signature: "(len sequence)",
    description: "The `len` function returns the length of a given sequence.
Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`.
    ",
    example: r#"
(len "blockstack") ;; Returns u10
(len (list 1 2 3 4 5)) ;; Returns u5
(len 0x010203) ;; Returns u3
"#,
};

const ELEMENT_AT_API: SpecialAPI = SpecialAPI {
    input_type: "sequence_A, uint",
    snippet: "element-at? ${1:sequence} ${2:index}",
    output_type: "(optional A)",
    signature: "(element-at? sequence index)",
    description: "The `element-at?` function returns the element at `index` in the provided sequence.
Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`,
for which the corresponding element types are, respectively, `A`, `(buff 1)`, `(string-ascii 1)` and `(string-utf8 1)`.

In Clarity1, `element-at` must be used (without the `?`). The `?` is added in Clarity2 for consistency -- built-ins that return responses or optionals end in `?`. The Clarity1 spelling is left as an alias in Clarity2 for backwards compatibility.
",
    example: r#"
(element-at? "blockstack" u5) ;; Returns (some "s")
(element-at? (list 1 2 3 4 5) u5) ;; Returns none
(element-at? (list 1 2 3 4 5) (+ u1 u2)) ;; Returns (some 4)
(element-at? "abcd" u1) ;; Returns (some "b")
(element-at? 0xfb01 u1) ;; Returns (some 0x01)
"#,
};

const INDEX_OF_API: SpecialAPI = SpecialAPI {
    input_type: "sequence_A, A",
    snippet: "index-of? ${1:sequence} ${2:item}",
    output_type: "(optional uint)",
    signature: "(index-of? sequence item)",
    description: "The `index-of?` function returns the first index at which `item` can be
found, using `is-eq` checks, in the provided sequence.
Applicable sequence types are `(list A)`, `buff`, `string-ascii` and `string-utf8`,
for which the corresponding element types are, respectively, `A`, `(buff 1)`, `(string-ascii 1)` and `(string-utf8 1)`.
If the target item is not found in the sequence (or if an empty string or buffer is
supplied), this function returns `none`.

In Clarity1, `index-of` must be used (without the `?`). The `?` is added in Clarity2 for consistency -- built-ins that return responses or optionals end in `?`. The Clarity1 spelling is left as an alias in Clarity2 for backwards compatibility.
",
    example: r#"
(index-of? "blockstack" "b") ;; Returns (some u0)
(index-of? "blockstack" "k") ;; Returns (some u4)
(index-of? "blockstack" "") ;; Returns none
(index-of? (list 1 2 3 4 5) 6) ;; Returns none
(index-of? 0xfb01 0x01) ;; Returns (some u1)
"#,
};

const SLICE_API: SpecialAPI = SpecialAPI {
    input_type: "sequence_A, uint, uint",
    snippet: "slice? ${1:sequence} ${2:left-pos} ${3:right-pos}",
    output_type: "(optional sequence_A)",
    signature: "(slice? sequence left-position right-position)",
    description:
        "The `slice?` function attempts to return a sub-sequence of that starts at `left-position` (inclusive), and
ends at `right-position` (non-inclusive).
If `left_position`==`right_position`, the function returns an empty sequence.
If either `left_position` or `right_position` are out of bounds OR if `right_position` is less than
`left_position`, the function returns `none`.",
    example: "(slice? \"blockstack\" u5 u10) ;; Returns (some \"stack\")
(slice? (list 1 2 3 4 5) u5 u9) ;; Returns none
(slice? (list 1 2 3 4 5) u3 u4) ;; Returns (some (4))
(slice? \"abcd\" u1 u3) ;; Returns (some \"bc\")
(slice? \"abcd\" u2 u2) ;; Returns (some \"\")
(slice? \"abcd\" u3 u1) ;; Returns none
",
};

const LIST_API: SpecialAPI = SpecialAPI {
    input_type: "A, ...",
    snippet: "list ${1:expr-1} ${2:expr-2}",
    output_type: "(list A)",
    signature: "(list expr1 expr2 expr3 ...)",
    description: "The `list` function constructs a list composed of the inputted values. Each
supplied value must be of the same type.",
    example: "(list (+ 1 2) 4 5) ;; Returns (3 4 5)",
};

const BEGIN_API: SpecialAPI = SpecialAPI {
    input_type: "AnyType, ... A",
    snippet: "begin ${1:expr-1} ${2:expr-2}",
    output_type: "A",
    signature: "(begin expr1 expr2 expr3 ... expr-last)",
    description: "The `begin` function evaluates each of its input expressions, returning the
return value of the last such expression.

Note: intermediary statements returning a response type must be checked.",
    example: "(begin (+ 1 2) 4 5) ;; Returns 5",
};

const PRINT_API: SpecialAPI = SpecialAPI {
    input_type: "A",
    snippet: "print ${1:expr}",
    output_type: "A",
    signature: "(print expr)",
    description: "The `print` function evaluates and returns its input expression. On Stacks Core
nodes configured for development (as opposed to production mining nodes), this function prints the resulting value to `STDOUT` (standard output).",
    example: "(print (+ 1 2 3)) ;; Returns 6",
};

const FETCH_ENTRY_API: SpecialAPI = SpecialAPI {
    input_type: "MapName, tuple",
    snippet: "map-get? ${1:map-name} ${2:key-tuple}",
    output_type: "(optional (tuple))",
    signature: "(map-get? map-name key-tuple)",
    description: "The `map-get?` function looks up and returns an entry from a contract's data map.
The value is looked up using `key-tuple`.
If there is no value associated with that key in the data map, the function returns a `none` option. Otherwise,
it returns `(some value)`.",
    example: "(define-map names-map { name: (string-ascii 10) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 })
(map-get? names-map (tuple (name \"blockstack\"))) ;; Returns (some (tuple (id 1337)))
(map-get? names-map { name: \"blockstack\" }) ;; Same command, using a shorthand for constructing the tuple
",
};

const SET_ENTRY_API: SpecialAPI = SpecialAPI {
    input_type: "MapName, tuple_A, tuple_B",
    snippet: "map-set ${1:map-name} ${2:key-tuple} ${3:value-tuple}",
    output_type: "bool",
    signature: "(map-set map-name key-tuple value-tuple)",
    description: "The `map-set` function sets the value associated with the input key to the
inputted value. This function performs a _blind_ update; whether or not a value is already associated
with the key, the function overwrites that existing association.

Note: the `value-tuple` requires 1 additional byte for storage in the materialized blockchain state,
and therefore the maximum size of a value that may be inserted into a map is MAX_CLARITY_VALUE - 1.",
    example: "(define-map names-map { name: (string-ascii 10) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 }) ;; Returns true
(map-set names-map (tuple (name \"blockstack\")) (tuple (id 1337))) ;; Same command, using a shorthand for constructing the tuple
",
};

const INSERT_ENTRY_API: SpecialAPI = SpecialAPI {
    input_type: "MapName, tuple_A, tuple_B",
    snippet: "map-insert ${1:map-name} ${2:key-tuple} ${3:value-tuple}",
    output_type: "bool",
    signature: "(map-insert map-name key-tuple value-tuple)",
    description: "The `map-insert` function sets the value associated with the input key to the
inputted value if and only if there is not already a value associated with the key in the map.
If an insert occurs, the function returns `true`. If a value already existed for
this key in the data map, the function returns `false`.

Note: the `value-tuple` requires 1 additional byte for storage in the materialized blockchain state,
and therefore the maximum size of a value that may be inserted into a map is MAX_CLARITY_VALUE - 1.",
    example: "(define-map names-map { name: (string-ascii 10) } { id: int })
(map-insert names-map { name: \"blockstack\" } { id: 1337 }) ;; Returns true
(map-insert names-map { name: \"blockstack\" } { id: 1337 }) ;; Returns false
(map-insert names-map (tuple (name \"blockstack\")) (tuple (id 1337))) ;; Same command, using a shorthand for constructing the tuple
",
};

const DELETE_ENTRY_API: SpecialAPI = SpecialAPI {
    input_type: "MapName, tuple",
    snippet: "map-delete ${1:map-name} ${2:key-tuple}",
    output_type: "bool",
    signature: "(map-delete map-name key-tuple)",
    description: "The `map-delete` function removes the value associated with the input key for
the given map. If an item exists and is removed, the function returns `true`.
If a value did not exist for this key in the data map, the function returns `false`.",
    example: "(define-map names-map { name: (string-ascii 10) } { id: int })
(map-insert names-map { name: \"blockstack\" } { id: 1337 }) ;; Returns true
(map-delete names-map { name: \"blockstack\" }) ;; Returns true
(map-delete names-map { name: \"blockstack\" }) ;; Returns false
(map-delete names-map (tuple (name \"blockstack\"))) ;; Same command, using a shorthand for constructing the tuple
",
};

const TUPLE_CONS_API: SpecialAPI = SpecialAPI {
    input_type: "(key-name A), (key-name-2 B), ...",
    snippet: "tuple (${1:key-1} ${2:val-1})",
    output_type: "(tuple (key-name A) (key-name-2 B) ...)",
    signature: "(tuple (key0 expr0) (key1 expr1) ...)",
    description: "The `tuple` special form constructs a typed tuple from the supplied key and expression pairs.
A `get` function can use typed tuples as input to select specific values from a given tuple.
Key names may not appear multiple times in the same tuple definition. Supplied expressions are evaluated and
associated with the expressions' paired key name.

There is a shorthand using curly brackets of the form {key0: expr0, key1: expr, ...}",
    example: "(tuple (name \"blockstack\") (id 1337)) ;; using tuple
    {name: \"blockstack\", id: 1337} ;; using curly brackets",
};

const TUPLE_GET_API: SpecialAPI = SpecialAPI {
    input_type: "KeyName, (tuple) | (optional (tuple))",
    snippet: "get ${1:key-name} ${2:tuple}",
    output_type: "A",
    signature: "(get key-name tuple)",
    description: "The `get` function fetches the value associated with a given key from the supplied typed tuple.
If an `Optional` value is supplied as the inputted tuple, `get` returns an `Optional` type of the specified key in
the tuple. If the supplied option is a `none` option, get returns `none`.",
    example: "(define-map names-map { name: (string-ascii 12) } { id: int })
(map-insert names-map { name: \"blockstack\" } { id: 1337 }) ;; Returns true
(get id (tuple (name \"blockstack\") (id 1337))) ;; Returns 1337
(get id (map-get? names-map (tuple (name \"blockstack\")))) ;; Returns (some 1337)
(get id (map-get? names-map (tuple (name \"non-existent\")))) ;; Returns none
"
};

const TUPLE_MERGE_API: SpecialAPI = SpecialAPI {
    input_type: "tuple, tuple",
    snippet: "merge ${1:tuple-1} ${2:tuple-2}",
    output_type: "tuple",
    signature: "(merge tuple { key1: val1 })",
    description: "The `merge` function returns a new tuple with the combined fields, without mutating the supplied tuples.",
    example: "(define-map users { id: int } { name: (string-ascii 12), address: (optional principal) })
(map-insert users { id: 1337 } { name: \"john\", address: none }) ;; Returns true
(let ((user (unwrap-panic (map-get? users { id: 1337 }))))
    (merge user { address: (some 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) })) ;; Returns (tuple (address (some SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)) (name \"john\"))"
};

const HASH160_API: SpecialAPI = SpecialAPI {
    input_type: "buff|uint|int",
    snippet: "hash160 ${1:buff}",
    output_type: "(buff 20)",
    signature: "(hash160 value)",
    description: "The `hash160` function computes `RIPEMD160(SHA256(x))` of the inputted value.
If an integer (128 bit) is supplied the hash is computed over the little-endian representation of the
integer.",
    example: "(hash160 0) ;; Returns 0xe4352f72356db555721651aa612e00379167b30f"
};

const SHA256_API: SpecialAPI = SpecialAPI {
    input_type: "buff|uint|int",
    snippet: "sha256 ${1:buff}",
    output_type: "(buff 32)",
    signature: "(sha256 value)",
    description: "The `sha256` function computes `SHA256(x)` of the inputted value.
If an integer (128 bit) is supplied the hash is computed over the little-endian representation of the
integer.",
    example: "(sha256 0) ;; Returns 0x374708fff7719dd5979ec875d56cd2286f6d3cf7ec317a3b25632aab28ec37bb"
};

const SHA512_API: SpecialAPI = SpecialAPI {
    input_type: "buff|uint|int",
    snippet: "sha512 ${1:buff}",
    output_type: "(buff 64)",
    signature: "(sha512 value)",
    description: "The `sha512` function computes `SHA512(x)` of the inputted value.
If an integer (128 bit) is supplied the hash is computed over the little-endian representation of the
integer.",
    example: "(sha512 1) ;; Returns 0x6fcee9a7b7a7b821d241c03c82377928bc6882e7a08c78a4221199bfa220cdc55212273018ee613317c8293bb8d1ce08d1e017508e94e06ab85a734c99c7cc34",
};

const SHA512T256_API: SpecialAPI = SpecialAPI {
    input_type: "buff|uint|int",
    snippet: "sha512/256 ${1:buff}",
    output_type: "(buff 32)",
    signature: "(sha512/256 value)",
    description: "The `sha512/256` function computes `SHA512/256(x)` (the SHA512 algorithm with the 512/256 initialization vector, truncated
to 256 bits) of the inputted value.
If an integer (128 bit) is supplied the hash is computed over the little-endian representation of the
integer.",
    example: "(sha512/256 1) ;; Returns 0x515a7e92e7c60522db968d81ff70b80818fc17aeabbec36baf0dda2812e94a86",
};

const KECCAK256_API: SpecialAPI = SpecialAPI {
    input_type: "buff|uint|int",
    snippet: "keccak256 ${1:buff}",
    output_type: "(buff 32)",
    signature: "(keccak256 value)",
    description: "The `keccak256` function computes `KECCAK256(value)` of the inputted value.

Note: this differs from the `NIST SHA-3` (that is, FIPS 202) standard. If an integer (128 bit)
is supplied the hash is computed over the little-endian representation of the integer.",
    example: "(keccak256 0) ;; Returns 0xf490de2920c8a35fabeb13208852aa28c76f9be9b03a4dd2b3c075f7a26923b4"
};

const SECP256K1RECOVER_API: SpecialAPI = SpecialAPI {
    input_type: "(buff 32), (buff 65)",
    snippet: "secp256k1-recover? ${1:message-hash} ${2:signature}",
    output_type: "(response (buff 33) uint)",
    signature: "(secp256k1-recover? message-hash signature)",
    description: "The `secp256k1-recover?` function recovers the public key used to sign the message whose sha256 is `message-hash`
with the provided `signature`. The signature includes 64 bytes plus an additional recovery id (00..03) for a total of 65 bytes.
On success, it returns the public key as a 33-byte buffer. This function may fail with one of the following error codes:

* `(err u1)` - the signature does not match the message hash
* `(err u2)` - the signature is invalid
",
    example: "(secp256k1-recover? 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301)
 ;; Returns (ok 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110)"
};

const SECP256K1VERIFY_API: SpecialAPI = SpecialAPI {
    input_type: "(buff 32), (buff 64) | (buff 65), (buff 33)",
    snippet: "secp256k1-verify ${1:message-hash} ${2:signature} ${3:public-key})",
    output_type: "bool",
    signature: "(secp256k1-verify message-hash signature public-key)",
    description: "The `secp256k1-verify` function verifies that the provided signature of the message-hash
was signed with the private key that generated the public key.
The `message-hash` is the `sha256` of the message.
The signature includes 64 bytes plus an optional additional recovery id (00..03) for a total of 64 or 65 bytes.",
    example: "(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a1301
 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110) ;; Returns true
(secp256k1-verify 0xde5b9eb9e7c5592930eb2e30a01369c36586d872082ed8181ee83d2a0ec20f04
 0x8738487ebe69b93d8e51583be8eee50bb4213fc49c767d329632730cc193b873554428fc936ca3569afc15f1c9365f6591d6251a89fee9c9ac661116824d3a13
 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110) ;; Returns true
(secp256k1-verify 0x0000000000000000000000000000000000000000000000000000000000000000
 0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110) ;; Returns false"
};

const CONTRACT_CALL_API: SpecialAPI = SpecialAPI {
    input_type: "ContractName, PublicFunctionName, Arg0, ...",
    snippet: "contract-call? ${1:contract-principal} ${2:func} ${3:arg1}",
    output_type: "(response A B)",
    signature: "(contract-call? .contract-name function-name arg0 arg1 ...)",
    description: "The `contract-call?` function executes the given public function of the given contract.
You _may not_ use this function to call a public function defined in the current contract. If the public
function returns _err_, any database changes resulting from calling `contract-call?` are aborted.
If the function returns _ok_, database changes occurred.",
    example: "
;; instantiate the sample/contracts/tokens.clar contract first!
(as-contract (contract-call? .tokens mint! u19)) ;; Returns (ok u19)"
};

const CONTRACT_OF_API: SpecialAPI = SpecialAPI {
    input_type: "Trait",
    output_type: "principal",
    snippet: "contract-of ${1:contract-name}",
    signature: "(contract-of .contract-name)",
    description: "The `contract-of` function returns the principal of the contract implementing the trait.",
    example: "
(use-trait token-a-trait 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF.token-a.token-trait)
(define-public (forward-get-balance (user principal) (contract <token-a-trait>))
  (begin
    (ok (contract-of contract)))) ;; returns the principal of the contract implementing <token-a-trait>
"
};

const PRINCIPAL_OF_API: SpecialAPI = SpecialAPI {
    input_type: "(buff 33)",
    snippet: "principal-of? ${1:public-key}",
    output_type: "(response principal uint)",
    signature: "(principal-of? public-key)",
    description: "The `principal-of?` function returns the principal derived from the provided public key.
This function may fail with the error code:

* `(err u1)` -- `public-key` is invalid

Note: Before Stacks 2.1, this function has a bug, in that the principal returned would always
be a testnet single-signature principal, even if the function were run on the mainnet. Starting
with Stacks 2.1, this bug is fixed, so that this function will return a principal suited to
the network it is called on. In particular, if this is called on the mainnet, it will
return a single-signature mainnet principal.
    ",
    example: "(principal-of? 0x03adb8de4bfb65db2cfd6120d55c6526ae9c52e675db7e47308636534ba7786110) ;; Returns (ok ST1AW6EKPGT61SQ9FNVDS17RKNWT8ZP582VF9HSCP)"
};

const AT_BLOCK: SpecialAPI = SpecialAPI {
    input_type: "(buff 32), A",
    snippet: "at-block ${1:id-header-hash} ${2:expr}",
    output_type: "A",
    signature: "(at-block id-block-hash expr)",
    description: "The `at-block` function evaluates the expression `expr` _as if_ it were evaluated at the end of the
block indicated by the _block-hash_ argument. The `expr` closure must be read-only.

Note: The block identifying hash must be a hash returned by the `id-header-hash` block information
property. This hash uniquely identifies Stacks blocks and is unique across Stacks forks. While the hash returned by
`header-hash` is unique within the context of a single fork, it is not unique across Stacks forks.

The function returns the result of evaluating `expr`.
",
    example: "
(define-data-var data int 1)
(at-block 0x0000000000000000000000000000000000000000000000000000000000000000 block-height) ;; Returns u0
(at-block (unwrap-panic (get-block-info? id-header-hash u0)) (var-get data)) ;; Throws NoSuchDataVariable because `data` wasn't initialized at block height 0"
};

const AS_CONTRACT_API: SpecialAPI = SpecialAPI {
    input_type: "A",
    snippet: "as-contract ${1:expr}",
    output_type: "A",
    signature: "(as-contract expr)",
    description: "The `as-contract` function switches the current context's `tx-sender` value to the _contract's_
principal and executes `expr` with that context. It returns the resulting value of `expr`.",
    example: "(as-contract tx-sender) ;; Returns S1G2081040G2081040G2081040G208105NK8PE5.docs-test"
};

const ASSERTS_API: SpecialAPI = SpecialAPI {
    input_type: "bool, C",
    snippet: "asserts! ${1:boolean-expr} (err ${2:thrown})",
    output_type: "bool",
    signature: "(asserts! bool-expr thrown-value)",
    description: "The `asserts!` function admits a boolean argument and asserts its evaluation:
if bool-expr is `true`, `asserts!` returns `true` and proceeds in the program execution.
If the supplied argument is returning a false value, `asserts!` _returns_ `thrown-value` and exits the current
control-flow.",
    example: "(asserts! (is-eq 1 1) (err 1)) ;; Returns true",
};

const EXPECTS_API: SpecialAPI = SpecialAPI {
    input_type: "(optional A) | (response A B), C",
    snippet: "unwrap! ${1:algebraic-expr} (err ${2:thrown})",
    output_type: "A",
    signature: "(unwrap! option-input thrown-value)",
    description: "The `unwrap!` function attempts to 'unpack' the first argument: if the argument is
an option type, and the argument is a `(some ...)` option, `unwrap!` returns the inner value of the
option. If the argument is a response type, and the argument is an `(ok ...)` response, `unwrap!` returns
 the inner value of the `ok`. If the supplied argument is either an `(err ...)` or a `none` value,
`unwrap!` _returns_ `thrown-value` from the current function and exits the current control-flow.",
    example: "
(define-map names-map { name: (string-ascii 12) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 })
(define-private (get-name-or-err (name (string-ascii 12)))
  (let ((raw-name (unwrap! (map-get? names-map { name: name }) (err 1))))
       (ok raw-name)))

(get-name-or-err \"blockstack\") ;; Returns (ok (tuple (id 1337)))
(get-name-or-err \"non-existant\") ;; Returns (err 1)",
};

const TRY_API: SpecialAPI = SpecialAPI {
    input_type: "(optional A) | (response A B)",
    snippet: "try! ${1:algebraic-expr}",
    output_type: "A",
    signature: "(try! option-input)",
    description: "The `try!` function attempts to 'unpack' the first argument: if the argument is
an option type, and the argument is a `(some ...)` option, `try!` returns the inner value of the
option. If the argument is a response type, and the argument is an `(ok ...)` response, `try!` returns
 the inner value of the `ok`. If the supplied argument is either an `(err ...)` or a `none` value,
`try!` _returns_ either `none` or the `(err ...)` value from the current function and exits the current control-flow.",
    example: "
(define-map names-map { name: (string-ascii 12) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 })
(try! (map-get? names-map { name: \"blockstack\" })) ;; Returns (tuple (id 1337))
(define-private (checked-even (x int))
  (if (is-eq (mod x 2) 0)
      (ok x)
      (err false)))
(define-private (double-if-even (x int))
  (ok (* 2 (try! (checked-even x)))))
(double-if-even 10) ;; Returns (ok 20)
(double-if-even 3) ;; Returns (err false)
",
};

const UNWRAP_API: SpecialAPI = SpecialAPI {
    input_type: "(optional A) | (response A B)",
    snippet: "unwrap-panic ${1:algebraic-expr}",
    output_type: "A",
    signature: "(unwrap-panic option-input)",
    description: "The `unwrap` function attempts to 'unpack' its argument: if the argument is
an option type, and the argument is a `(some ...)` option, this function returns the inner value of the
option. If the argument is a response type, and the argument is an `(ok ...)` response, it returns
 the inner value of the `ok`. If the supplied argument is either an `(err ...)` or a `none` value,
`unwrap` throws a runtime error, aborting any further processing of the current transaction.",
    example: "
(define-map names-map { name: (string-ascii 12) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 })
(unwrap-panic (map-get? names-map { name: \"blockstack\" })) ;; Returns (tuple (id 1337))
(unwrap-panic (map-get? names-map { name: \"non-existant\" })) ;; Throws a runtime exception
",
};

const UNWRAP_ERR_API: SpecialAPI = SpecialAPI {
    input_type: "(response A B)",
    snippet: "unwrap-err-panic ${1:algebraic-expr}",
    output_type: "B",
    signature: "(unwrap-err-panic response-input)",
    description:
        "The `unwrap-err` function attempts to 'unpack' the first argument: if the argument
is an `(err ...)` response, `unwrap` returns the inner value of the `err`.
If the supplied argument is an `(ok ...)` value,
`unwrap-err` throws a runtime error, aborting any further processing of the current transaction.",
    example: "(unwrap-err-panic (err 1)) ;; Returns 1
(unwrap-err-panic (ok 1)) ;; Throws a runtime exception",
};

const EXPECTS_ERR_API: SpecialAPI = SpecialAPI {
    input_type: "(response A B), C",
    snippet: "unwrap-err! ${1:algebraic-expr} (err ${2:thrown})",
    output_type: "B",
    signature: "(unwrap-err! response-input thrown-value)",
    description: "The `unwrap-err!` function attempts to 'unpack' the first argument: if the argument
is an `(err ...)` response, `unwrap-err!` returns the inner value of the `err`.
If the supplied argument is an `(ok ...)` value,
`unwrap-err!` _returns_ `thrown-value` from the current function and exits the current control-flow.",
    example: "(unwrap-err! (err 1) false) ;; Returns 1",
};

const MATCH_API: SpecialAPI = SpecialAPI {
    input_type:
        "(optional A) name expression expression | (response A B) name expression name expression",
    snippet: "match ${1:algebraic-expr} ${2:some-binding-name} ${3:some-branch} ${4:none-branch}",
    output_type: "C",
    signature: "(match opt-input some-binding-name some-branch none-branch) |
(match-resp input ok-binding-name ok-branch err-binding-name err-branch)",
    description: "The `match` function is used to test and destructure optional and response types.

If the `input` is an optional, it tests whether the provided
`input` is a `some` or `none` option, and evaluates `some-branch` or
`none-branch` in each respective case.

Within the `some-branch`, the _contained value_ of the `input`
argument is bound to the provided `some-binding-name` name.

Only _one_ of the branches will be evaluated (similar to `if` statements).

If the `input` is a response, it tests whether the provided `input` is
an `ok` or `err` response type, and evaluates `ok-branch` or
`err-branch` in each respective case.

Within the `ok-branch`, the _contained ok value_ of the `input`
argument is bound to the provided `ok-binding-name` name.

Within the `err-branch`, the _contained err value_ of the `input`
argument is bound to the provided `err-binding-name` name.

Only _one_ of the branches will be evaluated (similar to `if` statements).

Note: Type checking requires that the type of both the ok and err parts of the
response object be determinable. For situations in which one of the parts of a response
is untyped, you should use `unwrap-panic` or `unwrap-err-panic` instead of `match`.",
    example: "
(define-private (add-10 (x (optional int)))
  (match x
  value (+ 10 value)
  10))
(add-10 (some 5)) ;; Returns 15
(add-10 none) ;; Returns 10

(define-private (add-or-pass-err (x (response int (string-ascii 10))) (to-add int))
  (match x
   value (ok (+ to-add value))
   err-value (err err-value)))
(add-or-pass-err (ok 5) 20) ;; Returns (ok 25)
(add-or-pass-err (err \"ERROR\") 20) ;; Returns (err \"ERROR\")
",
};

const DEFAULT_TO_API: SpecialAPI = SpecialAPI {
    input_type: "A, (optional A)",
    snippet: "default-to ${1:default-value} ${2:option-value}",
    output_type: "A",
    signature: "(default-to default-value option-value)",
    description: "The `default-to` function attempts to 'unpack' the second argument: if the argument is
a `(some ...)` option, it returns the inner value of the option. If the second argument is a `none` value,
`default-to` it returns the value of `default-value`.",
    example: "
(define-map names-map { name: (string-ascii 12) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 })
(default-to 0 (get id (map-get? names-map (tuple (name \"blockstack\"))))) ;; Returns 1337
(default-to 0 (get id (map-get? names-map (tuple (name \"non-existant\"))))) ;; Returns 0
",
};

const CONS_OK_API: SpecialAPI = SpecialAPI {
    input_type: "A",
    snippet: "ok ${1:value}",
    output_type: "(response A B)",
    signature: "(ok value)",
    description: "The `ok` function constructs a response type from the input value. Use `ok` for
creating return values in public functions. An _ok_ value indicates that any database changes during
the processing of the function should materialize.",
    example: "(ok 1) ;; Returns (ok 1)",
};

const CONS_ERR_API: SpecialAPI = SpecialAPI {
    input_type: "A",
    snippet: "err ${1:value}",
    output_type: "(response A B)",
    signature: "(err value)",
    description: "The `err` function constructs a response type from the input value. Use `err` for
creating return values in public functions. An _err_ value indicates that any database changes during
the processing of the function should be rolled back.",
    example: "(err true) ;; Returns (err true)",
};

const CONS_SOME_API: SpecialAPI = SpecialAPI {
    input_type: "A",
    snippet: "some ${1:value}",
    output_type: "(optional A)",
    signature: "(some value)",
    description: "The `some` function constructs a `optional` type from the input value.",
    example: "(some 1) ;; Returns (some 1)
(is-none (some 2)) ;; Returns false",
};

const IS_OK_API: SpecialAPI = SpecialAPI {
    input_type: "(response A B)",
    snippet: "is-ok ${1:expr}",
    output_type: "bool",
    signature: "(is-ok value)",
    description:
        "`is-ok` tests a supplied response value, returning `true` if the response was `ok`,
and `false` if it was an `err`.",
    example: "(is-ok (ok 1)) ;; Returns true
(is-ok (err 1)) ;; Returns false",
};

const IS_NONE_API: SpecialAPI = SpecialAPI {
    input_type: "(optional A)",
    snippet: "is-none ${1:expr}",
    output_type: "bool",
    signature: "(is-none value)",
    description:
        "`is-none` tests a supplied option value, returning `true` if the option value is `none`,
and `false` if it is a `(some ...)`.",
    example: "
(define-map names-map { name: (string-ascii 12) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 })
(is-none (get id (map-get? names-map { name: \"blockstack\" }))) ;; Returns false
(is-none (get id (map-get? names-map { name: \"non-existant\" }))) ;; Returns true",
};

const IS_ERR_API: SpecialAPI = SpecialAPI {
    input_type: "(response A B)",
    snippet: "is-err ${1:expr}",
    output_type: "bool",
    signature: "(is-err value)",
    description:
        "`is-err` tests a supplied response value, returning `true` if the response was an `err`,
and `false` if it was an `ok`.",
    example: "(is-err (ok 1)) ;; Returns false
(is-err (err 1)) ;; Returns true",
};

const IS_SOME_API: SpecialAPI = SpecialAPI {
    input_type: "(optional A)",
    snippet: "is-some ${1:expr}",
    output_type: "bool",
    signature: "(is-some value)",
    description: "`is-some` tests a supplied option value, returning `true` if the option value is `(some ...)`,
and `false` if it is a `none`.",
    example: "
(define-map names-map { name: (string-ascii 12) } { id: int })
(map-set names-map { name: \"blockstack\" } { id: 1337 })
(is-some (get id (map-get? names-map { name: \"blockstack\" }))) ;; Returns true
(is-some (get id (map-get? names-map { name: \"non-existant\" }))) ;; Returns false"
};

const GET_BLOCK_INFO_API: SpecialAPI = SpecialAPI {
    input_type: "BlockInfoPropertyName, uint",
    snippet: "get-block-info? ${1:prop} ${2:block-height}",
    output_type: "(optional buff) | (optional uint)",
    signature: "(get-block-info? prop-name block-height)",
    description: "In Clarity 3, `get-block-info?` is removed. In its place, `get-stacks-block-info?` can be used to retrieve
information about a Stacks block and `get-tenure-info?` can be used to get information pertaining to the tenure.

The `get-block-info?` function fetches data for a block of the given *Stacks* block height. The
value and type returned are determined by the specified `BlockInfoPropertyName`. If the provided `block-height` does
not correspond to an existing block prior to the current block, the function returns `none`. The currently available property names
are as follows:

- `burnchain-header-hash`: This property returns a `(buff 32)` value containing the header hash of the burnchain (Bitcoin) block that selected the
Stacks block at the given Stacks chain height.

- `id-header-hash`: This property returns a `(buff 32)` value containing the _index block hash_ of a Stacks block.   This hash is globally unique, and is derived
from the block hash and the history of accepted PoX operations.  This is also the block hash value you would pass into `(at-block)`.

- `header-hash`: This property returns a `(buff 32)` value containing the header hash of a Stacks block, given a Stacks chain height.  **WARNING* this hash is
not guaranteed to be globally unique, since the same Stacks block can be mined in different PoX forks.  If you need global uniqueness, you should use `id-header-hash`.

- `miner-address`: This property returns a `principal` value corresponding to the miner of the given block.  **WARNING** In Stacks 2.1, this is not guaranteed to
be the same `principal` that received the block reward, since Stacks 2.1 supports coinbase transactions that pay the reward to a contract address.  This is merely
the address of the `principal` that produced the block.

- `time`: This property returns a `uint` value of the block header time field. This is a Unix epoch timestamp in seconds
which roughly corresponds to when the block was mined. This timestamp comes from the burnchain block. **Note**: this does not increase monotonically with each block
and block times are accurate only to within two hours. See [BIP113](https://github.com/bitcoin/bips/blob/master/bip-0113.mediawiki) for more information.
For blocks mined after epoch 3.0, all Stacks blocks in one tenure will share the same timestamp. To get the Stacks block time for a block in epoch 3.0+, use `get-stacks-block-info?`.

- `vrf-seed`: This property returns a `(buff 32)` value of the VRF seed for the corresponding block.

- `block-reward`: This property returns a `uint` value for the total block reward of the indicated Stacks block.  This value is only available once the reward for
the block matures.  That is, the latest `block-reward` value available is at least 101 Stacks blocks in the past (on mainnet).  The reward includes the coinbase,
the anchored block's transaction fees, and the shares of the confirmed and produced microblock transaction fees earned by this block's miner.  Note that this value may
be smaller than the Stacks coinbase at this height, because the miner may have been punished with a valid `PoisonMicroblock` transaction in the event that the miner
published two or more microblock stream forks. Added in Clarity 2.

- `miner-spend-total`: This property returns a `uint` value for the total number of burnchain tokens (i.e. satoshis) spent by all miners trying to win this block. Added in Clarity 2.

- `miner-spend-winner`: This property returns a `uint` value for the number of burnchain tokens (i.e. satoshis) spent by the winning miner for this Stacks block.  Note that
this value is less than or equal to the value for `miner-spend-total` at the same block height. Added in Clarity 2.
",
    example: "(get-block-info? time u0) ;; Returns (some u1557860301)
(get-block-info? header-hash u0) ;; Returns (some 0x374708fff7719dd5979ec875d56cd2286f6d3cf7ec317a3b25632aab28ec37bb)
(get-block-info? vrf-seed u0) ;; Returns (some 0xf490de2920c8a35fabeb13208852aa28c76f9be9b03a4dd2b3c075f7a26923b4)
"
};

const GET_BURN_BLOCK_INFO_API: SpecialAPI = SpecialAPI {
    input_type: "BurnBlockInfoPropertyName, uint",
    output_type: "(optional buff) | (optional (tuple (addrs (list 2 (tuple (hashbytes (buff 32)) (version (buff 1))))) (payout uint)))",
    snippet: "get-burn-block-info? ${1:prop} ${2:burn-block-height}",
    signature: "(get-burn-block-info? prop-name burn-block-height)",
    description: "The `get-burn-block-info?` function fetches data for a block of the given *burnchain* block height. The
value and type returned are determined by the specified `BlockInfoPropertyName`.  Valid values for `burn-block-height` only
include heights between the burnchain height at the time the Stacks chain was launched, and the last-processed burnchain
block.  If the `burn-block-height` argument falls outside of this range, then `none` shall be returned.

The following `BlockInfoPropertyName` values are defined:

* The `header-hash` property returns a 32-byte buffer representing the header hash of the burnchain block at
burnchain height `burn-block-height`.

* The `pox-addrs` property returns a tuple with two items: a list of up to two PoX addresses that received a PoX payout at that block height, and the amount of burnchain
tokens paid to each address (note that per the blockchain consensus rules, each PoX payout will be the same for each address in the block-commit transaction).
The list will include burn addresses -- that is, the unspendable addresses that miners pay to when there are no PoX addresses left to be paid.  During the prepare phase,
there will be exactly one burn address reported. During the reward phase, up to two burn addresses may be reported in the event that some PoX reward slots are not claimed.

The `addrs` list contains the same PoX address values passed into the PoX smart contract:
   * They each have type signature `(tuple (hashbytes (buff 32)) (version (buff 1)))`
   * The `version` field can be any of the following:
      * `0x00` means this is a p2pkh address, and `hashbytes` is the 20-byte hash160 of a single public key
      * `0x01` means this is a p2sh address, and `hashbytes` is the 20-byte hash160 of a redeemScript script
      * `0x02` means this is a p2wpkh-p2sh address, and `hashbytes` is the 20-byte hash160 of a p2wpkh witness script
      * `0x03` means this is a p2wsh-p2sh address, and `hashbytes` is the 20-byte hash160 of a p2wsh witness script
      * `0x04` means this is a p2wpkh address, and `hashbytes` is the 20-byte hash160 of the witness script
      * `0x05` means this is a p2wsh address, and `hashbytes` is the 32-byte sha256 of the witness script
      * `0x06` means this is a p2tr address, and `hashbytes` is the 32-byte sha256 of the witness script
",
    example: "
(get-burn-block-info? header-hash u677050) ;; Returns (some 0xe67141016c88a7f1203eca0b4312f2ed141531f59303a1c267d7d83ab6b977d8)
(get-burn-block-info? pox-addrs u677050) ;; Returns (some (tuple (addrs ((tuple (hashbytes 0x395f3643cea07ec4eec73b4d9a973dcce56b9bf1) (version 0x00)) (tuple (hashbytes 0x7c6775e20e3e938d2d7e9d79ac310108ba501ddb) (version 0x01)))) (payout u123)))
"
};

const GET_STACKS_BLOCK_INFO_API: SpecialAPI = SpecialAPI {
    input_type: "StacksBlockInfoPropertyName, uint",
    snippet: "get-stacks-block-info? ${1:prop} ${2:stacks-block-height}",
    output_type: "(optional buff) | (optional uint)",
    signature: "(get-stacks-block-info? prop-name stacks-block-height)",
    description: "The `get-stacks-block-info?` function fetches data for a block of the given *Stacks* block height. The
value and type returned are determined by the specified `StacksBlockInfoPropertyName`. If the provided `stacks-block-height` does
not correspond to an existing block prior to the current block, the function returns `none`. The currently available property names
are as follows:

- `id-header-hash`: This property returns a `(buff 32)` value containing the _index block hash_ of a Stacks block.   This hash is globally unique, and is derived
from the block hash and the history of accepted PoX operations.  This is also the block hash value you would pass into `(at-block)`.

- `header-hash`: This property returns a `(buff 32)` value containing the header hash of a Stacks block, given a Stacks chain height.  **WARNING* this hash is
not guaranteed to be globally unique, since the same Stacks block can be mined in different PoX forks.  If you need global uniqueness, you should use `id-header-hash`.

- `time`: This property returns a `uint` value of the block header time field. This is a Unix epoch timestamp in seconds
which roughly corresponds to when the block was mined. For a block mined before epoch 3.0, this timestamp comes from the burnchain block. **Note**: this does not increase monotonically with each block
and block times are accurate only to within two hours. See [BIP113](https://github.com/bitcoin/bips/blob/master/bip-0113.mediawiki) for more information.
For a block mined after epoch 3.0, this timestamp comes from the Stacks block header. **Note**: this is the time, according to the miner, when
the mining of this block started, but is not guaranteed to be accurate. This time will be validated by the signers to be:
  - Greater than the timestamp of the previous block
  - At most 15 seconds into the future (according to their own local clocks)
",
    example: "(get-stacks-block-info? time u0) ;; Returns (some u1557860301)
(get-stacks-block-info? header-hash u0) ;; Returns (some 0x374708fff7719dd5979ec875d56cd2286f6d3cf7ec317a3b25632aab28ec37bb)
"
};

const GET_TENURE_INFO_API: SpecialAPI = SpecialAPI {
    input_type: "TenureInfoPropertyName, uint",
    snippet: "get-tenure-info? ${1:prop} ${2:stacks-block-height}",
    output_type: "(optional buff) | (optional uint)",
    signature: "(get-tenure-info? prop-name stacks-block-height)",
    description: "The `get-tenure-info?` function fetches data for the tenure at the given block height. The
value and type returned are determined by the specified `TenureInfoPropertyName`. If the provided `stacks-block-height` does
not correspond to an existing block prior to the current block, the function returns `none`. The currently available property names
are as follows:

- `burnchain-header-hash`: This property returns a `(buff 32)` value containing the header hash of the burnchain (Bitcoin) block that selected the
tenure at the given height.

- `miner-address`: This property returns a `principal` value corresponding to the miner of the given tenure.  **WARNING** This is not guaranteed to
be the same `principal` that received the block reward, since Stacks 2.1+ supports coinbase transactions that pay the reward to a contract address.  This is merely
the address of the `principal` that produced the tenure.

- `time`: This property returns a `uint` Unix epoch timestamp in seconds which roughly corresponds to when the tenure was started. This timestamp comes
from the burnchain block. **Note**: this does not increase monotonically with each tenure and tenure times are accurate only to within two hours. See
[BIP113](https://github.com/bitcoin/bips/blob/master/bip-0113.mediawiki) for more information.

- `vrf-seed`: This property returns a `(buff 32)` value of the VRF seed for the corresponding tenure.

- `block-reward`: This property returns a `uint` value for the total block reward of the indicated tenure.  This value is only available once the reward for
the tenure matures.  That is, the latest `block-reward` value available is at least 101 Stacks blocks in the past (on mainnet).  The reward includes the coinbase,
the anchored tenure's transaction fees, and the shares of the confirmed and produced microblock transaction fees earned by this block's miner.  Note that this value may
be smaller than the Stacks coinbase at this height, because the miner may have been punished with a valid `PoisonMicroblock` transaction in the event that the miner
published two or more microblock stream forks.

- `miner-spend-total`: This property returns a `uint` value for the total number of burnchain tokens (i.e. satoshis) spent by all miners trying to win this tenure.

- `miner-spend-winner`: This property returns a `uint` value for the number of burnchain tokens (i.e. satoshis) spent by the winning miner for this tennure.  Note that
this value is less than or equal to the value for `miner-spend-total` at the same tenure height.
",
    example: "(get-tenure-info? time u0) ;; Returns (some u1557860301)
(get-tenure-info? vrf-seed u0) ;; Returns (some 0xf490de2920c8a35fabeb13208852aa28c76f9be9b03a4dd2b3c075f7a26923b4)
"
};

const PRINCIPAL_CONSTRUCT_API: SpecialAPI = SpecialAPI {
    input_type: "(buff 1), (buff 20), [(string-ascii 40)]",
    output_type: "(response principal { error_code: uint, value: (optional principal) })",
    snippet: "principal-construct? ${1:version} ${2:pub-key-hash}",
    signature: "(principal-construct? (buff 1) (buff 20) [(string-ascii 40)])",
    description: "A principal value represents either a set of keys, or a smart contract.
The former, called a _standard principal_,
is encoded as a `(buff 1)` *version byte*, indicating the type of account
and the type of network that this principal can spend tokens on,
and a `(buff 20)` *public key hash*, characterizing the principal's unique identity.
The latter, a _contract principal_, is encoded as a standard principal concatenated with
a `(string-ascii 40)` *contract name* that identifies the code body.

The `principal-construct?` function allows users to create either standard or contract principals,
depending on which form is used.  To create a standard principal,
`principal-construct?` would be called with two arguments: it
takes as input a `(buff 1)` which encodes the principal address's
`version-byte`, a `(buff 20)` which encodes the principal address's `hash-bytes`.
To create a contract principal, `principal-construct?` would be called with
three arguments: the `(buff 1)` and `(buff 20)` to represent the standard principal
that created the contract, and a `(string-ascii 40)` which encodes the contract's name.
On success, this function returns either a standard principal or contract principal,
depending on whether or not the third `(string-ascii 40)` argument is given.

This function returns a `Response`. On success, the `ok` value is a `Principal`.
The `err` value is a value tuple with the form `{ error_code: uint, value: (optional principal) }`.

If the single-byte `version-byte` is in the valid range `0x00` to `0x1f`, but is not an appropriate
version byte for the current network, then the error will be `u0`, and `value` will contain
`(some principal)`, where the wrapped value is the principal.  If the `version-byte` is not in this range,
however, then the `value` will be `none`.

If the `version-byte` is a `buff` of length 0, if the single-byte `version-byte` is a
value greater than `0x1f`, or the `hash-bytes` is a `buff` of length not equal to 20, then `error_code`
will be `u1` and `value` will be `none`.

If a name is given, and the name is either an empty string or contains ASCII characters
that are not allowed in contract names, then `error_code` will be `u2`.

Note: This function is only available starting with Stacks 2.1.",
    example: r#"
(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320) ;; Returns (ok ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK)
(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320 "foo") ;; Returns (ok ST3X6QWWETNBZWGBK6DRGTR1KX50S74D3425Q1TPK.foo)
(principal-construct? 0x16 0xfa6bf38ed557fe417333710d6033e9419391a320) ;; Returns (err (tuple (error_code u0) (value (some SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY))))
(principal-construct? 0x16 0xfa6bf38ed557fe417333710d6033e9419391a320 "foo") ;; Returns (err (tuple (error_code u0) (value (some SP3X6QWWETNBZWGBK6DRGTR1KX50S74D3433WDGJY.foo))))
(principal-construct? 0x   0xfa6bf38ed557fe417333710d6033e9419391a320) ;; Returns (err (tuple (error_code u1) (value none)))
(principal-construct? 0x16 0xfa6bf38ed557fe417333710d6033e9419391a3)   ;; Returns (err (tuple (error_code u1) (value none)))
(principal-construct? 0x20 0xfa6bf38ed557fe417333710d6033e9419391a320) ;; Returns (err (tuple (error_code u1) (value none)))
(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320 "") ;; Returns (err (tuple (error_code u2) (value none)))
(principal-construct? 0x1a 0xfa6bf38ed557fe417333710d6033e9419391a320 "foo[") ;; Returns (err (tuple (error_code u2) (value none)))
"#,
};

const DEFINE_TOKEN_API: DefineAPI = DefineAPI {
    input_type: "TokenName, <uint>",
    snippet: "define-fungible-token ${1:token-name} ${2:total-supply}",
    output_type: "Not Applicable",
    signature: "(define-fungible-token token-name <total-supply>)",
    description: "`define-fungible-token` is used to define a new fungible token class for use in the current contract.

The second argument, if supplied, defines the total supply of the fungible token. This ensures that all calls to the `ft-mint?`
function will never be able to create more than `total-supply` tokens. If any such call were to increase the total supply
of tokens passed that amount, that invocation of `ft-mint?` will result in a runtime error and abort.

Like other kinds of definition statements, `define-fungible-token` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).

Tokens defined using `define-fungible-token` may be used in `ft-transfer?`, `ft-mint?`, and `ft-get-balance` functions",
    example: "
(define-fungible-token stacks)
(define-fungible-token limited-supply-stacks u100)
"
};

const DEFINE_ASSET_API: DefineAPI = DefineAPI {
    input_type: "AssetName, TypeSignature",
    snippet: "define-non-fungible-token ${1:nft-name} ${2:nft-identifier-type}",
    output_type: "Not Applicable",
    signature: "(define-non-fungible-token asset-name asset-identifier-type)",
    description: "`define-non-fungible-token` is used to define a new non-fungible token class for use in the current contract.
Individual assets are identified by their asset identifier, which must be of the type `asset-identifier-type`. Asset
identifiers are _unique_ identifiers.

Like other kinds of definition statements, `define-non-fungible-token` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).

Assets defined using `define-non-fungible-token` may be used in `nft-transfer?`, `nft-mint?`, and `nft-get-owner?` functions",
    example: "
(define-non-fungible-token names (buff 50))
"
};

const DEFINE_PUBLIC_API: DefineAPI = DefineAPI {
    input_type: "MethodSignature, MethodBody",
    snippet: "define-public (${1:func-name}) ${2:body}",
    output_type: "Not Applicable",
    signature: "(define-public (function-name (arg-name-0 arg-type-0) (arg-name-1 arg-type-1) ...) function-body)",
    description: "`define-public` is used to define a _public_ function and transaction for a smart contract. Public
functions are callable from other smart contracts and may be invoked directly by users by submitting a transaction
to the Stacks blockchain.

Like other kinds of definition statements, `define-public` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).

Public functions _must_ return a ResponseType (using either `ok` or `err`). Any datamap modifications performed by
a public function is aborted if the function returns an `err` type. Public functions may be invoked by other
contracts via `contract-call?`.",
    example: "
(define-public (hello-world (input int))
  (begin (print (+ 2 input))
         (ok input)))
"
};

const DEFINE_CONSTANT_API: DefineAPI = DefineAPI {
    input_type: "MethodSignature, MethodBody",
    snippet: "define-constant ${1:name} ${2:exprs}",
    output_type: "Not Applicable",
    signature: "(define-constant name expression)",
    description: "`define-constant` is used to define a private constant value in a smart contract.
The expression passed into the definition is evaluated at contract launch, in the order that it is
supplied in the contract. This can lead to undefined function or undefined variable errors in the
event that a function or variable used in the expression has not been defined before the constant.

Like other kinds of definition statements, `define-constant` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).
",
    example: "
(define-constant four (+ 2 2))
(+ 4 four) ;; Returns 8
"
};

const DEFINE_PRIVATE_API: DefineAPI = DefineAPI {
    input_type: "MethodSignature, MethodBody",
    snippet: "define-private (${1:func-name}) ${2:body}",
    output_type: "Not Applicable",
    signature: "(define-private (function-name (arg-name-0 arg-type-0) (arg-name-1 arg-type-1) ...) function-body)",
    description: "`define-private` is used to define _private_ functions for a smart contract. Private
functions may not be called from other smart contracts, nor may they be invoked directly by users.
Instead, these functions may only be invoked by other functions defined in the same smart contract.

Like other kinds of definition statements, `define-private` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).

Private functions may return any type.",
    example: "
(define-private (max-of (i1 int) (i2 int))
  (if (> i1 i2)
      i1
      i2))
(max-of 4 6) ;; Returns 6
"
};

const DEFINE_READ_ONLY_API: DefineAPI = DefineAPI {
    input_type: "MethodSignature, MethodBody",
    snippet: "define-read-only (${1:func-name}) ${2:body}",
    output_type: "Not Applicable",
    signature: "(define-read-only (function-name (arg-name-0 arg-type-0) (arg-name-1 arg-type-1) ...) function-body)",
    description: "`define-read-only` is used to define a _public read-only_ function for a smart contract. Such
functions are callable from other smart contracts.

Like other kinds of definition statements, `define-read-only` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).

Read-only functions may return any type. However, read-only functions
may not perform any datamap modifications, or call any functions which
perform such modifications. This is enforced both during type checks and during
the execution of the function. Public read-only functions may
be invoked by other contracts via `contract-call?`.",
    example: "
(define-read-only (just-return-one-hundred)
  (* 10 10))"
};

const DEFINE_MAP_API: DefineAPI = DefineAPI {
    input_type: "MapName, TypeDefinition, TypeDefinition",
    snippet: "define-map ${1:map-name} { ${2:key-name-1}: ${3:key-type-1} } { ${4:val-name-1}: ${5:vals-type-1} }",
    output_type: "Not Applicable",
    signature: "(define-map map-name key-type value-type)",
    description: "`define-map` is used to define a new datamap for use in a smart contract. Such
maps are only modifiable by the current smart contract.

Maps are defined with a key type and value type, often these types are tuple types.

Like other kinds of definition statements, `define-map` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).",
    example: "
(define-map squares { x: int } { square: int })
(define-private (add-entry (x int))
  (map-insert squares { x: 2 } { square: (* x x) }))
(add-entry 1)
(add-entry 2)
(add-entry 3)
(add-entry 4)
(add-entry 5)
"
};

const DEFINE_DATA_VAR_API: DefineAPI = DefineAPI {
    input_type: "VarName, TypeDefinition, Value",
    snippet: "define-data-var ${1:name} ${2:type} ${3:value}",
    output_type: "Not Applicable",
    signature: "(define-data-var var-name type value)",
    description: "`define-data-var` is used to define a new persisted variable for use in a smart contract. Such
variable are only modifiable by the current smart contract.

Persisted variable are defined with a type and a value.

Like other kinds of definition statements, `define-data-var` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).",
    example: "
(define-data-var size int 0)
(define-private (set-size (value int))
  (var-set size value))
(set-size 1)
(set-size 2)
"
};

const DEFINE_TRAIT_API: DefineAPI = DefineAPI {
    input_type: "VarName, [MethodSignature]",
    snippet: "define-trait ${1:trait-name} ((${2:func-name} (${3:func-param-types}) (response ${4:ok-type} ${5:err-type})))",
    output_type: "Not Applicable",
    signature: "(define-trait trait-name ((func1-name (arg1-type arg2-type ...) (return-type))))",
    description: "`define-trait` is used to define a new trait definition for use in a smart contract. Other contracts
can implement a given trait and then have their contract identifier being passed as a function argument in order to be called
dynamically with `contract-call?`.

Traits are defined with a name, and a list of functions, where each function is defined with a name, a list of argument types, and a return type.

In Clarity 1, a trait type can be used to specify the type of a function parameter. A parameter with a trait type can
be used as the target of a dynamic `contract-call?`. A principal literal (e.g. `ST1PQHQKV0RJXZFY1DGX8MNSNYVE3VGZJSRTPGZGM.foo`)
may be passed as a trait parameter if the specified contract implements all of the functions specified by the trait.
A trait value (originating from a parameter with trait type) may also be passed as a trait parameter if the types are the same.

Beginning in Clarity 2, a trait can be used in all of the same ways that a built-in type can be used,
except that it cannot be stored in a data var or map, since this would inhibit static analysis.
This means that a trait type can be embedded in a compound type (e.g. `(optional <my-trait>)` or `(list 4 <my-trait>)`)
and a trait value can be bound to a variable in a `let` or `match` expression. In addition to the principal literal
and trait value with matching type allowed in Clarity 1, Clarity 2 also supports implicit casting from a
compatible trait, meaning that a value of type `trait-a` may be passed to a parameter with type `trait-b` if `trait-a`
includes all of the requirements of `trait-b` (and optionally additional functions).

Like other kinds of definition statements, `define-trait` may only be used at the top level of a smart contract
definition (i.e., you cannot put a define statement in the middle of a function body).
",
    example: "
(define-trait token-trait
    ((transfer? (principal principal uint) (response uint uint))
     (get-balance (principal) (response uint uint))))
"
};

const USE_TRAIT_API: DefineAPI = DefineAPI {
    input_type: "VarName, TraitIdentifier",
    snippet: "use-trait ${1:trait-alias} ${2:trait-identifier}",
    output_type: "Not Applicable",
    signature: "(use-trait trait-alias trait-identifier)",
    description: "`use-trait` is used to bring a trait, defined in another contract, to the current contract. Subsequent
references to an imported trait are signaled with the syntax `<trait-alias>`.

Traits import are defined with a name, used as an alias, and a trait identifier. Trait identifiers can either be
using the sugared syntax (.token-a.token-trait), or be fully qualified ('SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF.token-a.token-trait).

Like other kinds of definition statements, `use-trait` may only be used at the top level of a smart contract
definition (i.e., you cannot put such a statement in the middle of a function body).
    ",
    example: "
(use-trait token-a-trait 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF.token-a.token-trait)
(define-public (forward-get-balance (user principal) (contract <token-a-trait>))
  (begin
    (ok 1)))
"
};

const IMPL_TRAIT_API: DefineAPI = DefineAPI {
    input_type: "TraitIdentifier",
    snippet: "impl-trait ${1:trait-identifier}",
    output_type: "Not Applicable",
    signature: "(impl-trait trait-identifier)",
    description: "`impl-trait` can be use for asserting that a contract is fully implementing a given trait.
Additional checks are being performed when the contract is being published, rejecting the deployment if the
contract is violating the trait specification.

Trait identifiers can either be using the sugared syntax (.token-a.token-trait), or be fully qualified
('SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF.token-a.token-trait).

Like other kinds of definition statements, `impl-trait` may only be used at the top level of a smart contract
definition (i.e., you cannot put such a statement in the middle of a function body).
",
    example: "
(impl-trait 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF.token-a.token-trait)
(define-public (get-balance (account principal))
  (ok u0))
(define-public (transfer? (from principal) (to principal) (amount uint))
  (ok u0))
"
};

const MINT_TOKEN: SpecialAPI = SpecialAPI {
    input_type: "TokenName, uint, principal",
    snippet: "ft-mint? ${1:token-name} ${2:amount} ${3:recipient}",
    output_type: "(response bool uint)",
    signature: "(ft-mint? token-name amount recipient)",
    description: "`ft-mint?` is used to increase the token balance for the `recipient` principal for a token
type defined using `define-fungible-token`. The increased token balance is _not_ transfered from another principal, but
rather minted.

If a non-positive amount is provided to mint, this function returns `(err 1)`. Otherwise, on successfully mint, it
returns `(ok true)`. If this call would result in more supplied tokens than defined by the total supply in
`define-fungible-token`, then a `SupplyOverflow` runtime error is thrown.
",
    example: "
(define-fungible-token stackaroo)
(ft-mint? stackaroo u100 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
"
};

const MINT_ASSET: SpecialAPI = SpecialAPI {
    input_type: "AssetName, A, principal",
    snippet: "nft-mint? ${1:asset-name} ${2:asset-identifier} ${3:recipient}",
    output_type: "(response bool uint)",
    signature: "(nft-mint? asset-class asset-identifier recipient)",
    description: "`nft-mint?` is used to instantiate an asset and set that asset's owner to the `recipient` principal.
The asset must have been defined using `define-non-fungible-token`, and the supplied `asset-identifier` must be of the same type specified in
that definition.

The function returns `(ok true)` if the mint is successful. This function may fail with the error code:

* `(err u1)` -- an asset identified by `asset-identifier` _already exists_
",
    example: "
(define-non-fungible-token stackaroo (string-ascii 40))
(nft-mint? stackaroo \"Roo\" 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
"
};

const GET_OWNER: SpecialAPI = SpecialAPI {
    input_type: "AssetName, A",
    snippet: "nft-get-owner? ${1:asset-name} ${2:asset-identifier}",
    output_type: "(optional principal)",
    signature: "(nft-get-owner? asset-class asset-identifier)",
    description: "`nft-get-owner?` returns the owner of an asset, identified by `asset-identifier`, or `none` if the asset does not exist.
The asset type must have been defined using `define-non-fungible-token`, and the supplied `asset-identifier` must be of the same type specified in
that definition.",
    example: "
(define-non-fungible-token stackaroo (string-ascii 40))
(nft-mint? stackaroo \"Roo\" 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)
(nft-get-owner? stackaroo \"Roo\") ;; Returns (some SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF)
(nft-get-owner? stackaroo \"Too\") ;; Returns none
"
};

const GET_BALANCE: SpecialAPI = SpecialAPI {
    input_type: "TokenName, principal",
    snippet: "ft-get-balance ${1:token-name} ${2:principal}",
    output_type: "uint",
    signature: "(ft-get-balance token-name principal)",
    description: "`ft-get-balance` returns `token-name` balance of the principal `principal`.
The token type must have been defined using `define-fungible-token`.",
    example: "
(define-fungible-token stackaroo)
(ft-mint? stackaroo u100 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
(ft-get-balance stackaroo 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR) ;; Returns u100
",
};

const TOKEN_TRANSFER: SpecialAPI = SpecialAPI {
    input_type: "TokenName, uint, principal, principal",
    snippet: "ft-transfer? ${1:token-name} ${2:amount} ${3:sender} ${4:recipient}",
    output_type: "(response bool uint)",
    signature: "(ft-transfer? token-name amount sender recipient)",
    description: "`ft-transfer?` is used to increase the token balance for the `recipient` principal for a token
type defined using `define-fungible-token` by debiting the `sender` principal. In contrast to `stx-transfer?`,
any user can transfer the assets. When used, relevant guards need to be added.

This function returns (ok true) if the transfer is successful. In the event of an unsuccessful transfer it returns
one of the following error codes:

* `(err u1)` -- `sender` does not have enough balance to transfer
* `(err u2)` -- `sender` and `recipient` are the same principal
* `(err u3)` -- amount to send is non-positive
",
    example: "
(define-fungible-token stackaroo)
(ft-mint? stackaroo u100 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
(ft-transfer? stackaroo u50 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
(ft-transfer? stackaroo u60 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (err u1)
"
};

const ASSET_TRANSFER: SpecialAPI = SpecialAPI {
    input_type: "AssetName, A, principal, principal",
    snippet: "nft-transfer? ${1:asset-name} ${2:asset-identifier} ${3:sender} ${4:recipient}",
    output_type: "(response bool uint)",
    signature: "(nft-transfer? asset-class asset-identifier sender recipient)",
    description: "`nft-transfer?` is used to change the owner of an asset identified by `asset-identifier`
from `sender` to `recipient`. The `asset-class` must have been defined by `define-non-fungible-token` and `asset-identifier`
must be of the type specified in that definition. In contrast to `stx-transfer?`, any user can transfer the asset.
When used, relevant guards need to be added.

This function returns (ok true) if the transfer is successful. In the event of an unsuccessful transfer it returns
one of the following error codes:

* `(err u1)` -- `sender` does not own the asset
* `(err u2)` -- `sender` and `recipient` are the same principal
* `(err u3)` -- asset identified by asset-identifier does not exist
",
    example: "
(define-non-fungible-token stackaroo (string-ascii 40))
(nft-mint? stackaroo \"Roo\" 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
(nft-transfer? stackaroo \"Roo\" 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
(nft-transfer? stackaroo \"Roo\" 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (err u1)
(nft-transfer? stackaroo \"Stacka\" 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (err u3)
"
};

const GET_TOKEN_SUPPLY: SpecialAPI = SpecialAPI {
    input_type: "TokenName",
    snippet: "ft-get-supply ${1:token-name}",
    output_type: "uint",
    signature: "(ft-get-supply token-name)",
    description: "`ft-get-balance` returns `token-name` circulating supply.
The token type must have been defined using `define-fungible-token`.",
    example: "
(define-fungible-token stackaroo)
(ft-mint? stackaroo u100 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
(ft-get-supply stackaroo) ;; Returns u100
",
};

const BURN_TOKEN: SpecialAPI = SpecialAPI {
    input_type: "TokenName, uint, principal",
    snippet: "ft-burn? ${1:asset-name} ${2:amount} ${3:sender}",
    output_type: "(response bool uint)",
    signature: "(ft-burn? token-name amount sender)",
    description: "`ft-burn?` is used to decrease the token balance for the `sender` principal for a token
type defined using `define-fungible-token`. The decreased token balance is _not_ transfered to another principal, but
rather destroyed, reducing the circulating supply.

On a successful burn, it returns `(ok true)`. The burn may fail with error code:

* `(err u1)` -- `sender` does not have enough balance to burn this amount or the amount specified is not positive
",
    example: "
(define-fungible-token stackaroo)
(ft-mint? stackaroo u100 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
(ft-burn? stackaroo u50 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
"
};

const BURN_ASSET: SpecialAPI = SpecialAPI {
    input_type: "AssetName, A, principal",
    snippet: "nft-burn? ${1:asset-name} ${2:asset-identifier} ${3:sender}",
    output_type: "(response bool uint)",
    signature: "(nft-burn? asset-class asset-identifier sender)",
    description: "`nft-burn?` is used to burn an asset that the `sender` principal owns.
The asset must have been defined using `define-non-fungible-token`, and the supplied
`asset-identifier` must be of the same type specified in that definition.

On a successful burn, it returns `(ok true)`. In the event of an unsuccessful burn it
returns one of the following error codes:

* `(err u1)` -- `sender` does not own the specified asset
* `(err u3)` -- the asset specified by `asset-identifier` does not exist
",
    example: "
(define-non-fungible-token stackaroo (string-ascii 40))
(nft-mint? stackaroo \"Roo\" 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
(nft-burn? stackaroo \"Roo\" 'SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF) ;; Returns (ok true)
",
};

const STX_GET_BALANCE: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "stx-get-balance ${1:owner}",
    signature: "(stx-get-balance owner)",
    description: "`stx-get-balance` is used to query the STX balance of the `owner` principal.

This function returns the (unlocked) STX balance, in microstacks (1 STX = 1,000,000 microstacks), of the
`owner` principal. The result is the same as `(get unlocked (stx-account user))`.
In the event that the `owner` principal isn't materialized, it returns 0.
",
    example: "
(stx-get-balance 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR) ;; Returns u0
(stx-get-balance (as-contract tx-sender)) ;; Returns u1000
",
};

const STX_GET_ACCOUNT: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "stx-account ${1:owner}",
    signature: "(stx-account owner)",
    description: "`stx-account` is used to query the STX account of the `owner` principal.

This function returns a tuple with the canonical account representation for an STX account.
This includes the current amount of unlocked STX, the current amount of locked STX, and the
unlock height for any locked STX, all denominated in microstacks.
",
    example: r#"
(stx-account 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR) ;; Returns (tuple (locked u0) (unlock-height u0) (unlocked u0))
(stx-account (as-contract tx-sender)) ;; Returns (tuple (locked u0) (unlock-height u0) (unlocked u1000))
"#,
};

const STX_TRANSFER: SpecialAPI = SpecialAPI {
    input_type: "uint, principal, principal, buff",
    snippet: "stx-transfer? ${1:amount} ${2:sender} ${3:recipient}",
    output_type: "(response bool uint)",
    signature: "(stx-transfer? amount sender recipient)",
    description: "`stx-transfer?` is used to increase the STX balance for the `recipient` principal
by debiting the `sender` principal by `amount`, specified in microstacks. The `sender` principal
 _must_ be equal to the current context's `tx-sender`.

This function returns (ok true) if the transfer is successful. In the event of an unsuccessful transfer it returns
one of the following error codes:

* `(err u1)` -- `sender` does not have enough balance to transfer
* `(err u2)` -- `sender` and `recipient` are the same principal
* `(err u3)` -- amount to send is non-positive
* `(err u4)` -- the `sender` principal is not the current `tx-sender`
",
    example: r#"
(as-contract
  (stx-transfer? u60 tx-sender 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)) ;; Returns (ok true)
(as-contract
  (stx-transfer? u60 tx-sender 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)) ;; Returns (ok true)
(as-contract
  (stx-transfer? u50 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR tx-sender)) ;; Returns (err u4)
"#
};

const STX_TRANSFER_MEMO: SpecialAPI = SpecialAPI {
    input_type: "uint, principal, principal, buff",
    snippet: "stx-transfer-memo? ${1:amount} ${2:sender} ${3:recipient} ${4:memo}",
    output_type: "(response bool uint)",
    signature: "(stx-transfer-memo? amount sender recipient memo)",
    description: "`stx-transfer-memo?` is similar to `stx-transfer?`, except that it adds a `memo` field.

This function returns (ok true) if the transfer is successful, or, on an error, returns the same codes as `stx-transfer?`.
",
    example: r#"
(as-contract
  (stx-transfer-memo? u60 tx-sender 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR 0x010203)) ;; Returns (ok true)
"#
};

const STX_BURN: SimpleFunctionAPI = SimpleFunctionAPI {
    name: None,
    snippet: "stx-burn? ${1:amount} ${2:sender}",
    signature: "(stx-burn? amount sender)",
    description: "`stx-burn?` decreases the `sender` principal's STX holdings by `amount`,
specified in microstacks, by destroying the STX. The `sender` principal _must_ be equal to the current
context's `tx-sender`.

This function returns (ok true) if the burn is successful. In the event of an unsuccessful burn it returns
one of the following error codes:

* `(err u1)` -- `sender` does not have enough balance to burn
* `(err u3)` -- amount to burn is non-positive
* `(err u4)` -- the `sender` principal is not the current `tx-sender`
",
    example: "
(as-contract
  (stx-burn? u60 tx-sender)) ;; Returns (ok true)
(as-contract
  (stx-burn? u50 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)) ;; Returns (err u4)
"
};

const TO_CONSENSUS_BUFF: SpecialAPI = SpecialAPI {
    input_type: "any",
    snippet: "to-consensus-buff? ${1:value}",
    output_type: "(optional buff)",
    signature: "(to-consensus-buff? value)",
    description: "`to-consensus-buff?` is a special function that will serialize any
Clarity value into a buffer, using the SIP-005 serialization of the
Clarity value. Not all values can be serialized: some value's
consensus serialization is too large to fit in a Clarity buffer (this
is because of the type prefix in the consensus serialization).

If the value cannot fit as serialized into the maximum buffer size,
this returns `none`, otherwise, it will be
`(some consensus-serialized-buffer)`. During type checking, the
analyzed type of the result of this method will be the maximum possible
consensus buffer length based on the inferred type of the supplied value.
",
    example: r#"
(to-consensus-buff? 1) ;; Returns (some 0x0000000000000000000000000000000001)
(to-consensus-buff? u1) ;; Returns (some 0x0100000000000000000000000000000001)
(to-consensus-buff? true) ;; Returns (some 0x03)
(to-consensus-buff? false) ;; Returns (some 0x04)
(to-consensus-buff? none) ;; Returns (some 0x09)
(to-consensus-buff? 'SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR) ;; Returns (some 0x051fa46ff88886c2ef9762d970b4d2c63678835bd39d)
(to-consensus-buff? { abc: 3, def: 4 }) ;; Returns (some 0x0c00000002036162630000000000000000000000000000000003036465660000000000000000000000000000000004)
"#,
};

const FROM_CONSENSUS_BUFF: SpecialAPI = SpecialAPI {
    input_type: "type-signature(t), buff",
    snippet: "from-consensus-buff? ${1:type-signature} ${2:buffer}",
    output_type: "(optional t)",
    signature: "(from-consensus-buff? type-signature buffer)",
    description: "`from-consensus-buff?` is a special function that will deserialize a
buffer into a Clarity value, using the SIP-005 serialization of the
Clarity value. The type that `from-consensus-buff?` tries to deserialize
into is provided by the first parameter to the function. If it fails
to deserialize the type, the method returns `none`.
",
    example: r#"
(from-consensus-buff? int 0x0000000000000000000000000000000001) ;; Returns (some 1)
(from-consensus-buff? uint 0x0000000000000000000000000000000001) ;; Returns none
(from-consensus-buff? uint 0x0100000000000000000000000000000001) ;; Returns (some u1)
(from-consensus-buff? bool 0x0000000000000000000000000000000001) ;; Returns none
(from-consensus-buff? bool 0x03) ;; Returns (some true)
(from-consensus-buff? bool 0x04) ;; Returns (some false)
(from-consensus-buff? principal 0x051fa46ff88886c2ef9762d970b4d2c63678835bd39d) ;; Returns (some SZ2J6ZY48GV1EZ5V2V5RB9MP66SW86PYKKQ9H6DPR)
(from-consensus-buff? { abc: int, def: int } 0x0c00000002036162630000000000000000000000000000000003036465660000000000000000000000000000000004) ;; Returns (some (tuple (abc 3) (def 4)))
"#,
};

const REPLACE_AT: SpecialAPI = SpecialAPI {
    input_type: "sequence_A, uint, A",
    output_type: "(optional sequence_A)",
    snippet: "replace-at? ${1:sequence} ${2:index} ${3:element}",
    signature: "(replace-at? sequence index element)",
    description: "The `replace-at?` function takes in a sequence, an index, and an element,
and returns a new sequence with the data at the index position replaced with the given element.
The given element's type must match the type of the sequence, and must correspond to a single
index of the input sequence. The return type on success is the same type as the input sequence.

If the provided index is out of bounds, this functions returns `none`.
",
    example: r#"
(replace-at? u"ab" u1 u"c") ;; Returns (some u"ac")
(replace-at? 0x00112233 u2 0x44) ;; Returns (some 0x00114433)
(replace-at? "abcd" u3 "e") ;; Returns (some "abce")
(replace-at? (list 1) u0 10) ;; Returns (some (10))
(replace-at? (list (list 1) (list 2)) u0 (list 33)) ;; Returns (some ((33) (2)))
(replace-at? (list 1 2) u3 4) ;; Returns none
"#,
};

pub fn make_api_reference(function: &NativeFunctions) -> FunctionAPI {
    use crate::vm::functions::NativeFunctions::*;
    let name = function.get_name();
    match function {
        Add => make_for_simple_native(&ADD_API, function, name),
        ToUInt => make_for_simple_native(&TO_UINT_API, function, name),
        ToInt => make_for_simple_native(&TO_INT_API, function, name),
        Subtract => make_for_simple_native(&SUB_API, function, name),
        Multiply => make_for_simple_native(&MUL_API, function, name),
        Divide => make_for_simple_native(&DIV_API, function, name),
        BuffToIntLe => make_for_simple_native(&BUFF_TO_INT_LE_API, function, name),
        BuffToUIntLe => make_for_simple_native(&BUFF_TO_UINT_LE_API, function, name),
        BuffToIntBe => make_for_simple_native(&BUFF_TO_INT_BE_API, function, name),
        BuffToUIntBe => make_for_simple_native(&BUFF_TO_UINT_BE_API, function, name),
        IsStandard => make_for_simple_native(&IS_STANDARD_API, function, name),
        PrincipalDestruct => make_for_simple_native(&PRINCPIPAL_DESTRUCT_API, function, name),
        PrincipalConstruct => make_for_special(&PRINCIPAL_CONSTRUCT_API, function),
        StringToInt => make_for_simple_native(&STRING_TO_INT_API, function, name),
        StringToUInt => make_for_simple_native(&STRING_TO_UINT_API, function, name),
        IntToAscii => make_for_simple_native(&INT_TO_ASCII_API, function, name),
        IntToUtf8 => make_for_simple_native(&INT_TO_UTF8_API, function, name),
        CmpGeq => make_for_simple_native(&GEQ_API, function, name),
        CmpLeq => make_for_simple_native(&LEQ_API, function, name),
        CmpLess => make_for_simple_native(&LESS_API, function, name),
        CmpGreater => make_for_simple_native(&GREATER_API, function, name),
        Modulo => make_for_simple_native(&MOD_API, function, name),
        Power => make_for_simple_native(&POW_API, function, name),
        Sqrti => make_for_simple_native(&SQRTI_API, function, name),
        Log2 => make_for_simple_native(&LOG2_API, function, name),
        BitwiseXor => make_for_simple_native(&XOR_API, function, name),
        And => make_for_simple_native(&AND_API, function, name),
        Or => make_for_simple_native(&OR_API, function, name),
        Not => make_for_simple_native(&NOT_API, function, name),
        Equals => make_for_special(&EQUALS_API, function),
        If => make_for_special(&IF_API, function),
        Let => make_for_special(&LET_API, function),
        FetchVar => make_for_special(&FETCH_VAR_API, function),
        SetVar => make_for_special(&SET_VAR_API, function),
        Map => make_for_special(&MAP_API, function),
        Filter => make_for_special(&FILTER_API, function),
        Fold => make_for_special(&FOLD_API, function),
        Append => make_for_special(&APPEND_API, function),
        Concat => make_for_special(&CONCAT_API, function),
        AsMaxLen => make_for_special(&ASSERTS_MAX_LEN_API, function),
        Len => make_for_special(&LEN_API, function),
        ElementAt | ElementAtAlias => make_for_special(&ELEMENT_AT_API, function),
        IndexOf | IndexOfAlias => make_for_special(&INDEX_OF_API, function),
        Slice => make_for_special(&SLICE_API, function),
        ListCons => make_for_special(&LIST_API, function),
        FetchEntry => make_for_special(&FETCH_ENTRY_API, function),
        SetEntry => make_for_special(&SET_ENTRY_API, function),
        InsertEntry => make_for_special(&INSERT_ENTRY_API, function),
        DeleteEntry => make_for_special(&DELETE_ENTRY_API, function),
        TupleCons => make_for_special(&TUPLE_CONS_API, function),
        TupleGet => make_for_special(&TUPLE_GET_API, function),
        TupleMerge => make_for_special(&TUPLE_MERGE_API, function),
        Begin => make_for_special(&BEGIN_API, function),
        Hash160 => make_for_special(&HASH160_API, function),
        Sha256 => make_for_special(&SHA256_API, function),
        Sha512 => make_for_special(&SHA512_API, function),
        Sha512Trunc256 => make_for_special(&SHA512T256_API, function),
        Keccak256 => make_for_special(&KECCAK256_API, function),
        Secp256k1Recover => make_for_special(&SECP256K1RECOVER_API, function),
        Secp256k1Verify => make_for_special(&SECP256K1VERIFY_API, function),
        Print => make_for_special(&PRINT_API, function),
        ContractCall => make_for_special(&CONTRACT_CALL_API, function),
        ContractOf => make_for_special(&CONTRACT_OF_API, function),
        PrincipalOf => make_for_special(&PRINCIPAL_OF_API, function),
        AsContract => make_for_special(&AS_CONTRACT_API, function),
        GetBlockInfo => make_for_special(&GET_BLOCK_INFO_API, function),
        GetBurnBlockInfo => make_for_special(&GET_BURN_BLOCK_INFO_API, function),
        GetStacksBlockInfo => make_for_special(&GET_STACKS_BLOCK_INFO_API, function),
        GetTenureInfo => make_for_special(&GET_TENURE_INFO_API, function),
        ConsOkay => make_for_special(&CONS_OK_API, function),
        ConsError => make_for_special(&CONS_ERR_API, function),
        ConsSome => make_for_special(&CONS_SOME_API, function),
        DefaultTo => make_for_special(&DEFAULT_TO_API, function),
        Asserts => make_for_special(&ASSERTS_API, function),
        UnwrapRet => make_for_special(&EXPECTS_API, function),
        UnwrapErrRet => make_for_special(&EXPECTS_ERR_API, function),
        Unwrap => make_for_special(&UNWRAP_API, function),
        UnwrapErr => make_for_special(&UNWRAP_ERR_API, function),
        Match => make_for_special(&MATCH_API, function),
        TryRet => make_for_special(&TRY_API, function),
        IsOkay => make_for_special(&IS_OK_API, function),
        IsNone => make_for_special(&IS_NONE_API, function),
        IsErr => make_for_special(&IS_ERR_API, function),
        IsSome => make_for_special(&IS_SOME_API, function),
        MintAsset => make_for_special(&MINT_ASSET, function),
        MintToken => make_for_special(&MINT_TOKEN, function),
        GetTokenBalance => make_for_special(&GET_BALANCE, function),
        GetAssetOwner => make_for_special(&GET_OWNER, function),
        TransferToken => make_for_special(&TOKEN_TRANSFER, function),
        TransferAsset => make_for_special(&ASSET_TRANSFER, function),
        BurnToken => make_for_special(&BURN_TOKEN, function),
        BurnAsset => make_for_special(&BURN_ASSET, function),
        GetTokenSupply => make_for_special(&GET_TOKEN_SUPPLY, function),
        AtBlock => make_for_special(&AT_BLOCK, function),
        GetStxBalance => make_for_simple_native(&STX_GET_BALANCE, function, name),
        StxGetAccount => make_for_simple_native(&STX_GET_ACCOUNT, function, name),
        StxTransfer => make_for_special(&STX_TRANSFER, function),
        StxTransferMemo => make_for_special(&STX_TRANSFER_MEMO, function),
        StxBurn => make_for_simple_native(&STX_BURN, function, name),
        ToConsensusBuff => make_for_special(&TO_CONSENSUS_BUFF, function),
        FromConsensusBuff => make_for_special(&FROM_CONSENSUS_BUFF, function),
        ReplaceAt => make_for_special(&REPLACE_AT, function),
        BitwiseXor2 => make_for_simple_native(&BITWISE_XOR_API, function, name),
        BitwiseAnd => make_for_simple_native(&BITWISE_AND_API, function, name),
        BitwiseOr => make_for_simple_native(&BITWISE_OR_API, function, name),
        BitwiseNot => make_for_simple_native(&BITWISE_NOT_API, function, name),
        BitwiseLShift => make_for_simple_native(&BITWISE_LEFT_SHIFT_API, function, name),
        BitwiseRShift => make_for_simple_native(&BITWISE_RIGHT_SHIFT_API, function, name),
    }
}

pub fn make_keyword_reference(variable: &NativeVariables) -> Option<KeywordAPI> {
    let keyword = match variable {
        NativeVariables::TxSender => TX_SENDER_KEYWORD.clone(),
        NativeVariables::ContractCaller => CONTRACT_CALLER_KEYWORD.clone(),
        NativeVariables::NativeNone => NONE_KEYWORD.clone(),
        NativeVariables::NativeTrue => TRUE_KEYWORD.clone(),
        NativeVariables::NativeFalse => FALSE_KEYWORD.clone(),
        NativeVariables::BlockHeight => BLOCK_HEIGHT.clone(),
        NativeVariables::StacksBlockHeight => STACKS_BLOCK_HEIGHT_KEYWORD.clone(),
        NativeVariables::TenureHeight => TENURE_HEIGHT_KEYWORD.clone(),
        NativeVariables::BurnBlockHeight => BURN_BLOCK_HEIGHT.clone(),
        NativeVariables::TotalLiquidMicroSTX => TOTAL_LIQUID_USTX_KEYWORD.clone(),
        NativeVariables::Regtest => REGTEST_KEYWORD.clone(),
        NativeVariables::Mainnet => MAINNET_KEYWORD.clone(),
        NativeVariables::ChainId => CHAINID_KEYWORD.clone(),
        NativeVariables::TxSponsor => TX_SPONSOR_KEYWORD.clone(),
    };
    Some(KeywordAPI {
        name: keyword.name,
        snippet: keyword.snippet,
        output_type: keyword.output_type,
        description: keyword.description,
        example: keyword.example,
        min_version: variable.get_min_version(),
        max_version: variable.get_max_version(),
    })
}

fn make_for_special(api: &SpecialAPI, function: &NativeFunctions) -> FunctionAPI {
    FunctionAPI {
        name: function.get_name(),
        snippet: api.snippet.to_string(),
        input_type: api.input_type.to_string(),
        output_type: api.output_type.to_string(),
        signature: api.signature.to_string(),
        description: api.description.to_string(),
        example: api.example.to_string(),
        min_version: function.get_min_version(),
        max_version: function.get_max_version(),
    }
}

fn make_for_define(api: &DefineAPI, name: String) -> FunctionAPI {
    FunctionAPI {
        name,
        snippet: api.snippet.to_string(),
        input_type: api.input_type.to_string(),
        output_type: api.output_type.to_string(),
        signature: api.signature.to_string(),
        description: api.description.to_string(),
        example: api.example.to_string(),
        min_version: ClarityVersion::Clarity1,
        max_version: None,
    }
}

pub fn make_define_reference(define_type: &DefineFunctions) -> FunctionAPI {
    use crate::vm::functions::define::DefineFunctions::*;
    let name = define_type.get_name();
    match define_type {
        Constant => make_for_define(&DEFINE_CONSTANT_API, name),
        PrivateFunction => make_for_define(&DEFINE_PRIVATE_API, name),
        PublicFunction => make_for_define(&DEFINE_PUBLIC_API, name),
        Map => make_for_define(&DEFINE_MAP_API, name),
        NonFungibleToken => make_for_define(&DEFINE_ASSET_API, name),
        FungibleToken => make_for_define(&DEFINE_TOKEN_API, name),
        ReadOnlyFunction => make_for_define(&DEFINE_READ_ONLY_API, name),
        PersistedVariable => make_for_define(&DEFINE_DATA_VAR_API, name),
        Trait => make_for_define(&DEFINE_TRAIT_API, name),
        UseTrait => make_for_define(&USE_TRAIT_API, name),
        ImplTrait => make_for_define(&IMPL_TRAIT_API, name),
    }
}

fn make_all_api_reference() -> ReferenceAPIs {
    let mut functions: Vec<_> = NativeFunctions::ALL
        .iter()
        .map(make_api_reference)
        .collect();
    for data_type in DefineFunctions::ALL.iter() {
        functions.push(make_define_reference(data_type))
    }
    functions.sort_by(|x, y| x.name.cmp(&y.name));

    let mut keywords: Vec<_> = NativeVariables::ALL
        .iter()
        .filter_map(make_keyword_reference)
        .collect();

    keywords.sort_by_key(|x| x.name);

    ReferenceAPIs {
        functions,
        keywords,
    }
}

#[allow(clippy::expect_used)]
pub fn make_json_api_reference() -> String {
    let api_out = make_all_api_reference();
    serde_json::to_string(&api_out)
        .expect("Failed to serialize documentation")
        .to_string()
}

#[cfg(test)]
mod test {
    use stacks_common::address::AddressHashMode;
    use stacks_common::consts::{CHAIN_ID_TESTNET, PEER_VERSION_EPOCH_2_1};
    use stacks_common::types::chainstate::{
        BlockHeaderHash, BurnchainHeaderHash, ConsensusHash, SortitionId, StacksAddress,
        StacksBlockId, VRFSeed,
    };
    use stacks_common::types::{Address, StacksEpochId};
    use stacks_common::util::hash::hex_bytes;

    use super::{get_input_type_string, make_all_api_reference, make_json_api_reference};
    use crate::vm::analysis::type_check;
    use crate::vm::ast::ASTRules;
    use crate::vm::contexts::OwnedEnvironment;
    use crate::vm::costs::ExecutionCost;
    use crate::vm::database::{
        BurnStateDB, ClarityDatabase, HeadersDB, MemoryBackingStore, STXBalance,
    };
    use crate::vm::docs::get_output_type_string;
    use crate::vm::types::signatures::{FunctionArgSignature, FunctionReturnsSignature, ASCII_40};
    use crate::vm::types::{
        BufferLength, FunctionType, PrincipalData, SequenceSubtype, StringSubtype, TupleData,
        TypeSignature,
    };
    use crate::vm::{
        ast, eval_all, execute, ClarityVersion, ContractContext, Error, GlobalContext,
        LimitedCostTracker, QualifiedContractIdentifier, StacksEpoch, Value,
    };

    struct DocHeadersDB {}
    const DOC_HEADER_DB: DocHeadersDB = DocHeadersDB {};

    impl MemoryBackingStore {
        pub fn as_docs_clarity_db(&mut self) -> ClarityDatabase<'_> {
            ClarityDatabase::new(self, &DOC_HEADER_DB, &DOC_POX_STATE_DB)
        }
    }

    impl HeadersDB for DocHeadersDB {
        fn get_burn_header_hash_for_block(
            &self,
            _bhh: &StacksBlockId,
        ) -> Option<BurnchainHeaderHash> {
            None
        }
        fn get_consensus_hash_for_block(
            &self,
            _bhh: &StacksBlockId,
            _epoch: &StacksEpochId,
        ) -> Option<ConsensusHash> {
            Some(ConsensusHash([0; 20]))
        }
        fn get_vrf_seed_for_block(
            &self,
            _bhh: &StacksBlockId,
            epoch: &StacksEpochId,
        ) -> Option<VRFSeed> {
            Some(
                VRFSeed::from_hex(
                    "f490de2920c8a35fabeb13208852aa28c76f9be9b03a4dd2b3c075f7a26923b4",
                )
                .unwrap(),
            )
        }
        fn get_stacks_block_header_hash_for_block(
            &self,
            _id_bhh: &StacksBlockId,
            _epoch: &StacksEpochId,
        ) -> Option<BlockHeaderHash> {
            Some(
                BlockHeaderHash::from_hex(
                    "374708fff7719dd5979ec875d56cd2286f6d3cf7ec317a3b25632aab28ec37bb",
                )
                .unwrap(),
            )
        }
        fn get_burn_block_time_for_block(
            &self,
            _id_bhh: &StacksBlockId,
            _epoch: Option<&StacksEpochId>,
        ) -> Option<u64> {
            Some(1557860301)
        }
        fn get_stacks_block_time_for_block(&self, _id_bhh: &StacksBlockId) -> Option<u64> {
            Some(1557860302)
        }
        fn get_burn_block_height_for_block(&self, _id_bhh: &StacksBlockId) -> Option<u32> {
            Some(567890)
        }
        fn get_miner_address(
            &self,
            _id_bhh: &StacksBlockId,
            _epoch: &StacksEpochId,
        ) -> Option<StacksAddress> {
            None
        }
        fn get_burnchain_tokens_spent_for_block(
            &self,
            id_bhh: &StacksBlockId,
            _epoch: &StacksEpochId,
        ) -> Option<u128> {
            Some(12345)
        }

        fn get_burnchain_tokens_spent_for_winning_block(
            &self,
            id_bhh: &StacksBlockId,
            _epoch: &StacksEpochId,
        ) -> Option<u128> {
            Some(2345)
        }

        fn get_tokens_earned_for_block(
            &self,
            id_bhh: &StacksBlockId,
            _epoch: &StacksEpochId,
        ) -> Option<u128> {
            Some(12000)
        }

        fn get_stacks_height_for_tenure_height(
            &self,
            _tip: &StacksBlockId,
            tenure_height: u32,
        ) -> Option<u32> {
            Some(tenure_height)
        }
    }

    struct DocBurnStateDB {}
    const DOC_POX_STATE_DB: DocBurnStateDB = DocBurnStateDB {};

    impl BurnStateDB for DocBurnStateDB {
        fn get_tip_burn_block_height(&self) -> Option<u32> {
            Some(0x9abc)
        }

        fn get_tip_sortition_id(&self) -> Option<SortitionId> {
            Some(SortitionId([0u8; 32]))
        }

        fn get_burn_block_height(&self, _sortition_id: &SortitionId) -> Option<u32> {
            Some(5678)
        }
        fn get_burn_header_hash(
            &self,
            height: u32,
            _sortition_id: &SortitionId,
        ) -> Option<BurnchainHeaderHash> {
            Some(
                BurnchainHeaderHash::from_hex(
                    "e67141016c88a7f1203eca0b4312f2ed141531f59303a1c267d7d83ab6b977d8",
                )
                .unwrap(),
            )
        }
        fn get_sortition_id_from_consensus_hash(
            &self,
            consensus_hash: &ConsensusHash,
        ) -> Option<SortitionId> {
            Some(SortitionId([0u8; 32]))
        }

        fn get_stacks_epoch(&self, height: u32) -> Option<StacksEpoch> {
            Some(StacksEpoch {
                epoch_id: StacksEpochId::Epoch21,
                start_height: 0,
                end_height: u64::MAX,
                block_limit: ExecutionCost::max_value(),
                network_epoch: PEER_VERSION_EPOCH_2_1,
            })
        }
        fn get_burn_start_height(&self) -> u32 {
            0
        }

        fn get_v1_unlock_height(&self) -> u32 {
            u32::MAX
        }

        fn get_v2_unlock_height(&self) -> u32 {
            u32::MAX
        }

        fn get_v3_unlock_height(&self) -> u32 {
            u32::MAX
        }

        fn get_pox_3_activation_height(&self) -> u32 {
            u32::MAX
        }

        fn get_pox_4_activation_height(&self) -> u32 {
            u32::MAX
        }

        fn get_pox_prepare_length(&self) -> u32 {
            panic!("Docs db should not return PoX info")
        }

        fn get_pox_reward_cycle_length(&self) -> u32 {
            panic!("Docs db should not return PoX info")
        }

        fn get_pox_rejection_fraction(&self) -> u64 {
            panic!("Docs db should not return PoX info")
        }
        fn get_stacks_epoch_by_epoch_id(&self, epoch_id: &StacksEpochId) -> Option<StacksEpoch> {
            self.get_stacks_epoch(0)
        }
        fn get_ast_rules(&self, height: u32) -> ASTRules {
            ASTRules::PrecheckSize
        }
        fn get_pox_payout_addrs(
            &self,
            height: u32,
            sortition_id: &SortitionId,
        ) -> Option<(Vec<TupleData>, u128)> {
            // (some (tuple (addrs ((tuple (hashbytes 0x395f3643cea07ec4eec73b4d9a973dcce56b9bf1) (version 0x00)) (tuple (hashbytes 0x7c6775e20e3e938d2d7e9d79ac310108ba501ddb) (version 0x01)))) (payout u123)))

            Some((
                vec![
                    TupleData::from_data(vec![
                        ("version".into(), Value::buff_from(vec![0u8]).unwrap()),
                        (
                            "hashbytes".into(),
                            Value::buff_from(
                                hex_bytes("395f3643cea07ec4eec73b4d9a973dcce56b9bf1").unwrap(),
                            )
                            .unwrap(),
                        ),
                    ])
                    .unwrap(),
                    TupleData::from_data(vec![
                        ("version".into(), Value::buff_from(vec![1u8]).unwrap()),
                        (
                            "hashbytes".into(),
                            Value::buff_from(
                                hex_bytes("7c6775e20e3e938d2d7e9d79ac310108ba501ddb").unwrap(),
                            )
                            .unwrap(),
                        ),
                    ])
                    .unwrap(),
                ],
                123,
            ))
        }
    }

    fn docs_execute(store: &mut MemoryBackingStore, program: &str) {
        // execute the program, iterating at each ";; Returns" comment
        // there are maybe more rust-y ways of doing this, but this is the simplest.
        let mut segments = vec![];
        let mut current_segment: String = "".into();
        for line in program.lines() {
            current_segment.push_str(line);
            current_segment.push('\n');
            if line.contains(";;") && line.contains("Returns ") {
                segments.push(current_segment);
                current_segment = "".into();
            }
        }
        if !current_segment.is_empty() {
            segments.push(current_segment);
        }

        let contract_id = QualifiedContractIdentifier::local("docs-test").unwrap();

        {
            let mut analysis_db = store.as_analysis_db();
            let whole_contract = segments.join("\n");
            eprintln!("{}", whole_contract);
            let mut parsed = ast::build_ast(
                &contract_id,
                &whole_contract,
                &mut (),
                ClarityVersion::latest(),
                StacksEpochId::latest(),
            )
            .unwrap()
            .expressions;

            let analysis = type_check(
                &contract_id,
                &mut parsed,
                &mut analysis_db,
                false,
                &StacksEpochId::latest(),
                &ClarityVersion::latest(),
            )
            .expect("Failed to type check");
        }

        let mut type_results = vec![];
        let mut total_example = "".to_string();
        for segment in segments.iter() {
            total_example.push_str(segment);
            let mut parsed = ast::build_ast(
                &contract_id,
                &total_example,
                &mut (),
                ClarityVersion::latest(),
                StacksEpochId::latest(),
            )
            .unwrap()
            .expressions;

            let mut analysis_db = store.as_analysis_db();
            let analysis = type_check(
                &contract_id,
                &mut parsed,
                &mut analysis_db,
                false,
                &StacksEpochId::latest(),
                &ClarityVersion::latest(),
            )
            .expect("Failed to type check");
            type_results.push(
                analysis
                    .type_map
                    .as_ref()
                    .unwrap()
                    .get_type_expected(analysis.expressions.last().unwrap())
                    .cloned(),
            );
        }

        let conn = store.as_docs_clarity_db();
        let mut contract_context =
            ContractContext::new(contract_id.clone(), ClarityVersion::latest());
        let mut global_context = GlobalContext::new(
            false,
            CHAIN_ID_TESTNET,
            conn,
            LimitedCostTracker::new_free(),
            StacksEpochId::latest(),
        );

        global_context
            .execute(|g| {
                for (segment, type_result) in segments.iter().zip(type_results.iter()) {
                    let expected = if segment.contains("Returns ") {
                        let expects_start = segment.rfind("Returns ").unwrap() + "Returns ".len();
                        Some(segment[expects_start..].trim().to_string())
                    } else {
                        None
                    };

                    eprintln!("{}", segment);

                    let result = {
                        let parsed = ast::build_ast(
                            &contract_id,
                            segment,
                            &mut (),
                            ClarityVersion::latest(),
                            StacksEpochId::latest(),
                        )
                        .unwrap()
                        .expressions;

                        eval_all(&parsed, &mut contract_context, g, None).unwrap()
                    };

                    if let Some(expected) = expected {
                        assert_eq!(expected, result.as_ref().unwrap().to_string());
                        assert!(
                            type_result.as_ref().unwrap().admits(&StacksEpochId::latest(), result.as_ref().unwrap()).unwrap(),
                            "Type checker's expected type must admit result. Expected type = {}. Result = {}",
                            type_result.as_ref().unwrap(),
                            result.as_ref().unwrap()
                        );
                    }
                }
                Ok(())
            })
            .unwrap();
    }

    #[test]
    fn ensure_docgen_runs() {
        // add a test to make sure that we don't inadvertently break
        //  docgen in a panic-y way.
        make_json_api_reference();
    }

    #[test]
    fn test_examples() {
        // Execute test examples against the latest version of Clarity
        let apis = make_all_api_reference();
        let token_contract_content = include_str!("../../../../sample/contracts/tokens.clar");
        for func_api in apis.functions.iter() {
            if func_api.name == "at-block" {
                eprintln!("Skipping at-block, because it cannot be evaluated without a MARF");
                continue;
            }
            if func_api.name == "get-block-info?" {
                eprintln!(
                    "Skipping get-block-info?, because it cannot be evaluated without a MARF"
                );
                continue;
            }

            let mut store = MemoryBackingStore::new();
            // first, load the samples for contract-call
            // and give the doc environment's contract some STX
            {
                let contract_id = QualifiedContractIdentifier::local("tokens").unwrap();
                let trait_def_id = QualifiedContractIdentifier::parse(
                    "SPAXYA5XS51713FDTQ8H94EJ4V579CXMTRNBZKSF.token-a",
                )
                .unwrap();

                {
                    let mut analysis_db = store.as_analysis_db();
                    let mut parsed = ast::build_ast(
                        &contract_id,
                        token_contract_content,
                        &mut (),
                        ClarityVersion::latest(),
                        StacksEpochId::latest(),
                    )
                    .unwrap()
                    .expressions;

                    type_check(
                        &contract_id,
                        &mut parsed,
                        &mut analysis_db,
                        true,
                        &StacksEpochId::latest(),
                        &ClarityVersion::latest(),
                    )
                    .expect("Failed to type check sample/contracts/tokens");
                }

                {
                    let mut analysis_db = store.as_analysis_db();
                    let mut parsed = ast::build_ast(
                        &trait_def_id,
                        super::DEFINE_TRAIT_API.example,
                        &mut (),
                        ClarityVersion::latest(),
                        StacksEpochId::latest(),
                    )
                    .unwrap()
                    .expressions;

                    type_check(
                        &trait_def_id,
                        &mut parsed,
                        &mut analysis_db,
                        true,
                        &StacksEpochId::latest(),
                        &ClarityVersion::latest(),
                    )
                    .expect("Failed to type check sample/contracts/tokens");
                }

                let conn = store.as_docs_clarity_db();
                let docs_test_id = QualifiedContractIdentifier::local("docs-test").unwrap();
                let docs_principal_id = PrincipalData::Contract(docs_test_id);
                let mut env = OwnedEnvironment::new(conn, StacksEpochId::latest());
                let balance = STXBalance::initial(1000);
                env.execute_in_env::<_, _, ()>(
                    QualifiedContractIdentifier::local("tokens").unwrap().into(),
                    None,
                    None,
                    |e| {
                        let mut snapshot = e
                            .global_context
                            .database
                            .get_stx_balance_snapshot_genesis(&docs_principal_id)
                            .unwrap();
                        snapshot.set_balance(balance);
                        snapshot.save().unwrap();
                        e.global_context
                            .database
                            .increment_ustx_liquid_supply(100000)
                            .unwrap();
                        Ok(())
                    },
                )
                .unwrap();

                env.initialize_contract(
                    contract_id,
                    token_contract_content,
                    None,
                    ASTRules::PrecheckSize,
                )
                .unwrap();

                env.initialize_contract(
                    trait_def_id,
                    super::DEFINE_TRAIT_API.example,
                    None,
                    ASTRules::PrecheckSize,
                )
                .unwrap();
            }

            let example = &func_api.example;
            let without_throws: String = example
                .lines()
                .filter(|x| !x.contains(";; Throws"))
                .collect::<Vec<_>>()
                .join("\n");
            let the_throws = example.lines().filter(|x| x.contains(";; Throws"));
            docs_execute(&mut store, &without_throws);
            for expect_err in the_throws {
                eprintln!("{}", expect_err);
                execute(expect_err).unwrap_err();
            }
        }
    }

    #[test]
    fn test_get_input_type_string_binary() {
        let mut result: String;
        let ret = FunctionReturnsSignature::Fixed(TypeSignature::IntType);

        let mut function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Single(TypeSignature::UIntType),
            ret.clone(),
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "int, uint");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Union(vec![TypeSignature::IntType, TypeSignature::UIntType]),
            FunctionArgSignature::Single(TypeSignature::IntType),
            ret.clone(),
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "int, int | uint, int");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Union(vec![TypeSignature::IntType, TypeSignature::UIntType]),
            FunctionArgSignature::Union(vec![TypeSignature::UIntType, TypeSignature::IntType]),
            ret.clone(),
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "int, uint | int, int | uint, uint | uint, int");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Union(vec![TypeSignature::UIntType, TypeSignature::IntType]),
            ret.clone(),
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "int, uint | int, int");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Union(vec![ASCII_40, TypeSignature::IntType]),
            ret.clone(),
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "int, (string-ascii 40) | int, int");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Union(vec![
                TypeSignature::UIntType,
                TypeSignature::IntType,
                TypeSignature::PrincipalType,
            ]),
            ret.clone(),
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "int, uint | int, int | int, principal");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Union(vec![
                TypeSignature::UIntType,
                TypeSignature::PrincipalType,
                TypeSignature::IntType,
            ]),
            FunctionArgSignature::Union(vec![
                TypeSignature::UIntType,
                TypeSignature::IntType,
                TypeSignature::PrincipalType,
            ]),
            ret,
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "uint, uint | uint, int | uint, principal | principal, uint | principal, int | principal, principal | int, uint | int, int | int, principal");
    }

    #[test]
    fn test_get_input_type_string_unionargs() {
        let mut result: String;
        let ret = TypeSignature::BoolType;

        let mut function_type = FunctionType::UnionArgs(vec![TypeSignature::UIntType], ret.clone());
        result = get_input_type_string(&function_type);
        assert_eq!(result, "uint");

        function_type = FunctionType::UnionArgs(
            vec![TypeSignature::UIntType, TypeSignature::IntType],
            ret.clone(),
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "uint | int");

        function_type = FunctionType::UnionArgs(
            vec![
                TypeSignature::UIntType,
                TypeSignature::IntType,
                TypeSignature::PrincipalType,
            ],
            ret,
        );
        result = get_input_type_string(&function_type);
        assert_eq!(result, "uint | int | principal");
    }

    #[test]
    fn test_get_input_type_string_variadic() {
        let mut result: String;
        let ret = TypeSignature::BoolType;

        let mut function_type = FunctionType::Variadic(TypeSignature::IntType, ret.clone());
        result = get_input_type_string(&function_type);
        assert_eq!(result, "int, ...");

        function_type = FunctionType::Variadic(TypeSignature::PrincipalType, ret);
        result = get_input_type_string(&function_type);
        assert_eq!(result, "principal, ...");
    }

    #[test]
    fn test_get_output_type_string_binary() {
        let mut result: String;
        let mut function_type: FunctionType;

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionReturnsSignature::Fixed(TypeSignature::PrincipalType),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "principal");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionReturnsSignature::TypeOfArgAtPosition(0),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "int");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionReturnsSignature::TypeOfArgAtPosition(1),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "uint");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Union(vec![TypeSignature::IntType, TypeSignature::UIntType]),
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionReturnsSignature::TypeOfArgAtPosition(0),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "int | uint");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Union(vec![TypeSignature::IntType, TypeSignature::UIntType]),
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionReturnsSignature::TypeOfArgAtPosition(1),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "uint");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionArgSignature::Union(vec![TypeSignature::IntType, TypeSignature::UIntType]),
            FunctionReturnsSignature::TypeOfArgAtPosition(0),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "uint");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionArgSignature::Union(vec![TypeSignature::IntType, TypeSignature::UIntType]),
            FunctionReturnsSignature::TypeOfArgAtPosition(1),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "int | uint");

        function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionArgSignature::Union(vec![
                TypeSignature::IntType,
                TypeSignature::UIntType,
                TypeSignature::PrincipalType,
                ASCII_40,
            ]),
            FunctionReturnsSignature::TypeOfArgAtPosition(1),
        );
        result = get_output_type_string(&function_type);
        assert_eq!(result, "int | uint | principal | (string-ascii 40)");
    }

    #[test]
    #[should_panic(expected = "Index out of range")]
    fn test_get_output_type_string_binary_arg_at_pos_out_of_range_panics() {
        let function_type = FunctionType::Binary(
            FunctionArgSignature::Single(TypeSignature::IntType),
            FunctionArgSignature::Single(TypeSignature::UIntType),
            FunctionReturnsSignature::TypeOfArgAtPosition(2),
        );
        get_output_type_string(&function_type);
    }
}
