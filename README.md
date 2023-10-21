# BaseN
Formally verified implementations of the [Base16](https://datatracker.ietf.org/doc/html/rfc4648#section-8), [Base32](https://datatracker.ietf.org/doc/html/rfc4648#section-6) and [Base64](https://datatracker.ietf.org/doc/html/rfc4648#section-4) data encodings ([RFC 4648](https://datatracker.ietf.org/doc/rfc4648/)) using the [HOL4 theorem prover](https://hol-theorem-prover.org/) and [CakeML](https://cakeml.org).

## Structure
Each data encoding is implemented in its own theory script (i.e. `base16Script`, `base32Script` and `base64Script`) using the following structure of four definitions in order to decouple bit manipulations from the specific encoding alphabets. Shared helper definitions and theorems are implemented in `baseNUtilsScript`.

                 :word8 list -> num list              :num list -> string
                       ┌──────────┐                       ┌──────────┐
    Encoding  ┌──────  │  *_ENC   │──────────────────────▶│  *_PAD   │  ──────┐
              │        └──────────┘                       └──────────┘        │
              │                                                               │
              │                                                               │
              │                                                               │
              │        ┌──────────┐                       ┌──────────┐        │
              └─────▶  │  *_DEC   │◀──────────────────────│ *_DEPAD  │  ◀─────┘  Decoding
                       └──────────┘                       └──────────┘
                 :num list -> word8 list              :string -> num list

## Verified Properties
The following theorems about the data encodings have been verified:

### Base16

| Theorem              | Property                                                 |
| -------------------- | -------------------------------------------------------- |
| `BASE16_ENC_DEC`     | `∀ns. wf_base16 ns ⇒ base16enc (base16dec ns) = ns`      |
| `BASE16_DEC_ENC`     | `∀ws. base16dec (base16enc ws) = ws`                     |

### Base32

| Theorem              | Property                                                 |
| -------------------- | -------------------------------------------------------- |
| `BASE32_ENC_DEC`     | `∀ns. wf_base32 ns ⇒ base32enc (base32dec ns) = ns`      |
| `BASE32_DEC_ENC`     | `∀ws. base32dec (base32enc ws) = ws`                     |
| `BASE32_PAD_DEPAD`   | `∀ns. wf_base32_ns ns ⇒ base32depad (base32pad ns) = ns` |
| `BASE32_DEPAD_PAD`   | `∀cs. wf_base32_cs cs ⇒ base32pad (base32depad cs) = cs` |

### Base64

| Theorem              | Property                                                 |
| -------------------- | -------------------------------------------------------- |
| `BASE64_ENC_DEC`     | `∀ns. wf_base64 ns ⇒ base64enc (base64dec ns) = ns`      |
| `BASE64_DEC_ENC`     | `∀ws. base64dec (base64enc ws) = ws`                     |
| `BASE64_PAD_DEPAD`   | `∀ns. wf_base64_ns ns ⇒ base64depad (base64pad ns) = ns` |
| `BASE64_DEPAD_PAD`   | `∀cs. wf_base64_cs cs ⇒ base64pad (base64depad cs) = cs` |

where `wf_base{16, 32, 64}_{cs, ns}` are necessary preconditions for the property to hold. For instance, `wf_base64_ns` states that the length of the list of alphabet indices mod 4 must not be 1 and that each index must be smaller than the length of the alphabet.