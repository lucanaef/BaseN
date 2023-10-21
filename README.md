# BaseN
Formally verified implementations of the [Base16](https://datatracker.ietf.org/doc/html/rfc4648#section-8), [Base32](https://datatracker.ietf.org/doc/html/rfc4648#section-6) and [Base64](https://datatracker.ietf.org/doc/html/rfc4648#section-4) data encodings ([RFC 4648](https://datatracker.ietf.org/doc/rfc4648/)) using [HOL4 theorem prover](https://hol-theorem-prover.org/) and [CakeML](https://cakeml.org).

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