# BaseN
Formally verified implementations of the Base16, Base32 and Base64 data encodings ([RFC 4648](https://datatracker.ietf.org/doc/rfc4648/)).

## Structure
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