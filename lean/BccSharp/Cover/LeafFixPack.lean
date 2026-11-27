import BccSharp.Cover.LeafFix

set_option autoImplicit false

/-! # Packed witness lists for the fixed-point leaf checks

A generated module can state a support's witness list as `decodeWits k P` for
one literal natural number `P` instead of a list literal. The kernel decodes
`P` while it evaluates `supportOk`; the soundness theorems hold for any list,
so nothing about the decoder needs a proof. The packed form only saves disk:
`.olean` and `.ilean` hold one number per support instead of one expression
per witness.

The number is read from its low bits. A witness is a 2-bit tag (`0` cross and
`1` period direct witness, `2` wave, `3` perspective) followed by its fields.
A natural field is an 8-bit bit length `L` followed by `L` bits; an integer is
a zigzag-coded natural (`2z` for `z ≥ 0`, `−2z − 1` for `z < 0`); a dyadic
rational is an integer numerator followed by the exponent of its denominator;
an index is three integers. writes the numbers. -/

namespace BccSharp.Coulomb.CompactCover.LeafFix

def rdNat (P : ℕ) : ℕ × ℕ :=
  match P % 256, P / 256 with
  | L, Q => (Q % 2 ^ L, Q / 2 ^ L)

def unzig (z : ℕ) : ℤ := if z % 2 = 0 then ((z / 2 : ℕ) : ℤ) else -(((z + 1) / 2 : ℕ) : ℤ)

def rdInt (P : ℕ) : ℤ × ℕ :=
  match rdNat P with
  | (z, Q) => (unzig z, Q)

def rdQ (P : ℕ) : ℚ × ℕ :=
  match rdInt P with
  | (n, Q) => match rdNat Q with
    | (e, R) => ((n : ℚ) / ((2 ^ e : ℕ) : ℚ), R)

def rdVec (P : ℕ) : IntVec × ℕ :=
  match rdInt P with
  | (a, P) => match rdInt P with
    | (b, P) => match rdInt P with
      | (c, P) => (![a, b, c], P)

def rdWit (P : ℕ) : Wit × ℕ :=
  match P % 4, P / 4 with
  | 0, Q => match rdVec Q with
    | (i, Q) => match rdNat Q with
      | (A, Q) => match rdNat Q with
        | (N, Q) => (.direct ⟨true, i, A, N⟩, Q)
  | 1, Q => match rdVec Q with
    | (i, Q) => match rdNat Q with
      | (A, Q) => match rdNat Q with
        | (N, Q) => (.direct ⟨false, i, A, N⟩, Q)
  | 2, Q => match rdVec Q with
    | (i, Q) => match rdQ Q with
      | (a, Q) => match rdQ Q with
        | (b, Q) => match rdQ Q with
          | (x, Q) => match rdQ Q with
            | (t, Q) => (.wave ⟨i, a, b, x, t⟩, Q)
  | _, Q => match rdVec Q with
    | (i, Q) => match rdInt Q with
      | (U, Q) => (.persp ⟨i, U⟩, Q)

def decodeWits : ℕ → ℕ → List Wit
  | 0, _ => []
  | k + 1, P => match rdWit P with
    | (w, Q) => w :: decodeWits k Q

end BccSharp.Coulomb.CompactCover.LeafFix
