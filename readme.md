# Shatranj in Coq

Machine-checked formalization of Shatranj (medieval chess) following derived Laws of Shatranj.

## Scope

Complete game rules with bilateral specification/implementation proofs:
- Piece movements (Shah, Ferz, Alfil, Faras, Rukh, Baidaq)
- Stalemate as victory, bare king victory with counter-bare exception  
- No castling, no en passant, Ferz-only promotion

## Architecture

21 sections from finite domain theory through metatheorems. Every computational function paired with propositional specification and completeness proof. Each section validated with executable example.
