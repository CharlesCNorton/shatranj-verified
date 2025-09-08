(* ========================================================================= *)
(* SHATRANJ FORMALIZATION - COMPLETE SPECIFICATION WITH VALIDATION           *)
(* ========================================================================= *)

SECTION 1: FOUNDATIONS AND METATHEORY
- Imports: Program, Decidability, FunctionalExtensionality, Classical
- Custom tactics for automation
- Setoid infrastructure for board equality
- Global notation reservations
- Proof mode configuration
VALIDATION: Lemma example_decidable: forall (b: bool), {b = true} + {b = false}.

SECTION 2: FINITE DOMAIN THEORY
- Fin8: Fin.t 8 with complete enumeration theorem
- Finite type class with instances
- Decidable equality for all base types
- Exhaustive case analysis principles
- Bijection with bounded nat
VALIDATION: Lemma all_fin8_in_enumeration: forall (f: Fin.t 8), In f (enum_fin 8).

SECTION 3: POSITION ABSTRACTION
- Opaque Position module signature
- Rank/File as abstract types with Fin8 representation
- Position construction/destruction with proof obligations
- Position enumeration with NoDup proof
- Coordinate arithmetic with reversibility
- Algebraic notation: files a-h, ranks 1-8
VALIDATION: Example offset_roundtrip: forall p dr df p',
  offset p dr df = Some p' -> offset p' (-dr) (-df) = Some p.

SECTION 4: CORE GAME ONTOLOGY
- Color type: White | Black
- PieceType: Shah | Ferz | Alfil | Faras | Rukh | Baidaq
- Piece as record with color and type
- opposite_color function with involutive property
- Decidable equality for all types
- Exhaustiveness lemmas for case analysis
VALIDATION: Example opposite_color_involutive: forall c,
  opposite_color (opposite_color c) = c.

SECTION 5: BOARD ABSTRACTION
- Board as Position -> option Piece
- Board equality as extensional equality
- Update operations with commutativity
- Board predicates: occupied, occupied_by
- Initial position functions:
  * standard_initial: Shah on d1/d8, Ferz on e1/e8
  * alternative_initial: Shah on e1/e8, Ferz on d1/d8

HISTORICAL TABIYAT (Opening Arrays):
- tabiya_position: nat -> option Board
- 16 classical positions from al-Adli manuscripts
- tabiya_1: Muwashshah (Decorated) opening
- tabiya_2: Sayf (Sword) opening
- Agreement mechanism for tabiya start
- Theorem: all_tabiyat_wellformed

VALIDATION: Example board_update_retrieve: forall b p pc,
  board_get (board_set b p (Some pc)) p = Some pc.

SECTION 6: MOVEMENT GEOMETRY
- Movement types:
  * step_move: single square movement (Shah, Ferz)
  * leap_move: jumping movement (Alfil exactly 2 diagonal, Faras L-shape)
  * slide_move: straight line movement (Rukh)
- Path abstraction for sliding pieces
- Alfil leap specification: exactly 2 squares diagonally
- No path checking for leaping pieces
- Alfil color complex: only reaches 8 squares from any position
- Theorem: alfil_restricted_squares (1/8 of board reachable)
VALIDATION: Example alfil_color_bound: forall pos,
  card (reachable_squares_alfil pos) = 8.

SECTION 7: PIECE MOVEMENT RULES

SHAH (King):
- Spec: shah_move_spec: moves to any adjacent square (8 directions)
- Impl: shah_move_impl: one square orthogonally or diagonally
- No castling capability
- Cannot move into check

FERZ (Counselor):
- Spec: ferz_move_spec: moves exactly one square diagonally
- Impl: ferz_move_impl: diagonal step only (4 possible squares)

ALFIL (Elephant):
- Spec: alfil_move_spec: leaps exactly 2 squares diagonally
- Impl: alfil_move_impl: jumps over intervening pieces
- Cannot move 1 square or any other distance
- Color-bound: each Alfil restricted to 8 squares total

FARAS (Knight):
- Spec: faras_move_spec: L-shaped movement
- Impl: faras_move_impl: identical to modern chess knight
- Leaps over intervening pieces

RUKH (Rook):
- Spec: rukh_move_spec: slides along rank or file
- Impl: rukh_move_impl: any distance orthogonally
- Path must be clear

BAIDAQ (Pawn):
- Spec: baidaq_move_spec: 
  * Moves forward one square only
  * Captures one square diagonally forward
  * No initial two-square advance
  * No en passant
- Impl: baidaq_move_impl with promotion to Ferz only on 8th rank

VALIDATION: Example rukh_orthogonal: forall b c from to,
  rukh_move_impl b c from to = true ->
  (rankZ from = rankZ to) \/ (fileZ from = fileZ to).

SECTION 8: UNIFIED MOVEMENT
- can_move_piece dispatching by piece type
- No friendly capture allowed
- Capture removes opponent piece
- Movement preserves board validity
VALIDATION: Example no_friendly_fire: forall b pc from to,
  b[from] = Some pc ->
  can_move_piece b pc from to = true ->
  forall pc', b[to] = Some pc' -> piece_color pc' <> piece_color pc.

SECTION 9: ATTACK AND THREAT
- attacks: Board -> Position -> Position -> bool
- is_attacked: Board -> Position -> Color -> bool
- in_check: Board -> Color -> bool
- Shah cannot move into, remain in, or pass through check
VALIDATION: Example check_detection: forall b c shah_pos,
  b[shah_pos] = Some (mkPiece c Shah) ->
  in_check b c = true <-> is_attacked b shah_pos (opposite_color c) = true.

SECTION 10: GAME STATE
- GameState: board, turn, halfmove_clock, fullmove_number
- WellFormedBoard:
  * Exactly one Shah per color
  * Both Shahs present (never captured)
  * Valid piece counts (max 8 Baidaqs, etc.)
- No en_passant field needed
- No castling rights needed
- Optional: draw_offer_pending: bool
VALIDATION: Example initial_wellformed:
  WellFormedState initial_position = true.

SECTION 11: MOVE REPRESENTATION
- Move type:
  * Normal: Position -> Position -> Move
  * Promotion: Position -> Position -> Move (always to Ferz)
  * Resignation: Color -> Move
  * DrawOffer: Move
  * DrawAccept: Move
- No castling move constructor
- No en passant flag
VALIDATION: Example move_roundtrip: forall from to,
  move_from (Normal from to) = Some from /\
  move_to (Normal from to) = Some to.

SECTION 12: MOVE LEGALITY

MOVE VALIDATION ORDERING:
1. Check piece ownership (correct color)
2. Check basic movement pattern (piece-specific)
3. Check path clearance (sliding pieces only)
4. Check destination (empty or opponent piece)
5. Check no self-check results
6. Check special rules (mandatory promotion, bare king)

- legal_move_spec requirements:
  * Own piece at source
  * Movement follows piece rules
  * Destination empty or opponent piece
  * Shah never captured
  * No self-check after move
  * Baidaq reaching 8th rank must promote to Ferz
VALIDATION: Example legal_prevents_self_check: forall st m,
  legal_move_impl st m = true ->
  forall st', apply_move_impl st m = Some st' ->
  in_check (board st') (turn st) = false.

SECTION 13: MOVE APPLICATION
- apply_move updates:
  * Remove piece from source
  * Place piece at destination
  * Automatic Ferz promotion for Baidaq on 8th rank
  * Switch turn
  * Update move counters
  * Handle resignation/draw offers
- No castling logic
- No en passant logic
VALIDATION: Example apply_legal_succeeds: forall st m,
  WellFormedState st = true ->
  legal_move_impl st m = true ->
  exists st', apply_move_impl st m = Some st'.

SECTION 14: MOVE GENERATION
- Generate all pseudo-legal moves
- Filter for legality (no self-check)
- Include mandatory Ferz promotion
- No special case generation
VALIDATION: Example gen_captures_all_legal: forall st m,
  WellFormedState st = true ->
  legal_move_impl st m = true ->
  In m (generate_moves_impl st).

SECTION 15: GAME TREE PROPERTIES
- Reachability through legal moves
- Move sequences preserve well-formedness
- Finite game tree (positions eventually repeat)
VALIDATION: Example reachable_preserves_wf: forall st st',
  WellFormedState st = true ->
  reachable st st' ->
  WellFormedState st' = true.

SECTION 16: TERMINAL POSITIONS

CHECKMATE:
- Shah is in check
- No legal moves available
- Winner: attacking player
- is_checkmate: GameState -> bool

STALEMATE:
- Shah is NOT in check
- No legal moves available
- Winner: stalemating player (opposite of modern chess)
- is_stalemate: GameState -> bool

BARE KING:
- All pieces except Shah captured
- Winner: player who bared opponent
- Exception: immediate counter-bare results in draw
- Simultaneous bare (theoretical): draw
- bare_king_check: GameState -> option Color
- can_counter_bare: GameState -> bool

RESIGNATION:
- Player may resign at any time
- Immediate loss for resigning player
- handle_resignation: GameState -> Color -> GameResult

DRAW BY AGREEMENT:
- Both players may agree to draw
- Must be on player's turn to propose
- offer_draw: GameState -> GameState
- accept_draw: GameState -> option GameResult

DEAD POSITION:
- Neither player can achieve checkmate OR bare king
- Examples: 
  * Shah vs Shah
  * Shah vs Shah + Alfil (wrong color for checkmate)
  * Shah + Alfil vs Shah + Alfil (same color squares)
- is_dead_position: GameState -> bool

INSUFFICIENT MATERIAL:
- Both players have only Shah
- Result: draw
- is_insufficient_material: GameState -> bool

VALIDATION: Example stalemate_wins: forall st,
  is_stalemate_impl st = true ->
  game_winner st = Some (opposite_color (turn st)).

SECTION 17: HISTORICAL RULES

50-MOVE RULE:
- 50 moves without capture or Baidaq move
- Either player may claim draw
- fifty_move_counter: GameState -> nat
- claim_fifty_move: GameState -> option GameResult

THREEFOLD REPETITION:
- Same position 3 times
- Either player may claim draw
- position_history: list BoardConfiguration
- check_repetition: GameState -> bool
- claim_repetition: GameState -> option GameResult

ALTERNATIVE SETUP:
- Shah on e-file variant allowed
- Must be agreed before game
- Both colors must use same setup
- select_alternative_setup: bool -> GameState

TABIYA SELECTION:
- Players may agree to start from historical position
- select_tabiya: nat -> option GameState
- Theorem: tabiya_preserve_balance

VALIDATION: Example bare_king_wins: forall st c,
  bare_king_check st = Some c ->
  count_pieces (board st) c > 1 /\
  count_pieces (board st) (opposite_color c) = 1.

SECTION 18: VALIDATION FRAMEWORK
- Historical test positions from manuscripts
- Perft values for standard positions
- Problem positions (mansuba) verification
- Al-Adli's problems: 10 verified positions
- As-Suli's endgames: 8 verified positions
- Test harness for move generation
- Theorem: perft_deterministic
VALIDATION: Example perft_initial: 
  perft initial_position 4 = [historically_verified_value].

SECTION 19: GAME NOTATION

ALGEBRAIC NOTATION:
- Pieces: K=Shah, F=Ferz, A=Alfil, N=Faras, R=Rukh
- Pawns indicated by absence of letter
- Files a-h, ranks 1-8
- Special symbols:
  * "+" : Check
  * "#" : Checkmate
  * "BK" : Bare King victory

RESULT NOTATION:
- "1-0" : White wins
- "0-1" : Black wins
- "½-½" : Draw
- Game termination reasons in PGN tags

FEN ADAPTATION:
- Piece mapping for Shatranj pieces
- No castling rights field
- No en passant field
- fen_to_state: string -> option GameState
- state_to_fen: GameState -> string

MOVE NOTATION:
- move_to_algebraic: GameState -> Move -> string
- parse_algebraic: string -> GameState -> option Move
- Theorem: parse_move_inverse

VALIDATION: Example fen_roundtrip: forall st,
  WellFormedState st = true ->
  state_of_fen (fen_of_state st) = Some st.

SECTION 20: POSITION EVALUATION
- Material values (historical):
  * Rukh: 5
  * Faras: 3
  * Alfil: 2
  * Ferz: 2
  * Baidaq: 1
- Positional factors:
  * Shah safety
  * Piece mobility
  * Baidaq advancement
- evaluate_position: GameState -> Color -> Z
- Theorem: evaluation_bounded
VALIDATION: Example material_bounds: forall b c,
  0 <= material_value b c <= 31. (* 2R + 2N + 2A + 1F + 8P *)

SECTION 21: METATHEOREMS
- Game termination: finite due to repetition/50-move
- Stalemate as victory preserves game termination
- Bare king with counter-bare produces well-defined outcome
- All pieces reachable from initial position
- Alfil color-binding creates independent subsystems
- Dead position detection is decidable
- Theorem: no_infinite_games
- Theorem: wellformed_invariant
- Theorem: move_generation_complete
VALIDATION: Example finite_game_length: forall st,
  WellFormedState st = true ->
  exists n, n <= 5000 /\ (* 50-move rule ensures termination *)
  forall path, game_path st path -> length path <= n.

IMPLEMENTATION REQUIREMENTS:

1. Every function has bilateral spec/impl with completeness proof
2. Partial functions specify Some/None conditions precisely
3. All invariants have preservation proofs
4. Enumerations have NoDup and completeness
5. No modern chess features (castling, en passant, promotion choice)
6. Stalemate victory correctly implemented
7. Bare king rules with counter-bare exception
8. Historical accuracy in piece movements
