
(****************************************************************************** 
 *                FORMALIZING COMBINATORIAL GAME THEORY IN COQ                * 
 *                                       (by Jacqueline Casey)                * 
 ******************************************************************************)

(* The goal of this project is twofold:
 * - First, I formalize (some) of the fundamentals of combinatorial game theory.
 * - Second, I will use this work to solve an actual game, to demonstrate the 
 *   usefulness of the tools developed in the first part.
 *
 * Of course, we can only go so far in the first part, the goal I set was to prove
 * enough there in order to comfortably carry out the analysis in the second part.
 * For the second part, I have chosen to analyze the game Nim. On the surface, Nim
 * seems like a fairly simple game, but the analysis of Nim winds up being important
 * in the analysis of a whole class of combinatorial games (the impartial games, 
 * where each position affords the same moves to each player). Also, for reasons 
 * that will become clear below, Nim is a pretty fun game to analyze because it 
 * it is *fuzzy*. We will see at some point that all games have a value, and that
 * value can be positive, negative, zero, or fuzzy. The fact that we have a
 * fourth category and not just three is part of what makes Combinatorial Game
 * Theory so interesting to me, so I could not resist choosing a game (Nim) where
 * fuzzy states are abundant. 
 *
 * In order to prove Nim, I needed to define and prove a notion of game equivalence,
 * as well as its basic properties. In short, the first part builds up topics up
 * until game equivalence, and the second part analyzes Nim until we can show a 
 * procedure to decide which player wins a given Nim position. 
 *
 * While writing this project, I referred to a book: "Winning Ways for Your Mathematical Plays"
 * by Elwyn Berlekamp, John Conway, and Richard Guy. This book is a fun read, and
 * I was introduced to this field by someone recommending it to me. So I've read
 * it in the past, but I'll note that I did not follow it very closely while writing
 * the project. I opened it a few times to get my bearing when I was particularly
 * confused. Also, the book operates at a high level of abstraction - Many of the
 * results I show below are not proved, or even formally stated, in the book. This
 * is part of why I though the book would be a good target for formalization. 
 *
 * The topics in this project are a subset of topics covered in the first 3 chapters 
 * of Winning Ways. This includes the analysis of Nim. *)



(* I've broken up the project into 6 sections.
 *
 * SECTION 0: Prelude
 * SECTION 1: Definitions
 * SECTION 2: Game Addition 
 * SECTION 3: Value Classes and Negation
 * SECTION 4: Equivalence
 * SECTION 5: Nim 
 *
 * Over time, it became clear that Nim was easy in comparison to showing all the
 * theorems of general game theory needed to handle Nim. Hence, there are 4 general 
 * game theory sections and 1 Nim section. The lack of balance here is fine by me. *)



(* SECTION 0: Prelude
 * ------------------
 * 
 * This is mostly setup, but we also prove some very general lemmas that don't
 * fit anywhere else and don't really concern game theory. *)

(* These are our standard imports. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
Set Default Goal Selector "!".

(* We also use Classical, primarily for convenience, though I suspect in places
 * it is necessary. *)

From Coq Require Import Classical.

(* These lemmas are taken from LF's Logic.v. Some were exercises, some were given
 * in the text. *)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) <-> (~Q -> ~P).
Proof.
  split; intros.
  - specialize classic with P. intuition.
  - specialize classic with Q. intuition.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H.  
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - intros H. induction l as [| x' l' IH].
    + simpl in H. contradiction. 
    + simpl in H. destruct H as [Hfxy | Hl'].
      * exists x'. split.
        -- apply Hfxy.
        -- simpl. left. reflexivity.
      * apply IH in Hl' as [x'' [Hfxy Hfl']]. exists x''. split.
        -- apply Hfxy.
        -- simpl. right. apply Hfl'.
  - intros [x [Hfxy Hl]]. induction l as [|x' l' IH].
    + apply Hl.
    + simpl. simpl in Hl. destruct Hl.
      * left. rewrite H. apply Hfxy.
      * right. apply (IH H).
Qed.  

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - intros l' a. split.
    + simpl. intro H. right. apply H.
    + simpl. intros [[] | H]. apply H.
  - intros l'' a. simpl. rewrite IH. intuition.
Qed.

(* Finally, we use the Equations library, which is NOT in Coq's standard library.
 * You will need to install it. We use equations to generate useful induction 
 * principles for a certain tricky type below. *)

(* See the installation instructions for this library here:
 * https://github.com/mattam82/Coq-Equations#installation *)

From Equations Require Import Equations.

(* Now, without further ado... *)



(* SECTION 1: Definitions
 * ----------------------
 *
 * In this section, we define what a combinatorial game is, and we define the related
 * concepts like the two players and what it means to win a game. We investigate
 * the basic properties of these objects, proving some results we will use many times
 * later on. *)

(* First, an informal description of a combinatorial game:
 * 
 * A combinatorial game is a 2 player game where the 2 players (called Left and Right) 
 * take turns, alternating. All combinatorial games must terminate at some point, 
 * and they always end with a victory for one of the 2 players. We follow the 
 * "Normal Play Convention" where the first player that cannot make a move is declared
 * the loser. 
 *
 * Interestingly, we don't fix which of Left and Right is the start player. Games
 * are not thought of as having a curent player - any game has moves that Left can
 * make (if they are moving) and moves that Right can make (if they are moving). We
 * will see that this is actually important when we discuss combinations of games.
 * 
 * It is possible to generalize this definition to include more games, but this is
 * the definition we are working with today. Our games are all perfect imformation,
 * deterministic, and finite depth. Winning Ways actually allows infinite depth (which
 * is very hard to model in Coq), so long as the game is gauranteed to end when actually
 * played. We make the simplifying assumption that all games actually have finite depth,
 * so no branch of moves even by the same player can be infinite. *)

(* Now, we formalize. *)

(* The players of the game are called Left and Right. We will of course shorten
 * this to L and R. *)

Inductive player :=
  | L 
  | R.

(* When we are discussing a player in the abstract, it is useful to have a notion 
 * of their opponent. *)

Definition opponent (p : player) := 
  match p with
  | L => R
  | R => L
  end.

Notation "! p" := (opponent p) (at level 60).

(* This operation is obviously involutive. *)

Lemma double_opponent:
  forall p, !(!p) = p.
Proof. 
  intros. destruct p; reflexivity. 
Qed.

(* Now we have to define a game, and this is somewhat tricky. We will take the tree
 * view of the game, viewing the game as the tree of all possible sequences of moves
 * that can be made. From each position, left can play some moves, and right can
 * play other moves. Each move yields a new game, so we model a game as two lists
 * of games. The order of the games within these lists is irrelevant, but we use
 * lists because they are familiar and easy to work with inductively. 
 *
 * [ls] is the list of moves that Left can make, and [rs] is the list of moves that
 * Right can make. *)

Inductive game :=
  | moves (ls : list game) (rs : list game).
  
Notation "{ l | r }" := (moves l r).

(* This notation is sometimes a little clunky, but I am not much of a notation wizard.
 * It resembles the notation used in Winning Ways, but there the square brackets for
 * the lists are omitted, as they are obviously superfluous.
 * 
 * I will note that this notation is used simultaneously to refer to games and their
 * values (a concept which we will investigate later). Games are actually closely 
 * related to a very general (and strange) numerical system that uses precisely 
 * this notation: the surreal numbers. More on those later. *)

(* We provide some examples, though some of these will come back again and again. *)

(* The 0 game is an immediate loss for whoever plays. *)

Example zero_game : game := { [] | [] }.

Notation "00" := zero_game.  (* I use 00 here to avoid clashing with the natural number 0. *)

(* The game with value 1 lets left move to zero, and doesn't let right move at all. *)

Example one_game : game := {[00] | []}.

(* The game with value -1 is the mirror image. *)

Example negative_one_game : game := {[] | [00]}.

(* We won't give these games notation yet. *)

(* We don't prove this yet, but it is important to know: positive games are wins
 * for L, and negative games are wins for R. A Mnemonic: in some since, we are 
 * rooting for L, since we assign their wins a positive value. Another Menmonic: 
 * In some sense, the vertical bar [|] between the lists of numbers is kinda 
 * expressing where the number itself is. In the one_game [{[0] | []}], the bar
 * is somewhere to the right of 0, therefore 1. It turns out the number is in the
 * "simplest possible" place subject to these constraints, but the precise meaning
 * of this statement is not covered here. *)

(* Not all games have values that we recognize. Here we show a game value that is 
 * very important in the analysis of Nim, a game with value *. Either player can
 * move * to 0. Thus, whichever player starts wins, so in some since * is the
 * opposite of 0. However, star is not unique in this regard. *)

Example star_game : game := { [00] | [00] }.

Notation "*" := star_game. 

(* We define what it means for a given player to make a certain move. Left can play
 * a game G = { ls | rs } to any game in ls, and Right can play to any game in rs. *)

Definition left_can_play (g : game) (g' : game) : Prop := 
  match g with
  | moves ls rs => In g' ls
  end.

Definition right_can_play (g : game) (g' : game) : Prop := 
  match g with
  | moves ls rs => In g' rs
  end.

(* We bundle theses together so we can work with an abstract player. *)

Definition can_play (p : player) (g : game) (g' : game) : Prop :=
  match p with
  | L => left_can_play g g'
  | R => right_can_play g g'
  end.

Notation "p @ g => g'" := (can_play p g g') (at level 60).

(* I like to read this as "p can send g to g'". Here is what it looks like in vivo. *)

Check ( L @ * => 00 ).
Check ( R @ 00 => * ).

(* And an example proof : any player can play [00] from [*]. *)

Example star_yields_0 : forall p, p @ * => 00.
Proof. 
  destruct p; simpl; intuition. 
Qed.

(* 00 is an imporant game for us. We will prove the first of many facts about 00,
 * that 00 is the only game where no one can move. *)

Theorem no_plays_zero_game : forall g,
  (forall p g', ~(p @ g => g')) <-> g = 00.
Proof.
  split; intros.
  - destruct g. destruct ls.
    + destruct rs; trivial.
      exfalso. apply H with (R) (g). simpl. left. reflexivity.
    + exfalso. apply H with (L) (g). simpl. left. reflexivity.
  - subst. intros C. destruct p; destruct C.
Qed.

(* Games are naturally inductive / recursive, so we would like to be able to do
 * induction on them. Let's take a look at the induction principles Coq generates. *)

Check game_ind.

(* game_ind
  : forall P : game -> Prop,
      (forall ls rs : list game, P {ls | rs}) -> forall g : game, P g *)
      
(* Unfortunately, this is useless. *)

(* Games are basically slightly more complex Rose trees, and there are resources online that
* describe how to use the [equations] package to generate inductive principles 
* for Rose trees. I found this discussion here to be particularly useful: 
* https://coq.discourse.group/t/proving-properties-for-inductives-with-nested-inductives/174/6. 
*
* All code in the following section basically comes from that discussion, though
* I have adapted it slightly to work for games instead of Rose trees. *)

Section Game_Induction.

Variable P : game -> Prop.
Variable P_list : list game -> Prop.
Hypothesis P_nil : P_list [].
Hypothesis P_cons : forall t l, P t -> P_list l -> P_list (t :: l).
Hypothesis P_moves : forall l1 l2, P_list l1 -> P_list l2 -> P {l1 | l2}.

Equations raw_game_induction (t : game) : P t := {
  raw_game_induction (moves l1 l2) := P_moves l1 l2 (raw_game_induction_list l1) (raw_game_induction_list l2) 
}
where raw_game_induction_list (l : list (game)) : P_list l := { raw_game_induction_list [] := P_nil;
  raw_game_induction_list (tn :: l') := P_cons tn l' (raw_game_induction tn) (raw_game_induction_list l') 
}.

End Game_Induction. (* Also end of the code I am citing. *)

Check raw_game_induction.

(* Our result is a kinda clunky (hence, "raw"), though working, induction principle. 
 *  raw_game_induction
 *  : forall (P : game -> Prop) (P_list : list game -> Prop),
 *      P_list [] ->
 *      (forall (t : game) (l : list game), P t -> P_list l -> P_list (t :: l)) ->
 *       (forall l1 l2 : list game, P_list l1 -> P_list l2 -> P {l1 | l2}) -> 
 *      forall t : game, P t 
 *)

(* We refine induction a bit to make it nicer to use. *)

Theorem game_induction_half_refined (P : game -> Prop) : 
  (forall ls rs : list game, (forall g, In g ls -> P g) -> (forall g, In g rs -> P g) -> 
  P {ls | rs}) -> forall t : game, P t.
Proof.
  intros.
  specialize raw_game_induction with
    (P := P)
    (P_list := fun l => forall g, In g l -> P g)
  as H0. apply H0; clear H0.
  - contradiction.
  - intros. destruct H2; subst; auto.
  - intros. apply H.
    + apply H0.
    + apply H1.
Qed.

(* But the best version is as follows. *)
 
Theorem game_induction (P : game -> Prop) 
  (IH : forall g, (forall g' p, p @ g => g' -> P g') -> P g) :
  forall g, P g.
Proof.
  intros. apply game_induction_half_refined. intros.
  apply IH; intros.
  destruct p; auto.
Qed.

(* Strictly speaking, there are fewer things that you can prove with [game_induction] 
 * than with [raw_game_induction], but none of the proofs below need the raw version. *)

(* We move on to another property of games, which is depth. Sometimes, where game
 * induction fails us, we can do induction on a game's depth as a proxy. To make 
 * this work though, we would like to show that all games have a depth. *)

Inductive depth : game -> nat -> Prop := 
  | Decreasing (ls rs : list game) (n : nat) 
      (H : forall g', (In g' ls \/ In g' rs) -> exists k, k < n /\ depth g' k)
    : depth {ls|rs} n.

(* We've chosen a flexible definition - all subgames must have lower depth, but we
 * do not require that the depth of the game is the smallest such number where this
 * holds. For example, 00 has depth 0, but it also has depth 42. *)

Example ex_depth_00 : depth 00 0.
Proof. 
  constructor; intros. destruct H; contradiction. 
Qed.

Example ex_depth_overkill : depth 00 42.
Proof. 
  constructor; intros. destruct H; contradiction. 
Qed.

(* Indeed, 00 is the only depth 0 game. *)

Theorem depth_0_00 : forall g, 
  depth g 0 <-> g = 00.
Proof.
  split; intros.
  - inversion H; subst. apply no_plays_zero_game. intros. intros C.
    destruct p.
    + eapply or_introl in C. apply H0 in C. destruct C. lia.
    + eapply or_intror in C. apply H0 in C. destruct C. lia.
  - subst. apply ex_depth_00.
Qed.

(* It is helpful to be able to relax a game's depth during some proofs. *)

Theorem relax_depth: forall g k n,
  k <= n -> depth g k -> depth g n.
Proof.
  intros. destruct g. inversion H0; subst. 
  constructor; intros g' [H1 | H1].
  - eapply or_introl in H1. eapply H4 in H1 as [k' [Hk' HDepth]].
    exists k'. split; try lia. auto.
  - eapply or_intror in H1. eapply H4 in H1 as [k' [Hk' HDepth]].
    exists k'. split; try lia. auto.
Qed.

(* We now show that all games have a depth. First we show that all lists of games
 * have a maximum depth. *)

Lemma list_max_depth_exists : forall l, 
  (forall g, In g l -> exists k, depth g k) ->
  (exists n, forall g, In g l -> depth g n).
Proof.
  intros l. induction l.
  - intros. exists 42. intros. contradiction.
  - intros. assert (forall g : game, In g l -> exists k : nat, depth g k). {
      intros. apply H. right. auto.
    }
    apply IHl in H0 as [n H0].
    specialize H with a. assert (exists k : nat, depth a k). {
      apply H. left. reflexivity.
    }
    destruct H1 as [k H1].
    exists (S (k + n)).
    intros. destruct H2; subst.
    + eapply relax_depth; try apply H1. lia.
    + apply H0 in H2. eapply relax_depth; try apply H2. lia.  
Qed.

(* And now for the main proof. *)

Theorem depth_exists : forall g, exists n,
  depth g n.
Proof.
  apply game_induction.
  intros [ls rs] IH.
  specialize list_max_depth_exists with ls as [n1 Hn1].
  { intros g' H. apply IH with L. auto. }
  specialize list_max_depth_exists with rs as [n2 Hn2].
  { intros g' H. apply IH with R. auto. }
  exists (S (n1 + n2)). constructor. intros g' [H | H].
  - apply Hn1 in H. exists n1. split; try lia. auto.
  - apply Hn2 in H. exists n2. split; try lia. auto.
Qed.

(* Games have winners, and we are interested in figuring out those winners. However, 
 * it is not true that each game is either a win for L or a win for R, indeed 
 * we have seen that both [*] and [0] are exceptions. Instead, we define properties 
 * that say a given player wins if they play first or wins if they play second. *)

(* It turns that that "p wins g when p starts" and "p wins g when !p starts" are
 * inherently interrelated concepts. We therefore define them at once, as a coinductive 
 * structure. *)

Inductive wins_first : player -> game -> Prop :=
  | wins_one (p : player) (g g' : game) 
      : (p @ g => g') -> (wins_second p g') -> wins_first p g
with wins_second : player -> game -> Prop :=
  | wins_all (p : player) (g : game) 
      : (forall g', ((!p) @ g => g') -> wins_first p g') -> wins_second p g.

(* A player [wins_first] if they have at least 1 move to a game where they [wins_second].
 * A player [wins_second] if they [wins_first] after any move their opponent makes. 
 *
 * Games are secretly all about these chains of alternating quantifiers: 
 * "forall, there exists, forall, there exists ...". I saw games discussed briefly
 * in complexity theory this quarter, since these alternating quantifiers show up
 * in the quintessential PSPACE complete problem, TQBF (Totally Quantified Boolean Formula). *)

(* Here are some example proofs, that justify my statements earlier about [*] and 
 * [00]. *)

Example all_win_zero_second : forall p, wins_second p 00.
Proof. 
  destruct p; apply wins_all; intros.
  - contradiction. (* Zero cannot yield another game. *)
  - contradiction.
Qed.

Example all_win_star_first : forall p, wins_first p *.
Proof.
  destruct p; apply wins_one with (00);
    try (simpl; intuition); (* Show that p can send * to 0. *)
    try apply all_win_zero_second. (* Show that !p loses 0 (i.e. p `wins_second` zero). *)
Qed.

(* It is obvious that if a player wins first, then their opponent loses second. *)

Theorem A_wins_first_B_loses_second: forall g p,
  wins_first p g -> ~wins_second (!p) g.
Proof.
  specialize game_induction with 
    (* Unfortunately, we still have to tell game_induction exactly what to do. *)
    (P := fun h => forall p, wins_first p h -> ~ wins_second (!p) h)
  as H. apply H; clear H; intros.
  intros Contra. 
  inversion H0; subst. inversion Contra; subst.
  specialize H3 with g'. rewrite double_opponent in H3.
  apply H3 in H1 as H5.
  assert (HDone : ~ wins_second (p) g'). {
    specialize H with g' (p) (!p). rewrite double_opponent in H.
    eauto.
  }
  intuition.
Qed.

(* We would also like to show the converse: 
 * [forall g p, wins_first p g -> ~wins_second (!p) g]
 * But this is possibly a bit harder. *)

(* We first need a lemma, which says that if [p] loses playing second, then there 
 * is a killer move that [!p] plays to a game where [p] loses first. *)

Lemma losing_second_killer_move: forall g p,
  (exists g', (!p) @ g => g' /\ ~wins_first (p) g') <-> ~wins_second p g.
Proof.
  split.
  - intros. destruct H as [g' [H1 H2]]. intros C. inversion C; subst; clear C.
    specialize H with g'. intuition.
  - intros. destruct g. apply not_all_not_ex.
    intros C. apply H. constructor. intros g' H1. specialize C with g'.
    simpl in H1. apply not_and_or in C. destruct C; try contradiction.
    apply NNPP. apply H0.
Qed.

(* Now for the converse. *)

Theorem B_loses_second_A_wins_first: forall g p,
  ~wins_second (!p) g -> wins_first p g.
Proof.
  specialize game_induction with 
    (P := fun g => forall (p : player), ~ wins_second (! p) g -> wins_first p g)
  as H.
  apply H; clear H; intros.
  rewrite <- losing_second_killer_move in H0. destruct H0 as [g' [H2 H3]].
  rewrite double_opponent in H2.
  econstructor; eauto. 
  specialize classic with (wins_second p g'); try intuition.
  exfalso. apply H3. eapply H; eauto. rewrite double_opponent. auto.
Qed.

(* It makes sense to bundle these as one result with a (slightly) more intuitive name. *)

Theorem win_first_opponent_lose_second : forall g p,
  wins_first p g <-> ~wins_second (!p) g.
Proof.
  split.
  - apply A_wins_first_B_loses_second.
  - apply B_loses_second_A_wins_first.
Qed.

(* And some closely related versions may also be nice to have. *)

Theorem lose_first_opponent_win_second : forall g p,
  ~wins_first p g <-> wins_second (!p) g.
  split.
  - apply contrapositive. intros. apply double_neg. 
    rewrite win_first_opponent_lose_second. easy.
  - apply contrapositive. intros. apply NNPP in H.
    rewrite <- win_first_opponent_lose_second. easy.
Qed.

Theorem win_second_opponent_loses_first : forall g p,
  wins_second p g <-> ~wins_first (!p) g.
Proof.
  split; intros.
  - apply lose_first_opponent_win_second. rewrite double_opponent. assumption.
  - apply lose_first_opponent_win_second in H. rewrite double_opponent in H. assumption.
Qed.

Theorem lose_second_opponent_win_first : forall g p,
  ~wins_second p g <-> wins_first (!p) g.
Proof.
  split.
  - apply contrapositive. intros. apply double_neg.
    rewrite win_second_opponent_loses_first. easy.
  - apply contrapositive. intros. apply NNPP.
    rewrite <- win_second_opponent_loses_first. easy.
Qed.



(* SECTION 2: Game Addition 
 * ------------------------
 *
 * In this section, we investigate the concept of game addition, where two games 
 * are combined to make a new compound game. This eventually allows us to analyze 
 * and compare values in games by combining them and seeing the result. *)

(* First, we define game combination (which is our addition). If you have two games,
 * then you can create a single new game which is the combination of the two. On
 * Left's turn, they choose one of the component games to move in. On Right's turn,
 * they choose a (possibly different) component game to move in. This is why we
 * said that games are defined to have moves for both players at all positions - even
 * though in a single game play alternates, play in a subgame need not alternate. *)

(* If a player can play G to G', then they can play G + H to G' plus H, and the same 
 * holds for H. We define combination so that these are exactly the moves allowed. 
 * We don't actually say anything about the order of the underlying lists, so technically,
 * this relation is not a function (even though it often feels like one, since games 
 * that only have the choices permuted always play identically). *)

Inductive combination (g1 g2 g : game) : Prop :=
  | combines 
    (H1 : forall (p : player) (g' : game), 
      (p @ g => g' -> exists gi', 
        (p @ g1 => gi' /\ combination gi' g2 g') \/ (p @ g2 => gi' /\ combination g1 gi' g')))
    (H2 : forall (p : player) (g1' : game),
      p @ g1 => g1' -> exists g', (p @ g => g') /\ combination g1' g2 g')
    (H3 : forall (p : player) (g2' : game),
      p @ g2 => g2' -> exists g', (p @ g => g') /\ combination g1 g2' g'). 


(* We continue the pattern of duplicating symbols to avoid annoying clashes with 
 * existing symbols. *)
Notation "g1 ++ g2 == g3" := (combination g1 g2 g3) (at level 60).

(* A quick, though perhaps not very interesting, example. *)

Example zero_game_plus_zero_game : 00 ++ 00 == 00.
Proof.
  constructor; intros; destruct p; inversion H.
Qed. 

(* We will prove some of the properties that we expect addition to have. For instance
 * combination is commutative. *)

Lemma combination_comm : forall g g1 g2,
  g1 ++ g2 == g -> g2 ++ g1 == g.
Proof.
  specialize game_induction with 
    (P := fun g => forall g1 g2, g1 ++ g2 == g -> g2 ++ g1 == g)
  as H. apply H; clear H; intros;
  try contradiction; try (destruct H0; subst; auto).
  constructor; intros.
  - specialize H1 with (p) (g'). remember H0 as Hmove. clear HeqHmove.
    apply H1 in H0. destruct H0 as [gi' H4].
    exists gi'. rewrite or_comm. 
    destruct H4 as [H4 | H4].
    + left. split. { intuition. } eapply H; eauto. intuition.
    + right. split. { intuition. } eapply H; eauto. intuition.
  - specialize H3 with (p) (g1'). remember H0 as Hmove. clear HeqHmove.
    apply H3 in H0. destruct H0 as [g' H4]. exists g'.
    split; destruct H4; eauto.
  - specialize H2 with (p) (g2'). remember H0 as Hmove. clear HeqHmove.
    apply H2 in H0. destruct H0 as [g' H4]. exists g'.
    split; destruct H4; eauto.
Qed.

(* The 0 game is neutral. *)

Theorem zero_game_neutral_left : forall g : game,
  00 ++ g == g.
Proof.
  specialize game_induction with 
    (P := fun g => 00 ++ g == g)
  as H. apply H; clear H. intros.
  constructor; intros.
  - exists g'. right. split; auto. eapply H. eauto.
  - destruct p; inversion H0.
  - exists g2'. split; auto. eapply H; eauto.
Qed.

Theorem zero_game_neutral_right : forall g : game,
  g ++ 00 == g.
Proof.
  intros.
  apply combination_comm.
  apply zero_game_neutral_left.
Qed.

(* We will drop these in auto's database. *)

Hint Resolve zero_game_neutral_left zero_game_neutral_right : core.

(* These tools make a more involved example feasible. *)

Example one_plus_neg_one : {[00]|[]} ++ {[]|[00]} == { [{ [] | [00] }] | [{ [00] | [] }] }.
  constructor; intros.
  - destruct p; simpl in *; destruct H as [H | []]; exists 00. 
    + left. split; subst; auto.
    + right. split; subst; auto.
  - destruct p; inversion H; subst; try contradiction.
    exists {[] | [00]}.
    split; simpl; auto.  
  - destruct p; inversion H; subst; try contradiction.
    exists {[00] | []}.
    split; simpl; auto.  
Qed.

(* We would now like to show that for any two games, a combination game exists. This
 * is a remarkably long proof, since we seemingly cannot get away with normal game
 * induction. Instead, we use the idea of depth we saw before. *)

(* It is clear the combination of two games has depth at most the sum of depths 
 * of the two games. *)

Theorem combination_depth : forall g g1 g2 n1 n2,
  g1 ++ g2 == g -> depth g1 n1 -> depth g2 n2 -> depth g (n1 + n2).
Proof.
  specialize game_induction with
    (P := fun g => forall g1 g2 n1 n2, g1 ++ g2 == g -> 
      depth g1 n1 -> depth g2 n2 -> depth g (n1 + n2))
  as H. apply H; clear H.
  intros g IH g1 g2 n1 n2 HComb HDepth1 HDepth2. destruct g.
  constructor. intros g' Hg'. destruct Hg' as [Hg' | Hg'].
  - inversion HComb. eapply H1 with L _ in Hg' as H4. clear H1 H2 H3. destruct H4 as [gi' [[H4 H5]|[H4 H5]]].
    + destruct n1.
      * inversion HDepth1; subst. eapply or_introl in H4. eapply H in H4 as [k [Hk Hdk]]. lia.
      * exists (n1 + n2). split; try lia.
        eapply IH with L _ _.
        -- trivial.
        -- eapply H5. 
        -- inversion HDepth1; subst. eapply or_introl in H4. apply H in H4 as [k' [Hk' HDepth']].
          apply relax_depth with k'; try lia; auto.
        -- auto.
    + destruct n2.
      * inversion HDepth2; subst. eapply or_introl in H4. eapply H in H4 as [k [Hk Hdk]]. lia.
      * exists (n1 + n2). split; try lia.
        eapply IH with L _ _.
        -- trivial.
        -- apply H5.
        -- auto. 
        -- inversion HDepth2; subst. eapply or_introl in H4. apply H in H4 as [k' [Hk' HDepth']].
          apply relax_depth with k'; try lia; auto.
  - inversion HComb. eapply H1 with R _ in Hg' as H4. clear H1 H2 H3. destruct H4 as [gi' [[H4 H5]|[H4 H5]]].
    + destruct n1.
      * inversion HDepth1; subst. eapply or_intror in H4. eapply H in H4 as [k [Hk Hdk]]. lia.
      * exists (n1 + n2). split; try lia.
        eapply IH with R _ _.
        -- trivial. 
        -- apply H5. 
        -- inversion HDepth1; subst. eapply or_intror in H4. apply H in H4 as [k' [Hk' HDepth']].
          apply relax_depth with k'; try lia; auto.
        -- auto.
    + destruct n2.
      *  inversion HDepth2; subst. eapply or_intror in H4. eapply H in H4 as [k [Hk Hdk]]. lia.
      *  exists (n1 + n2). split; try lia.
        eapply IH with R _ _.
        -- trivial. 
        -- apply H5.
        -- auto. 
        -- inversion HDepth2; subst. eapply or_intror in H4. apply H in H4 as [k' [Hk' HDepth']].
          apply relax_depth with k'; try lia; auto.
Qed.

(* Now some lemmas that help us during the induction later. *)

Lemma depth_list_helper_l : forall a ls rs n,
  depth {a :: ls | rs} n -> depth {ls | rs} n /\ depth a (pred n).
Proof.
  intros. destruct n.
  - apply depth_0_00 in H. discriminate H.
  - split.
    + constructor; intros.
      assert (In g' (a :: ls) \/ In g' rs). {
        destruct H0.
        - left. right. auto.
        - right. auto.
      }
      inversion H; subst. apply H5 in H1 as [k H1]. eauto.
    + inversion H; subst. specialize H3 with a.
      assert (exists k : nat, k < S n /\ depth a k). {
        apply H3. left; left; auto.
      }
      destruct H0 as [k H0].
      eapply relax_depth with k; try lia. intuition.
Qed.

Lemma depth_list_helper_r : forall a ls rs n,
  depth {ls | a :: rs} n -> depth {ls | rs} n /\ depth a (pred n).
Proof.
intros. destruct n.
- apply depth_0_00 in H. discriminate H.
- split.
  + constructor; intros.
    assert (In g' ls \/ In g' (a :: rs)). {
      destruct H0.
      - left. auto.
      - right. right. auto.
    }
    inversion H; subst. apply H5 in H1 as [k H1]. eauto.
  + inversion H; subst. specialize H3 with a.
    assert (exists k : nat, k < S n /\ depth a k). {
      apply H3. right; left; auto.
    }
    destruct H0 as [k H0].
    eapply relax_depth with k; try lia. intuition.
Qed.

(* One more helper lemma. This one is really quite long. *)

Lemma combination_exists_helper : forall n g1 g2, 
  (exists n1 n2, depth g1 n1 /\ depth g2 n2 /\ n1 + n2 <= n) -> exists g, g1 ++ g2 == g.
Proof.
  intros n. induction n.
  - intros g1 g2 [n1 [n2 [H1 [H2 H3]]]].
    assert (n1 = 0) by lia. assert (n2 = 0) by lia. subst. 
    apply depth_0_00 in H1.
    apply depth_0_00 in H2.
    subst.
    exists 00.
    apply zero_game_neutral_left.
  - intros g1 g2 [n1 [n2 [H1 [H2 H3]]]].
    destruct g1 as [ls1 rs1].
    destruct g2 as [ls2 rs2].

    destruct n1. {
      rewrite depth_0_00 in H1. exists {ls2 | rs2}. rewrite H1. apply zero_game_neutral_left. 
    }
    destruct n2. {
      rewrite depth_0_00 in H2. exists {ls1 | rs1}. rewrite H2. apply zero_game_neutral_right. 
    }

    assert (exists ls1', (forall g', In g' ls1' -> exists g, In g ls1 /\ g ++ {ls2 | rs2} == g') /\ (forall g, In g ls1 -> exists g', In g' ls1' /\ g ++ {ls2 | rs2} == g')). {
      induction ls1.
      - exists []. split; intros [g Hg] HIn; contradiction.
      - apply depth_list_helper_l in H1 as [HDepth1 HDepth2].
        specialize IHn with a {ls2 | rs2}. assert (exists g : game, a ++ {ls2 | rs2} == g). {
          apply IHn. exists (n1). exists (S n2). split; auto. split; auto. lia.  
        }
        destruct H as [a' H].
        apply IHls1 in HDepth1 as [ls1' [H4 H5]].
        exists (a' :: ls1'). split; intros.
        + destruct H0.
          * subst. exists a. split; auto. left. auto.
          * apply H4 in H0 as [g'' [H0 H1]]. exists g''. split; auto. right. auto.
        + destruct H0.
          * subst. exists a'. split; auto. left. auto.
          * apply H5 in H0 as [g'' [H0 H1]]. exists g''. split; auto. right. auto.
    }

    assert (exists ls2', (forall g', In g' ls2' -> exists g, In g ls2 /\ {ls1 | rs1} ++ g == g') /\ (forall g, In g ls2 -> exists g', In g' ls2' /\ {ls1 | rs1} ++ g == g')). {
      clear H. induction ls2.
      - exists []. split; intros [g Hg] HIn; contradiction.
      - apply depth_list_helper_l in H2 as [HDepth1 HDepth2].
        specialize IHn with {ls1 | rs1} a. assert (exists g : game, {ls1 | rs1} ++ a == g). {
          apply IHn. exists (S n1). exists n2. split; auto. split; auto. lia.  
        }
        destruct H as [a' H0].
        apply IHls2 in HDepth1 as [ls2' [H4 H5]].
        exists (a' :: ls2'). split; intros.
        + destruct H.
          * subst. exists a. split; auto. left. auto.
          * apply H4 in H as [g'' [H H2]]. exists g''. split; auto. right. auto.
        + destruct H.
          * subst. exists a'. split; auto. left. auto.
          * apply H5 in H as [g'' [H H2]]. exists g''. split; auto. right. auto.
    }

    assert (exists rs1', (forall g', In g' rs1' -> exists g, In g rs1 /\ g ++ {ls2 | rs2} == g') /\ (forall g, In g rs1 -> exists g', In g' rs1' /\ g ++ {ls2 | rs2} == g')). {
      clear H H0. induction rs1.
      - exists []. split; intros [g Hg] HIn; contradiction.
      - apply depth_list_helper_r in H1 as [HDepth1 HDepth2].
        specialize IHn with a {ls2 | rs2}. assert (exists g : game, a ++ {ls2 | rs2} == g). {
          apply IHn. exists (n1). exists (S n2). split; auto. split; auto. lia.  
        }
        destruct H as [a' H].
        apply IHrs1 in HDepth1 as [rs1' [H4 H5]].
        exists (a' :: rs1'). split; intros.
        + destruct H0.
          * subst. exists a. split; auto. left. auto.
          * apply H4 in H0 as [g'' [H0 H1]]. exists g''. split; auto. right. auto.
        + destruct H0.
          * subst. exists a'. split; auto. left. auto.
          * apply H5 in H0 as [g'' [H0 H1]]. exists g''. split; auto. right. auto.
    }

    assert (exists rs2', (forall g', In g' rs2' -> exists g, In g rs2 /\ {ls1 | rs1} ++ g == g') /\ (forall g, In g rs2 -> exists g', In g' rs2' /\ {ls1 | rs1} ++ g == g')). {
      clear H H0 H4. induction rs2.
      - exists []. split; intros [g Hg] HIn; contradiction.
      - apply depth_list_helper_r in H2 as [HDepth1 HDepth2].
        specialize IHn with {ls1 | rs1} a. assert (exists g : game, {ls1 | rs1} ++ a == g). {
          apply IHn. exists (S n1). exists n2. split; auto. split; auto. lia.  
        }
        destruct H as [a' H0].
        apply IHrs2 in HDepth1 as [rs2' [H4 H5]].
        exists (a' :: rs2'). split; intros.
        + destruct H.
          * subst. exists a. split; auto. left. auto.
          * apply H4 in H as [g'' [H H2]]. exists g''. split; auto. right. auto.
        + destruct H.
          * subst. exists a'. split; auto. left. auto.
          * apply H5 in H as [g'' [H H2]]. exists g''. split; auto. right. auto.
    }

    destruct H as [ls1' H]. destruct H0 as [ls2' H0]. destruct H4 as [rs1' H4]. destruct H5 as [rs2' H5].
    exists { (app ls1' ls2') | (app rs1' rs2') }.
    constructor; intros.
    + destruct p; simpl in *.
      * rewrite In_app_iff in H6. destruct H6 as [H6 | H6].
        -- apply H in H6 as [gi' [H6 H7]]. exists gi'. left. split; auto.
        -- apply H0 in H6 as [gi' [H6 H7]]. exists gi'. right. split; auto.
      * rewrite In_app_iff in H6. destruct H6 as [H6 | H6].
        -- apply H4 in H6 as [gi' [H6 H7]]. exists gi'. left. split; auto.
        -- apply H5 in H6 as [gi' [H6 H7]]. exists gi'. right. split; auto.
    + destruct p; simpl in *.
      * destruct H as [_ H]. apply H in H6 as [g' [H6 H7]]. exists g'; split; auto. 
        rewrite In_app_iff. intuition.
      * destruct H4 as [_ H4]. apply H4 in H6 as [g' [H6 H7]]. exists g'; split; auto.
        rewrite In_app_iff. intuition.
    + destruct p; simpl in *.
      * destruct H0 as [_ H0]. apply H0 in H6 as [g' [H6 H7]]. exists g'; split; auto.
        rewrite In_app_iff. intuition.
      * destruct H5 as [_ H5]. apply H5 in H6 as [g' [H6 H7]]. exists g'; split; auto.
        rewrite In_app_iff. intuition.
Qed.

(* And after these lemmas are proved, we assemble them together really easily. *)

Theorem combination_exists : forall g1 g2,
  exists g, g1 ++ g2 == g.
Proof.
  intros.
  specialize depth_exists with g1 as [n1 H1].
  specialize depth_exists with g2 as [n2 H2].
  apply combination_exists_helper with (n1 + n2).
  eauto.
Qed.


(* SECTION 3: Value Classes and Negation 
 * -------------------------------------
 *
 * In this section, we define the four value classes - each game belongs to one
 * and only one class. We then define negation, and see how negation interacts 
 * with the value classes, as well as with addition. *)

(* Recall our analysis of the game 1 + -1. 
 *
 * {[00]|[]} ++ {[]|[00]} == { [{ [] | [00] }] | [{ [00] | [] }] }
 *
 * This sum game feels like it should be the 00 game, since we named its components
 * 1 and -1 and are analogizing combination to addition. Unfortunately, it is not
 * the 00 game. However, like the 00 game, the first player always loses (this can 
 * be proven more easily later). This inspires us to think about classes of game values.
 * Even if 00 and 1 + -1 are not the same game, perhaps we can say they belong to
 * the same value class. *)

(* Values are split into 4 outcome classes. If we can learn the value of the game
 * and its class, then we can determine the outcome. *)

(* Nobody wins in zero games. *)

Definition zero_value (g : game) : Prop := 
  forall p, ~wins_first p g.

(* Left wins in positive games. Recall that we are rooting for Left. *)

Definition positive_value (g : game) : Prop := 
  wins_first L g /\ wins_second L g.

(* R wins in negative games. *)

Definition negative_value (g : game) : Prop :=
  wins_first R g /\ wins_second R g.

(* Is that all? Of course not. What happens to games where the first player always 
 * wins, like [*]. These are not zero, not positive, and not negative. Winning Ways
 * calls these games *fuzzy*, and I quite like that name. *)

Definition fuzzy_value (g : game) : Prop := 
  forall p, wins_first p g.

(* The zero game has zero value. Remember this distinction - the zero game is 
 * simply the canonical zero_value game. Soon (as in 1000 lines lower) we will see
 * all zero value games are equivalent to this one, and therefore each other, but
 * for now we don't know that. *)

Example zero_game_zero_value :
  zero_value 00.
Proof.
  intros p C. inversion C. destruct p; auto.
Qed.

(* So naturally, using the words zero, positive, and negative suggests that there
 * is some sort of ordering (and there is, but we won't talk about it here). However,
 * we also have 'fuzzy' which should raise some eyebrows. *)

Example star_fuzzy : 
  fuzzy_value *.
Proof.
  intros. intro p. apply all_win_star_first.
Qed.

(* ASIDE: We are used to the trichotomy law for most ordered things. It turns out games
 * satisfy a "quadchotomy". If G and H are games, then either G = H (as in, the
 * values are equal, the games can be different game trees certainly), G < H, G > H,
 * and G || H where this is read "G is confused with H". We of course use <=
 * and >=, but we also have "less than or confused with" written <| and
 * "greater than or confused with" written |>.
 *
 * How a game compares with 0 tells you its value class (or outcome class).
 * Fuzzy values are those confused with 0.
 *
 * I think that fuzzyness and confusion are really fun. While we could spend a
 * lot of time talking about the order relation as a whole, we will focus on 
 * fuzzyness in the second half of the project - Nim is a great game for this, since
 * all Nim boards are either zero or fuzzy. Thus, we do NOT talk about order - though,
 * eventually, we will get to value equality, which we call game equivalance. *)

(* We now prove that these classes partition the set of all games. That is to say,
 * all games have a value class, and the value classes do not overlap. *)

Theorem classes_complete : forall g,
  zero_value g \/ positive_value g \/ negative_value g \/ fuzzy_value g.
Proof.
  intros. 
  specialize classic with (P := wins_first L g) as H1.
  specialize classic with (P := wins_second L g) as H2.
  destruct H1, H2.
  - right. left; unfold positive_value. auto.
  - right. right. right. unfold fuzzy_value. intros [|]; trivial.
    apply win_first_opponent_lose_second. auto.
  - left. unfold zero_value. intros [|]; trivial.
    apply lose_first_opponent_win_second. auto.
  - right. right. left. unfold negative_value. split.
    + apply win_first_opponent_lose_second; auto.
    + rewrite lose_first_opponent_win_second in H. auto.
Qed.

Theorem classes_exclusive : forall g,
  ~(zero_value g /\ positive_value g) /\
  ~(zero_value g /\ negative_value g) /\
  ~(zero_value g /\ fuzzy_value g) /\
  ~(positive_value g /\ negative_value g) /\
  ~(positive_value g /\ fuzzy_value g) /\
  ~(negative_value g /\ fuzzy_value g).
Proof.
  repeat (try split); intros [H1 H2];
  try (destruct H2; eapply H1; eauto).
  - apply (H1 L). apply (H2 L).
  - destruct H1, H2. apply win_first_opponent_lose_second in H. contradiction.
  - destruct H1. apply double_neg in H0. apply H0. assert (L = !R); auto. rewrite
    H1. apply win_first_opponent_lose_second. apply H2.
  - destruct H1. apply double_neg in H0. apply H0. assert (R = !L); auto. rewrite
    H1. apply win_first_opponent_lose_second. apply H2.
Qed.

(* One more ingredient before we can really start comparing games (and values) - 
 * negation. *)

(* Remember when I said that -1 was the mirror image of 1. The mirror image of
 * a game is its negation (though again we don't care about the order of subgames 
 * in the two lists). Thus, if L can play G to H, then R can play -G to -H (and all
 * moves of -G look like this). *)

Inductive negation (g g' : game) : Prop :=
  | Neg 
    (H1 : forall p h, p @ g => h -> exists h', !p @ g' => h' /\ negation h h')
    (H2 : forall p h', p @ g' => h' -> exists h, !p @ g => h /\ negation h' h).

(* Some examples: *)

Example neg_zero_game_is_zero_game :
  negation 00 00.
Proof.
  constructor; intros; destruct p; contradiction.
Qed.

Example negative_one_is_neg_one : 
  negation {[00]|[]} {[]|[00]}.
Proof.
  constructor; intros; destruct p; simpl; 
    try contradiction;
    try (exists 00; intuition;
      destruct H; try contradiction; subst; apply neg_zero_game_is_zero_game).
Qed.

(* Is the property of being its own negation unique to zero? Of course not! *)

Example star_is_neg_star : 
  negation * *.
Proof.
  constructor; intros; destruct p; simpl; destruct H; exists 00; subst; intuition;
    try contradiction;
    try apply neg_zero_game_is_zero_game.
Qed.

(* Negation is of course commutative. *)

Theorem neg_comm : forall g g',
  negation g g' -> negation g' g.
Proof.
  specialize game_induction with
    (P := fun g => forall g', negation g g' -> negation g' g)
  as H. apply H; clear H.
  intros g IH g' H1. inversion H1. constructor; intros p h H3.
  - specialize H2 with (p) (h). apply H2 in H3. destruct H3 as [h' H4].
    exists h'. intuition.
  - specialize H0 with (p) (h). apply H0 in H3. destruct H3 as [h' H4].
    exists h'. intuition.
Qed.

Hint Resolve neg_comm : core.

(* Once again, we set out to prove that our relation assigns at least one value to
 * every game. This time, things are much nicer, because we can give a function
 * that performs negation. If I am being honest, I am suprised that Coq's termination
 * checker allows this, I was preparing to write another series of depth proofs to
 * get this done, so this is a pleasant surprise. *)

Fixpoint negate (g : game) : game := 
  match g with 
  | moves ls rs => moves (map negate rs) (map negate ls)
  end.

(* Is this right? Let's prove it. *)

Theorem negate_correct : forall g,
  negation g (negate g).
Proof.
  specialize game_induction with
    (P := fun g => negation g (negate g))
  as H. apply H; clear H; intros [ls rs] IH.
  constructor; intros.
  - exists (negate h). split; eauto.
    destruct p; simpl in *; apply In_map; auto. 
  - destruct p; simpl in *;
    rewrite In_map_iff in H; destruct H as [g [H1 H2]];
    exists g; intuition; apply neg_comm; subst.
    + apply IH with R. auto.
    + apply IH with L. auto. 
Qed.

(* We won't use the function form of negate very much, as we prefer props as much
 * as possible to avoid issues with the termination checker. However, we use it here 
 * to show that every game has a negation, a very useful property. *)

Theorem neg_exists : forall g,
  exists g', negation g g'.
Proof.
  intros. exists (negate g). apply negate_correct.
Qed.

(* It is natural to wonder how negation interacts with addition. Our first question: 
 * What happens when you add a value with its negation. The answer: You get a game of
 * value zero. *)

(* Proof idea: If your opponent makes a move in one subgame, you can make the 
 * corresponding move in the other subgame. Then the resulting game is still composed
 * of subgames that are opposite. If we knew by an inductive hypothesis that the
 * resulting game was value zero, it is easy to show the original game is value zero,
 * since you placed your opponenet in a value zero (losing) position.
 *
 * Note that this requires not induction on the whole game, but induction on one of
 * the subgames. The whole game advances by 2 moves, while the subgames each advance
 * by one.
 *
 * Winning Ways calls this the Tweedledum and Tweedledee argument. *)

Theorem sum_with_neg_is_zero : forall g1 g2 g,
  negation g1 g2 -> g1 ++ g2 == g -> zero_value g.
Proof.
  specialize game_induction with 
    (P := fun g1 => forall g2 g : game, negation g1 g2 -> g1 ++ g2 == g -> zero_value g)
  as H. apply H; clear H; intros g1.
  unfold zero_value; intros. apply lose_first_opponent_win_second.
  constructor; intros. rewrite double_opponent in H2.
  inversion H0; rename H0 into Hinv. inversion H1; clear H1.
  apply H0 in H2. destruct H2 as [gi' H2].
  destruct H2 as [[H8 H9] | [H8 H9]].
  - assert (SavedH8 := H8). apply H3 in H8. destruct H8 as [gi [H10 H11]].
    assert (Hmove := H10).
    apply H4 in H10. destruct H10 as [h H10].
    inversion H9. assert (Hmove' := Hmove). apply H7 in Hmove.
    destruct Hmove as [G [Hmove1 Hmove2]].
    econstructor; try apply Hmove1.
    apply lose_first_opponent_win_second.
    apply H6 in Hmove'. destruct Hmove' as [h' [Hmove' Hmove'']]. 
    eauto.
  - assert (SavedH8 := H8). apply H4 in H8. destruct H8 as [gi [H10 H11]].
    assert (Hmove := H10).
    inversion H9. assert (Hmove' := Hmove). apply H2 in Hmove. destruct Hmove as [G [Hmove1 Hmove2]].
    econstructor; try apply Hmove1.
    apply lose_first_opponent_win_second.
    apply H5 in Hmove'. destruct Hmove' as [h [Hmove' Hmove'']].
    apply neg_comm in H11. 
    eauto.
Qed.

(* Now it is easy to see that 00 is not the only 00 value game (00 is just the 
 * canonical one). *)

Example one_plus_neg_one_val_zero : forall g, 
  {[00]|[]} ++ {[]|[00]} == g -> zero_value g.
Proof.
  intros.
  eapply sum_with_neg_is_zero; eauto.
  apply negative_one_is_neg_one.
Qed.

(* We of course now see that * + * is 0. This * value seems to be getting more 
 * mysterious by the moment! *)

Example star_plus_star_val_zero : forall g,
  * ++ * == g -> zero_value g.
Proof.
  intros.
  eapply sum_with_neg_is_zero; eauto.
  apply star_is_neg_star.
Qed.

(* Our second question: Does negation distribute over addition? Yes, of course it
 * does! Given a sum game, and a negation that game and its parts, we can show that 
 * the negation of the sum is the sum of the negated parts. *)

Theorem neg_distr : forall g g1 g2 h h1 h2 ,
  g1 ++ g2 == g -> negation g1 h1 -> negation g2 h2 -> negation g h ->
  h1 ++ h2 == h.
Proof.
  specialize game_induction with 
    (P := fun g => forall g1 g2 h h1 h2, g1 ++ g2 == g -> negation g1 h1 -> negation g2 h2 
      -> negation g h -> h1 ++ h2 == h)
  as H. apply H; clear H.
  intros g IH g1 g2 h h1 h2 H H0 H1 H2. constructor.
  - intros p h' H3.
    inversion H2; clear H4. apply H5 in H3; clear H5. destruct H3 as [g' [H3 H4]].
    inversion H; clear H6 H7. assert (HSave := H3). apply H5 in H3; clear H5. destruct H3 as [gi' [[H3 H5] | [H3 H5]]].
    + inversion H0. clear H7. apply H6 in H3. clear H6. destruct H3 as [hi' [H3 H6]].
      exists hi'. left. rewrite double_opponent in H3. intuition. 
      eauto.
    + inversion H1. clear H7. apply H6 in H3. clear H6. destruct H3 as [hi' [H3 H6]].
      exists hi'. right. rewrite double_opponent in H3. intuition.
      eauto.
  - intros p h1' H3.
    inversion H0. clear H4. apply H5 in H3. clear H5. destruct H3 as [g1' [H3 H4]].
    inversion H. clear H5 H7. apply H6 in H3. clear H6. destruct H3 as [g' [H3 H5]].
    inversion H2. clear H7. assert (HSave := H3). apply H6 in H3. clear H6. destruct H3 as [h' [H3 H6]].
    exists h'. rewrite double_opponent in H3. intuition. 
    eauto.
  - intros p h1' H3.
    inversion H1. clear H4. apply H5 in H3. clear H5. destruct H3 as [g1' [H3 H4]].
    inversion H. clear H5 H6. apply H7 in H3. clear H7. destruct H3 as [g' [H3 H5]].
    inversion H2. clear H7. assert (HSave := H3). apply H6 in H3. clear H6. destruct H3 as [h' [H3 H6]].
    exists h'. rewrite double_opponent in H3. intuition. 
    eauto.
Qed.    
     
(* How does negation interact with the winning relation? It is clear that the opposite
 * player wins after negation. Note that we don't prove a wins_second version, since
 * we linked winning first with winning second in win_first_opponent_lose_second. *)

Theorem A_wins_B_wins_neg : forall g g' p,
  negation g g' -> wins_first p g <-> wins_first (!p) g'.
Proof.
  specialize game_induction with 
    (P := fun g => forall g' p, negation g g' -> wins_first p g <-> wins_first (!p) g')
  as H. apply H; clear H.
  intros g IH g' p H. split; intros.
  - inversion H0; subst. 
    assert (~wins_first (!p) g'0). {
      apply lose_first_opponent_win_second;
      rewrite double_opponent; auto.
    }
    inversion H. assert (HSaved := H1). apply H4 in H1. clear H4 H5. destruct H1 as [h' [H1 H4]].
    specialize IH with g'0 p h' (!p).
    exists h'; try apply H1.
    apply IH in HSaved; trivial. rewrite double_opponent in *.
    rewrite HSaved in H3. apply lose_first_opponent_win_second in H3. apply H3.
  - inversion H0; subst.
    inversion H. apply H4 in H1. clear H3 H4. destruct H1 as [h' [H1 H4]].
    assert (~wins_first (p) g'0). {
      apply lose_first_opponent_win_second. auto.
    }
    rewrite double_opponent in H1.
    specialize IH with h' p g'0 (!p); rewrite double_opponent in *.
    exists h'; trivial.
    apply IH in H1; try (apply neg_comm; trivial).
    rewrite <- H1 in H3.
    apply lose_first_opponent_win_second in H3. 
    rewrite double_opponent in *. auto.
Qed.

(* One may wonder if negation interacts with the 4 categories of game values in 
 * the expected ways. *)

(* For instance, we can generalize [neg_zero_game_is_zero_game] to hold for all
 * zero value games *)

Theorem neg_zero_zero : forall g g',
  zero_value g -> negation g g' -> zero_value g'.
Proof.
  intros. intros p.
  rewrite A_wins_B_wins_neg; eauto.
Qed.

(* The exact same proof works for fuzzy values. *)

Theorem neg_fuzzy_fuzzy : forall g g',
  fuzzy_value g -> negation g g' -> fuzzy_value g'.
Proof.
  intros. intros p.
  rewrite A_wins_B_wins_neg; eauto.
Qed.

(* And yeah, positive values become negative. *)

Theorem neg_positive_negative : forall g g', 
  positive_value g -> negation g g' -> negative_value g'.
Proof.
  intros. inversion H. constructor.
  - rewrite A_wins_B_wins_neg; try eapply H1.
    apply neg_comm; auto.
  - assert (~wins_first (!L) g). {
      apply lose_first_opponent_win_second; trivial.
    }
    rewrite A_wins_B_wins_neg in H3; eauto.
    apply lose_first_opponent_win_second in H3.
    easy.
Qed.

(* And of course the other way works too. *)

Theorem neg_negative_positive : forall g g', 
  negative_value g -> negation g g' -> positive_value g'.
Proof.
  intros. inversion H. constructor.
  - rewrite A_wins_B_wins_neg; try eapply H1.
    apply neg_comm; auto.
  - assert (~wins_first (!R) g). {
      apply lose_first_opponent_win_second; trivial.
    }
    rewrite A_wins_B_wins_neg in H3; eauto.
    apply lose_first_opponent_win_second in H3.
    easy.
Qed.

(* These facts might be good for clearing goals. *)

Hint Resolve neg_zero_zero neg_fuzzy_fuzzy 
  neg_positive_negative neg_negative_positive : core.

(* We now see how negation interacts with the 4 value categories.
 * Now for where the value categories are useful. *)

(* A major topic of combinatorial game theory is how to analyze a game by looking 
 * at its parts. We can already do this for a lot of games just by looking at the
 * value categories of their parts, though this does not work for every pair of
 * value categories. *)

(* Interestingly, it is easiest to do this by looking at combinations of value 
 * categories, so games were g (>=, <=, |>, or <|) 0 (recall |> and <| are our
 * notations for greater/less than or confused with). *)

(* Thus, we relate combinations of classes to what they say about who wins. *)

Theorem ge_0_iff_L_wins_second : forall g,
  (positive_value g \/ zero_value g) <-> wins_second L g.
Proof.
 split; intros.
 - destruct H.
   + apply H.
   + rewrite win_second_opponent_loses_first. apply H.
 - specialize classic with (wins_first L g) as [H1 | H1].
   + left. split; auto.
   + right; intros [|].
     * apply H1.
     * apply lose_first_opponent_win_second. apply H.
Qed.

Theorem le_0_iff_R_wins_second : forall g,
  (negative_value g \/ zero_value g) <-> wins_second R g.
Proof.
 split; intros.
 - destruct H.
   + apply H.
   + rewrite win_second_opponent_loses_first. apply H.
 - specialize classic with (wins_first R g) as [H1 | H1].
   + left. split; auto.
   + right; intros [|].
     * apply lose_first_opponent_win_second. apply H.
     * apply H1.
Qed.

(* I'll use `ge` for greater than or equals, and `gf` for greater than or fuzzy. 
 * Same for `le` and `lf`. *)

Theorem gf_0_iff_L_wins_first : forall g,
 (positive_value g \/ fuzzy_value g) <-> wins_first L g.
Proof.
 split; intros.
 - destruct H; eauto. apply H.
 - specialize classic with (wins_first R g) as [|].
   + right. intros [|]; auto.
   + left. constructor; auto. apply win_second_opponent_loses_first; auto.
Qed.

Theorem lf_0_iff_R_wins_first : forall g,
 (negative_value g \/ fuzzy_value g) <-> wins_first R g.
Proof.
 split; intros.
 - destruct H; eauto. apply H.
 - specialize classic with (wins_first L g) as [|].
   + right. intros [|]; auto.
   + left. constructor; auto. apply win_second_opponent_loses_first; auto.
Qed.

(* This particularly challenging inductive proof is how we get our foot in the door. 
 * We want to prove that if two games are greater than or equal to zero, then their 
 * sum is also greater than or equal to zero. *)

(* Here is the inductive helper lemma. The induction we choose is super funky,
 * we basically smuggle in what feels like an inductive hypothesis in a case where 
 * it shouldn't be. *)

Theorem G_ge_0_H_ge_0_sum_ge_0_induction : forall g g1 g2,
  (g1 ++ g2 == g -> wins_second L g1 -> wins_second L g2 -> wins_second L g)
  /\ (forall g' g1' g2', L @ g => g' -> g1' ++ g2' == g' -> wins_second L g1' -> wins_second L g2' -> wins_second L g').
Proof.
  specialize game_induction with 
    (P := fun g => forall g1 g2,
      (g1 ++ g2 == g -> wins_second L g1 -> wins_second L g2 -> wins_second L g)
      /\ (forall g' g1' g2', L @ g => g' -> g1' ++ g2' == g' -> wins_second L g1' -> wins_second L g2' -> wins_second L g'))
  as H. apply H; clear H.
  intros g IH. split; intros.
  - constructor; intros.
    assert (HSaved := H2).
    inversion H; apply H3 in H2 as [gi' [[H6 H7]|[H6 H7]]]; clear H3 H4 H5.
    + specialize IH with g' R gi' g2.
      apply IH in HSaved as [H8 IH2]. (* We've smuggled in an inductive hypothesis. *)
      inversion H0; subst. apply H2 in H6.
      inversion H6; subst.
      inversion H7. apply H9 in H3 as [gi'' [H11 H12]]. clear H5 H9 H10.
      assert (HSaved := H11).
      eapply IH2 in H11; eauto.
      econstructor; eauto.
    + specialize IH with g' R g1 gi'.
      apply IH in HSaved as [H8 IH2]. (* We've smuggled in an inductive hypothesis. *)
      inversion H1; subst. apply H2 in H6.
      inversion H6; subst.
      inversion H7. apply H10 in H3 as [gi'' [H11 H12]]. clear H5 H9 H10.
      assert (HSaved := H11).
      eapply IH2 in H11; eauto.
      econstructor; eauto.
  - specialize IH with g' L g1' g2'. apply IH in H as [H _].
    apply H; auto.
Qed.

(* Now for the main proof, which simply refers to the lemma after doing some unpacking. *)

Theorem G_ge_0_H_ge_0_sum_ge_0 : forall g1 g2 g,
  g1 ++ g2 == g ->
  (positive_value g1 \/ zero_value g1) -> 
  (positive_value g2 \/ zero_value g2) ->
  (positive_value g \/ zero_value g).
Proof.
  intros. rewrite ge_0_iff_L_wins_second in *.
  specialize G_ge_0_H_ge_0_sum_ge_0_induction with g g1 g2 as [H2 _].
  apply H2; auto.
Qed.

(* Unsurprisingly, the analog for less than or equal to 0 also holds. We can 
 * avoid induction by using properties of negation and the previous proof. *)

Theorem G_le_0_H_le_0_sum_le_0 : forall g1 g2 g,
  g1 ++ g2 == g ->
  (negative_value g1 \/ zero_value g1) -> 
  (negative_value g2 \/ zero_value g2) ->
  (negative_value g \/ zero_value g).
Proof.
  intros.
  specialize neg_exists with g1 as [g1'].
  specialize neg_exists with g2 as [g2'].
  specialize neg_exists with g as [g'].
  assert (g1' ++ g2' == g'). {
    eapply neg_distr; eauto.
  }
  assert (positive_value g' \/ zero_value g'). {
    eapply G_ge_0_H_ge_0_sum_ge_0.
    - apply H5.
    - destruct H0; eauto.
    - destruct H1; eauto.
  }
  destruct H6; eauto.
Qed.

(* Now we consider fuzzyness. If one of the games is greater than 0 or fuzzy, and 
 * the other is greater or equal to 0, then the resulting game is greater than or
 * fuzzy. *)

(* The proof proceeds by essentially playing a single move in the possibly fuzzy game
 * and then using the previous results. *)

Theorem G_gf_0_H_ge_0_sum_gf_0 : forall g1 g2 g,
  g1 ++ g2 == g ->
  (positive_value g1 \/ fuzzy_value g1) -> 
  (positive_value g2 \/ zero_value g2) ->
  (positive_value g \/ fuzzy_value g).
Proof.
  intros. rewrite gf_0_iff_L_wins_first in *.
  inversion H0; subst. rename g' into g1'.
  inversion H. apply H5 in H2 as [g' [H7 H8]]. clear H4 H5 H6.
  econstructor; eauto.
  rewrite <- ge_0_iff_L_wins_second in *.
  eapply G_ge_0_H_ge_0_sum_ge_0.
  - apply H8.
  - auto.
  - auto.
Qed.

(* And likewise holds for less than. *)

Theorem G_lf_0_H_le_0_sum_lf_0 : forall g1 g2 g,
  g1 ++ g2 == g ->
  (negative_value g1 \/ fuzzy_value g1) -> 
  (negative_value g2 \/ zero_value g2) ->
  (negative_value g \/ fuzzy_value g).
Proof.
  intros.
  specialize neg_exists with g1 as [g1'].
  specialize neg_exists with g2 as [g2'].
  specialize neg_exists with g as [g'].
  assert (g1' ++ g2' == g'). {
    eapply neg_distr; eauto.
  }
  assert (positive_value g' \/ fuzzy_value g'). {
    eapply G_gf_0_H_ge_0_sum_gf_0.
    - apply H5.
    - destruct H0; eauto.
    - destruct H1; eauto.
  }
  destruct H6; eauto.
Qed.

(* We continue marching forwards. We can show that zero values (not just the zero
 * game), are additively neutral, at least with respect to outcome. *)

Theorem zero_neutral_left_outcome : forall g2 z g1 p,
  z ++ g1 == g2 -> zero_value z -> 
  wins_first p g1 <-> wins_first p g2.
Proof.
  intros. apply combination_comm in H. split; destruct p; intros.
  - rewrite <- gf_0_iff_L_wins_first in *.
    eapply G_gf_0_H_ge_0_sum_gf_0; eauto.
  - rewrite <- lf_0_iff_R_wins_first in *.
    eapply G_lf_0_H_le_0_sum_lf_0; eauto.
  - rewrite <- gf_0_iff_L_wins_first in *.
    specialize classic with (positive_value g1 \/ fuzzy_value g1). intros [|]; auto.
    assert (negative_value g1 \/ zero_value g1). { 
      destruct (classes_complete g1) as [|[|[|]]].
      - right. auto.
      - exfalso. apply H2. left. auto.
      - left. auto.
      - exfalso. apply H2. right. auto.  
    }
    eapply or_intror in H0.
    specialize G_le_0_H_le_0_sum_le_0 with g1 z g2 as H4.
    apply H4 in H; eauto.
    specialize classes_exclusive with g2 as H5.
    destruct H, H1; intuition.
  - rewrite <- lf_0_iff_R_wins_first in *.
    specialize classic with (negative_value g1 \/ fuzzy_value g1). intros [|]; auto.
    assert (positive_value g1 \/ zero_value g1). { 
      destruct (classes_complete g1) as [|[|[|]]].
      - right. auto.
      - left. auto.
      - exfalso. apply H2. left. auto.
      - exfalso. apply H2. right. auto.  
    }
    eapply or_intror in H0.
    specialize G_ge_0_H_ge_0_sum_ge_0 with g1 z g2 as H4.
    apply H4 in H; eauto.
    specialize classes_exclusive with g2 as H5.
    destruct H, H1; intuition.
Qed.

(* As a result, two zero games add to another zero game. *)

Theorem zero_plus_zero_zero : forall z g1 g2,
  z ++ g1 == g2 -> zero_value z -> 
  zero_value g1 <-> zero_value g2.
Proof.
  split; intros; intros p. 
  - erewrite <- zero_neutral_left_outcome; eauto using combination_comm.
  - erewrite zero_neutral_left_outcome.
    2: eauto. 1-2: eauto.
Qed.

(* ASIDE: We now have enough material to prove the following chart from Winning
 * Ways p33. We won't (it would be tedious, and not needed for later), but we easily could. 
 *
 * The chart tells you the value of a combination of games G and H, if the value categories 
 * of G and H are known.
 * 
 *            |     H = 0    |     H > 0    |     H < 0    |    H || 0    |
 * +----------+--------------+--------------+--------------+--------------+
 * |  G = 0   |   G + H = 0  |   G + H > 0  |   G + H < 0  |  G + H || 0  |
 * |  G > 0   |   G + H > 0  |   G + H > 0  |   G + H ? 0  |  G + H |> 0  |
 * |  G < 0   |   G + H < 0  |   G + H ? 0  |   G + H < 0  |  G + H <| 0  |
 * |  G || 0  |  G + H || 0  |  G + H |> 0  |  G + H <| 0  |   G + H ? 0  |
 *
 * Entries marked ? can be any of the four. Yes, this means a positive plus a negative
 * might become fuzzy. It even means that two fuzzy games don't have the decency to
 * be either zero or fuzzy, they can also be negative or positive.
 *
 * Of course, it is nice to see that if you remove fuzzyness from the picture, the
 * resulting 3 by 3 matrix looks exactly as you'd expect for run of the mill real
 * numbers. *)



(* SECTION 4: Equivalence
 * ----------------------
 * 
 * While we do not go all in on discussing the order relation, we will define and
 * discuss the properties of game equivalence (which is equality of values in the
 * sense that Winning Ways uses it). We of course prove that game equivalence is
 * an actual equivalence relation, and we prove the equivalence preserves the
 * value categories of games, as well as interactions with negation and sum. *)

(* We compare games G and H by playing one against the negation of the other. If 
 * the resulting game is zero value, then the games are said to be equivalent. *)

Definition equiv (g1 g2 : game) : Prop := forall g2', 
  negation g2 g2' -> forall g3, g1 ++ g2' == g3 -> zero_value g3.

Notation "g1 ~ g2" := (equiv g1 g2) (at level 60).

(* We have basically already proven reflexivity back when we say the sum of a game 
 * and its negative is zero. *)

Theorem equiv_refl : forall g,
  g ~ g.
Proof.
  unfold equiv. intros.
  - eapply sum_with_neg_is_zero; eauto.
Qed.

(* Symmetry is a little harder, but knowing how negation interacts with addition 
 * and zero valued games helps a lot. *)

Theorem equiv_symm : forall g h,
  g ~ h -> h ~ g.
Proof.
  unfold equiv. intros.
  rename g into g2. rename h into g1.
  specialize neg_exists with (g3) as [g3' H2].
  specialize neg_exists with (g1) as [g1' H3].
  assert (g1' ++ g2 == g3'). {
    eapply neg_distr in H1; eauto.
  }
  specialize neg_zero_zero with g3' g3 as H5.
  apply H5; try (apply neg_comm; easy).
  eapply H; eauto.
  apply combination_comm. easy.
Qed. 

(* However, transitivity is really hairy, one of the most difficult goals of the
 * project. Many of the helper lemmas I generated to prove this got moved up earlier
 * into the project, but without them it is far from obvious how to get to transitivity. *)

(* We start with a (very repetitive, but otherwise not horrible) helper lemma,
 * which proves that (g1 + g2) + (g3 + g4) = (g1 + g4) + (g2 + g3).
 * I am not quite sure if this can be proven from associativity (which I didn't prove) 
 * or if it needs to be tackled directly. Either way, I figured this proof may actually
 * be easier, because there is more symmetry to exploit. *)

Theorem combination_swap_outcome : forall s12_34 g1 g2 g3 g4 s12 s34  s14 s23 s14_23 p,
  g1 ++ g2 == s12 -> g3 ++ g4 == s34 -> g1 ++ g4 == s14 -> g2 ++ g3 == s23 ->
  s12 ++ s34 == s12_34 -> s14 ++ s23 == s14_23 ->
  (wins_first p s12_34) <-> (wins_first p s14_23).
Proof.
  specialize game_induction with 
    (P := fun s12_34 => forall 
      g1 g2 g3 g4 s12 s34  s14 s23 s14_23 p,
      g1 ++ g2 == s12 -> g3 ++ g4 == s34 -> g1 ++ g4 == s14 -> g2 ++ g3 == s23 ->
      s12 ++ s34 == s12_34 -> s14 ++ s23 == s14_23 ->
      (wins_first p s12_34) <-> (wins_first p s14_23))
  as H. apply H; clear H.
  intros g IH. split; intros.
  - inversion H5; subst. assert (HSaved := H6).
    inversion H3. apply H8 in H6 as [si' [[H11 H12] | [H11 H12]]]; clear H8 H9 H10.
    + rename si' into s12'. 
      inversion H. apply H6 in H11 as [gi' [[H13 H14] | [H13 H14]]]; clear H6 H8 H9.
      * rename gi' into g1'.
        inversion H1. apply H8 in H13 as [s14' [H15 H16]]. clear H6 H8 H9.
        inversion H4. apply H8 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite <- IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
      * rename gi' into g2'.
        inversion H2. apply H8 in H13 as [s23' [H15 H16]]. clear H6 H8 H9.
        inversion H4. apply H9 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite <- IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
    + rename si' into s34'. 
      inversion H0. apply H6 in H11 as [gi' [[H13 H14] | [H13 H14]]]; clear H6 H8 H9.
      * rename gi' into g3'.
        inversion H2. apply H9 in H13 as [s23' [H15 H16]]. clear H6 H8 H9.
        inversion H4. apply H9 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite <- IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
      * rename gi' into g4'.
        inversion H1. apply H9 in H13 as [s14' [H15 H16]]. clear H6 H8 H9.
        inversion H4. apply H8 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite <- IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
  - inversion H5; subst.
    inversion H4. apply H8 in H6 as [si' [[H11 H12] | [H11 H12]]]; clear H8 H9 H10.
    + rename si' into s14'. 
      inversion H1. apply H6 in H11 as [gi' [[H13 H14] | [H13 H14]]]; clear H6 H8 H9.
      * rename gi' into g1'.
        inversion H. apply H8 in H13 as [s12' [H15 H16]]. clear H6 H8 H9.
        inversion H3. apply H8 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite  IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
      * rename gi' into g4'.
        inversion H0. apply H9 in H13 as [s34' [H15 H16]]. clear H6 H8 H9.
        inversion H3. apply H9 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite -> IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
    + rename si' into s23'. 
      inversion H2. apply H6 in H11 as [gi' [[H13 H14] | [H13 H14]]]; clear H6 H8 H9.
      * rename gi' into g2'.
        inversion H. apply H9 in H13 as [s12' [H15 H16]]. clear H6 H8 H9.
        inversion H3. apply H8 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
      * rename gi' into g3'.
        inversion H0. apply H8 in H13 as [s34' [H15 H16]]. clear H6 H8 H9.
        inversion H3. apply H9 in H15 as [s14_23' [H17 H18]]. clear H6 H8 H9.
        econstructor; eauto.
        apply win_second_opponent_loses_first.
        erewrite IH.
        7: eauto. 3: eauto. 3: eauto.
        1: apply lose_first_opponent_win_second; rewrite double_opponent; eauto.
        1-4: eauto.
Qed.

(* Time for transitivity itself.
 *
 * The proof idea is that if:
 *   g1 + -g2 = 0 and g2 + -g3 = 0
 * Then we can add the equations together to get:
 *   (g1 + -g2) + (g2 + -g3) = 0
 * By applying our swap lemma, we have:
 *   (g1 + -g3) + (g2 + -g2) = 0
 * But the negative cancel, so we get:
 *   g1 + -g3 = 0   
 * Which is precisely what we need. *)

Theorem equiv_trans : forall g1 g2 g3, 
  g1 ~ g2 -> g2 ~ g3 -> g1 ~ g3.
Proof.
  intros.
  specialize neg_exists with (g1) as [g1' H1].
  specialize neg_exists with (g2) as [g2' H2].
  unfold equiv. intros g3' H3 s13' H4.
  assert (HNeg := H2).
  apply H in H2.
  apply H0 in H3.
  assert (exists s12', g1 ++ g2' == s12') by apply combination_exists. 
  assert (exists s23', g2 ++ g3' == s23') by apply combination_exists. 
  destruct H5 as [s12' H5]. destruct H6 as [s23' H6].
  apply H2 in H5 as H7. apply H3 in H6 as H8. clear H2 H3.
  assert (exists s12'_23', s12' ++ s23' == s12'_23' /\ zero_value s12'_23'). {
    specialize combination_exists with s12' s23' as [s12'_23' H9].
    exists s12'_23'. split; auto.
    specialize zero_plus_zero_zero with s12' s23' s12'_23' as H10.
    rewrite <- H10; auto.
  }
  destruct H2 as [s12'_23' [H9 H10]].
  assert (exists s13'_2'2 s2'2, g2' ++ g2 == s2'2 /\ s13' ++ s2'2 == s13'_2'2 /\ zero_value s13'_2'2). {
    specialize combination_exists with g2' g2 as [s2'2 H11].
    specialize combination_exists with s13' s2'2 as [s13'_2'2 H12].
    exists s13'_2'2, s2'2. split; auto. split; auto. 
    intros p.
    erewrite <- combination_swap_outcome.
    1: apply H10.
    5: eauto.
    1-5: eauto. 
  }
  destruct H2 as [s13'_2'2 [s2'2 [H11 [H12 H13]]]].
  apply combination_comm in H12.
  erewrite zero_plus_zero_zero.
  2: apply H12.
  1: apply H13.
  eapply sum_with_neg_is_zero.
    + apply HNeg.
    + apply combination_comm. apply H11.
Qed.

(* So equiv is an equivalence relation. We have essentially discovered the notion
 * of game value - every game has a value, and all games with the same value are
 * equivalent. If you want, you could say that the values themselves are the equivalence
 * classes, but we won't. *)

Add Parametric Relation : game equiv
reflexivity proved by equiv_refl
symmetry proved by equiv_symm
transitivity proved by equiv_trans as equiv_rel.

(* There is a lot to say about game values (indeed, Berlekamp, Conway, and Guy wrote
 * a 4 volume book about them). It turns out that game values model the "surreal"
 * number system. This is a superset of the real numbers, and it also contains 
 * infinite and infinitessimal numbers, as well as strange fuzzy numbers like [*].
 *
 * Of course, we can't look at them all here, and I'm not even going to show the integers
 * (though its not terribly hard to do so). Showing that game value is a well defined
 * and interesting concept is the largest hill we will climb in this abstract domain.
 * We will soon switch gears to talk about a specific game, giving us a chance to
 * apply what we have learned about games. *)

(* Before we depart for Nim, we will prove a few more things about general games. *)

(* First, we show how equivalence interacts with negation. We now prove that the 
 * double negation of a game is equivalent to the game itself. Note that they are 
 * not equal in Coq's perspective, since we allow negation to permute the lists 
 * (and add and remove duplicates, etc). *)

(* First, a lemma, about triple negation. Strangely, this is easier than double negation. *)

Lemma triple_neg_neg : forall g1 g2 g3 g4,
  negation g1 g2 -> negation g2 g3 -> negation g3 g4 -> negation g1 g4.
Proof.
  specialize game_induction with 
    (P := fun g1 => forall g2 g3 g4, negation g1 g2 -> negation g2 g3 -> negation g3 g4 -> negation g1 g4)
  as H. apply H; clear H.
  intros g IH g2 g3 g4 H1 H2 H3. constructor.
  - inversion H1. clear H1 H4.
    inversion H2. clear H2 H4.
    inversion H3. clear H3 H4.
    intros. assert (Hmove := H).
    apply H0 in H. destruct H as [h' [H3 H']].
    apply H1 in H3. destruct H3 as [h'' [H3 H'']].
    apply H2 in H3. destruct H3 as [h''' [H3 H''']].
    exists h'''. rewrite double_opponent in H3. split; eauto.
  - inversion H1. clear H1 H0.
    inversion H2. clear H2 H1.
    inversion H3. clear H3 H1.
    intros.
    apply H2 in H. destruct H as [g' [H1 H']].
    apply H0 in H1. destruct H1 as [g'' [H1 H'']].
    apply H4 in H1. destruct H1 as [g''' [H1 H''']].
    exists g'''. rewrite double_opponent in H1.
    split; eauto.
    apply neg_comm. 
    apply neg_comm in H', H'', H'''.
    eauto.
Qed.

(* And now the main proof. *)

Theorem double_neg_equiv : forall g g' g'',
  negation g g' -> negation g' g'' -> g ~ g''.
Proof.
  unfold equiv. intros.
  assert (negation g g2').
  - eapply triple_neg_neg; eauto.
  - eapply sum_with_neg_is_zero; eauto.
Qed.

(* We can also prove that if two games are equivalent, their negations are equivalent. *)

Theorem neg_equiv : forall g1 g2 g1' g2',
  negation g1 g1' -> negation g2 g2' -> g1 ~ g2 -> g1' ~ g2'.
Proof.
  intros. unfold equiv in *. intros.
  rename g2'0 into g2''.
  rename g3 into g3'.
  specialize neg_exists with g3' as [g3 H5].
  apply neg_comm in H0.
  apply neg_comm in H, H0, H2.
  eapply neg_distr in H3. 2-4: eauto.
  eapply H1 in H0. 2: eauto.
  eapply neg_zero_zero.
  - apply H0.
  - apply neg_comm. assumption.
Qed.

(* We now aim to show that all zero values are equivalent. In other words, there 
 * really is only one zero, just many games with that zero value. *)

(* A helper first. For this one, you have to carefully select which game you induct 
 * on to ensure you can always step there exactly once. *)

Theorem outcome_cancellation : forall g2 p z g1 g1' g3,
  negation g1 g1' -> z ++ g1 == g2 -> g2 ++ g1' == g3 ->
  (wins_first p z <-> wins_first p g3).
Proof.
  specialize game_induction with 
    (P := fun g2 => forall p z g1 g1' g3,
      negation g1 g1' -> z ++ g1 == g2 -> g2 ++ g1' == g3 ->
      (wins_first p z <-> wins_first p g3))
  as H. apply H; clear H.
  intros g IH p z g1 g1' g3 Hneg Hg2 Hg3. split.
  - (* We are p. We play our winning move in z, creating a losing
     * z' for !p. By the induction hypothesis, that corresponds to a losing 
     * g3' for !p, implying the existence of a winning move to g3' for p. *)
    intros. inversion H; subst. rename g' into z'.
    inversion Hg2. apply H3 in H0 as H5. clear H2 H3 H4. destruct H5 as [g2' [H5 H6]].
    inversion Hg3. apply H3 in H5 as H7. clear H2 H3 H4. destruct H7 as [g3' [H7 H8]].
    econstructor; eauto. assert (~wins_first (!p) g3'). {  
      rewrite <- IH; eauto. rewrite lose_first_opponent_win_second. 
      rewrite double_opponent. auto.
    }
    rewrite lose_first_opponent_win_second in H2. destruct p; auto.
  - (* Apply contrapositive. We must show all of our choices are bad. If we play
     * in z to z', it becomes winning for our opponenet. If we play g1 to h1, our
     * opponenet can play g1' to h1'. If we play g1' to h1', our opponent can play 
     * g1 to h1. *)
    apply contrapositive. intros H Contra.
    inversion Contra; subst. rename g' into h3.
    inversion Hg3. assert (HSaved := H0). apply H2 in H0 as [hi [[H5 H6]|[H5 H6]]]; clear H2 H3 H4.
    + (* p chose to advance g2 = {ls | rs} to h2. *)
      rename hi into h2.
      inversion Hg2. assert (HSaved2 := H5). apply H0 in H5 as [hi [[H7 H8]|[H7 H8]]]; clear H0 H2 H3.
      * (* in g2, p chose to advance z to z' *)
        rename hi into z'.
        apply lose_first_opponent_win_second in H. inversion H; subst.
        rewrite double_opponent in H0.
        apply H0 in H7 as H9.
        erewrite IH in H9; eauto. apply win_first_opponent_lose_second in H9. 
        rewrite double_opponent in *. intuition.
      * (* in g2, p chose to advance g1 to h1 *)
        rename hi into h1.
        inversion Hneg. apply H0 in H7 as H9. clear H0 H2. destruct H9 as [h1' [H9 H10]].
        inversion H6. apply H3 in H9 as H11. clear H0 H2 H3. destruct H11 as [hh3 [H11 H2]].
        inversion H1. apply H.
        erewrite IH; try apply H2; eauto.
    + (* p chose to advance g1' to hi *)
      rename hi into h1'.
      inversion Hneg. apply H2 in H5 as H7. clear H0 H2. destruct H7 as [h1 [H7 H8]].
      inversion Hg2. apply H3 in H7 as H9. clear H0 H2 H3. destruct H9 as [h2 [H9 H10]].
      inversion H6. apply H2 in H9 as H11. clear H0 H2 H3. destruct H11 as [hh3 [H11 H12]].
      inversion H1. apply H.
      erewrite IH; try apply H12; eauto.
Qed.

(* We see that 0 + G is equivalent to G. *)

Theorem plus_zero_equiv : forall z g1 g2,
  z ++ g1 == g2 -> zero_value z -> g1 ~ g2.
Proof.
  intros. apply equiv_symm. intros g1' H1 g3 H2 p.
  specialize outcome_cancellation with g2 p z g1 g1' g3 as H3.
  erewrite <- H3; eauto.
Qed.

(* And we see that being equivalent to 00 means a game has value 0. *)

Theorem zero_value_if_equiv_00 : forall g,
  g ~ 00 -> zero_value g.
Proof.
  intros. unfold equiv in H.
    eapply H. 
    + apply neg_zero_game_is_zero_game.
    + apply zero_game_neutral_right.
Qed.

(* The converse holds as well, but it depends on the previous so we seperate the
 * proofs. *)

Theorem equiv_00_if_zero_value : forall g,
  zero_value g -> g ~ 00.
Proof.
  intros. intros g1 H1 g2 H2.
  assert (g1 = 00). {
    inversion H1.
    apply no_plays_zero_game; intros. intros C.
    apply H3 in C as [h [H4 H5]].
    destruct p; inversion H4.
  }
  subst. apply plus_zero_equiv in H2; trivial.
  apply equiv_symm in H2. eapply zero_value_if_equiv_00. auto.
Qed.

(* Although bundling them together is convenient. *)

Theorem zero_equiv_00 : forall g,
  zero_value g <-> g ~ 00.
Proof.
  split. { apply equiv_00_if_zero_value. } { apply zero_value_if_equiv_00. }
Qed.

(* Finally, we show all zeros are the same. 00 is the same value as 100 + -100
 * is the same value as * + *. *)

Theorem zero_equiv : forall g1 g2,
  zero_value g1 -> zero_value g2 -> g1 ~ g2.
Proof.
  intros. rewrite zero_equiv_00 in *.
  rewrite H, H0.
  reflexivity.
Qed.

(* This lets us prove a series of preservation theorems, showing that if two games 
 * are equivalent, then they must have the same value category. *)

(* zero preservation follows immediately, with a little transitivity. *)

Theorem zero_preserved : forall g1 g2,
  g1 ~ g2 -> zero_value g1 -> zero_value g2.
Proof.
  intros. rewrite zero_equiv_00 in H0.
  eapply equiv_trans in H0. 2: { apply equiv_symm. apply H. }
  rewrite <- zero_equiv_00 in H0.
  assumption.
Qed.

(* Positivity requires some effort, but we can use our analysis of compound categories 
 * when analyzing the sum implicity in g1 ~ g2. *)

Theorem positive_preserved : forall g1 g2,
  g1 ~ g2 -> positive_value g1 -> positive_value g2.
Proof.
  intros. unfold equiv in H.
  specialize neg_exists with g2 as [g2'].
  specialize combination_exists with g1 g2' as [g3].
  eapply H in H1 as H10; eauto.
  specialize classes_complete with g2' as [H3 | [H3 | [H3 | H3]]].
  - apply combination_comm in H2.
    apply zero_neutral_left_outcome with _ _ _ L in H2; eauto.
    inversion H0.
    rewrite H2 in H4.
    apply H10 in H4. contradiction.
  - assert (positive_value g1 \/ zero_value g1) by intuition.
    assert (positive_value g2' \/ zero_value g2') by intuition.
    apply G_ge_0_H_ge_0_sum_ge_0 in H2 as H6; eauto.
    assert (positive_value g1 \/ fuzzy_value g1) by intuition.
    apply G_gf_0_H_ge_0_sum_gf_0 in H2; eauto.
    specialize classes_exclusive with g3 as H8.
    intuition.
  - eapply neg_negative_positive; eauto.
  - assert (positive_value g1 \/ zero_value g1) by intuition.
    assert (positive_value g2' \/ fuzzy_value g2') by intuition.
    apply combination_comm in H2.
    apply G_gf_0_H_ge_0_sum_gf_0 in H2; eauto.
    specialize classes_exclusive with g3 as H8.
    intuition.
Qed.

(* Once again, we easily generalize results on positive values to results on negative 
 * values using properties of negation. *)

Theorem negative_preserved : forall g1 g2,
  g1 ~ g2 -> negative_value g1 -> negative_value g2.
Proof.
  intros.
  specialize neg_exists with g1 as [g1'].
  specialize neg_exists with g2 as [g2'].
  eapply neg_equiv in H; eauto.
  apply neg_negative_positive with _ g1' in H0; eauto.
  eapply positive_preserved in H0; eauto.
Qed.

(* Fuzzy preservation could be a little tricky directly, but we can prove it indirectly 
 * by using [classes_exclusive] and the other three preservation lemmas. *)

Theorem fuzzy_preserved : forall g1 g2,
  g1 ~ g2 -> fuzzy_value g1 -> fuzzy_value g2.
Proof.
  intros.
  apply equiv_symm in H.
  specialize classes_exclusive with g1 as H1.
  specialize classes_complete with g2 as [H2 | [H2 | [H2 | H2]]].
  - eapply zero_preserved in H2; eauto. intuition.
  - eapply positive_preserved in H2; eauto. intuition.
  - eapply negative_preserved in H2; eauto. intuition.
  - assumption.
Qed.

(* These can be bundled together to give [outcome_preservation]. *)

Theorem outcome_preservation_one_way : forall g1 g2 p,
  g1 ~ g2 -> wins_first p g1 -> wins_first p g2.
Proof.
  intros.
  destruct p.
  - rewrite <- gf_0_iff_L_wins_first in *. destruct H0.
    + left. eapply positive_preserved; eauto.
    + right. eapply fuzzy_preserved; eauto.
  - rewrite <- lf_0_iff_R_wins_first in *. destruct H0.
    + left. eapply negative_preserved; eauto.
    + right. eapply fuzzy_preserved; eauto.
Qed.

Theorem outcome_preservation : forall g1 g2 p,
  g1 ~ g2 -> wins_first p g1 <-> wins_first p g2.
Proof.
  split; intros.
  - eapply outcome_preservation_one_way; eauto.
  - apply equiv_symm in H. eapply outcome_preservation_one_way; eauto.
Qed.

(* Finally, we look again at how equivalence interacts with addition. It turns out
 * that swapping a summand with an equivalent game yields an equivalent sum. *)

Theorem equiv_sum_right : forall g1 g2 g2' g3 g3',
  g1 ++ g2 == g3 -> g1 ++ g2' == g3' -> g2 ~ g2' -> g3 ~ g3'.
Proof.
  intros. unfold equiv; intros.
  rename g2'0 into neg_g3'.
  specialize neg_exists with g1 as [neg_g1].
  specialize neg_exists with g2' as [neg_g2'].
  assert (neg_g1 ++ neg_g2' == neg_g3'). { eapply neg_distr. 2-4: eauto. 1: eauto. }
  apply combination_comm in H6.
  specialize combination_exists with g1 neg_g1 as [s1].
  specialize combination_exists with g2 neg_g2' as [s2].
  specialize combination_exists with s1 s2 as [s3].
  assert (forall p, wins_first p g0 <-> wins_first p s3). {
    intros p.
    eapply combination_swap_outcome.
    5: eauto. 5: eauto. 1-4: eauto.
  }
  intros p.
  rewrite H10.
  eapply sum_with_neg_is_zero in H4. 2: eauto.
  assert (zero_value s2) by (eapply H1; eauto).
  assert (zero_value s3). { 
    erewrite <- zero_plus_zero_zero; eauto.
  }
  apply H12.
Qed.

(* That's all we have for games in the abstract. We now show how to use this framework 
 * to analyze a specific game. *)



(* SECTION 5: Nim 
 * ---------------
 *
 * In this section, we define and analyze the game Nim. Nim is a desirable game to
 * analyze because it contains lots of fuzzy values, so we can build more intuition
 * about how those strange values work. Also, Nim is an impartial game, meaning that
 * at each position, each player has the same moves. However, Winning Ways claims that 
 * Nim contains the additive structure of *every* impartial game. We won't show that, 
 * but we will analyze that additive structure, so our analysis here applies to many
 * many interesting games. 
 * 
 * Our goal is a decision procedure (i.e. a Coq function), which will tell us 
 * which player wins a given Nim position. After this point, we can declare Nim solved. *) 

(* In a game of Nim, there are several (any number really) piles of stones (or sticks, 
 * coins, counters, etc). On a given player's turn, they choose a pile, and remove
 * any positive number of stones from the pile. In the Normal Play Convention we have
 * been following, the last person to take a stone wins, because their opponent
 * will have no more moves to make. Wikipedia claims that Nim is typically played
 * using the other play convention, where the last person to take a stone loses, but
 * Winning Ways sticks to the Normal Play Convention, and so will we. *)

(* At this point, it might be unclear how to define a game like this - our games 
 * have all been abstract trees. We need some way to bind a game tree to a given
 * Nim board. My strategy is to define two relations - one which encodes the movement 
 * rules for Nim, and another which binds a game tree to a nim board so that the 
 * game can only step to nim positions that the nim board can step to.
 *
 * I believe this two-relation strategy can be followed for other games, though 
 * Nim benefits by being impartial, so the nim_step relation does not say anything
 * about which player is moving. *)

(* This is the relation the encodes legal moves in the game nim. A nim board is
 * simply a list of natural numbers. *)

Inductive nim_step : list nat -> list nat -> Prop :=
  | Take_Head (n m : nat) (H : m < n) (ls : list nat) 
    : nim_step (n :: ls) (m :: ls)
  | Take_Tail (n : nat) (ls1 ls2 : list nat) (H : nim_step ls1 ls2) 
    : nim_step (n :: ls1) (n :: ls2).

Notation "ls1 --> ls2" := (nim_step ls1 ls2) (at level 60).

(* Note: we technically allow 0 piles, it ends up being less annoying than 
 * forcibly removing them. *)

Example nim_step_ex : [5; 3; 0] --> [2; 3; 0].
Proof.
  apply Take_Head. lia.
Qed.

Example nim_step_ex2 : [5; 4; 2; 0] --> [5; 0; 2; 0].
Proof.
  apply Take_Tail. apply Take_Head. lia.
Qed.

(* Our first result is very simple - our version of nim, where 0 piles are allowed 
 * in the list, maintains its length throughout any game step. *)

Theorem nim_preserves_length : forall l1 l2,
  l1 --> l2 -> length l1 = length l2.
Proof.
  intros. induction H; auto.
  - simpl. rewrite IHnim_step. reflexivity.
Qed.

(* We now relate nim positions to game trees. For any nim_step, the game tree contains
 * a move (for each player) to a game corresponding to the board after the nim_step.
 * These are also the only moves allowed, meaning all moves look like that. *)

Inductive nim : list nat -> game -> Prop :=
  | Board (g : game) (ls1 : list nat) 
      (H1 : forall p ls2, nim_step ls1 ls2 -> exists h, nim ls2 h /\ p @ g => h) 
      (H2 : forall p h, p @ g => h -> exists ls2, nim ls2 h /\ nim_step ls1 ls2)
    : nim ls1 g.

(* Some examples of how this works follow. *)

Example nim_game_ex : forall g1 p, 
  nim [5; 3; 0] g1 -> exists g2, nim [2; 3; 0] g2 /\ p @ g1 => g2.
Proof.
  intros. inversion H. remember nim_step_ex as H5. clear HeqH5.
  eapply H1 in H5. apply H5.
Qed.

Example nim_game_ex2 : forall g1 g2 p, 
  nim [5; 3; 0] g1 -> p @ g1 => g2 -> exists l2, nim l2 g2 /\ [5; 3; 0] --> l2.
Proof.
  intros. inversion H. apply H2 in H0. destruct H0 as [l2 H0].
  exists l2. apply H0.
Qed.

(* Some of the games we've already met can be recognized as nim games. For instance,
 * 00 corresponds to the empty nim board. *)

Example empty_nim_is_0 :
  nim [] 00.
Proof.
  constructor; intros.
  - inversion H.
  - destruct p; contradiction.
Qed.

(* Actually, we can go further. Any nim board with no stones in any pile is 00. *)

Theorem all_0_nim_is_0 : forall l,
  (forall n, In n l -> n = 0) -> nim l 00.
Proof.
  constructor; intros.
  - induction H0.
    + specialize H with n. assert (In n (n :: ls)). { left; auto. }
      apply H in H1. lia. 
    + assert (exists h, nim ls2 h /\ p @ 00 => h). {
        apply IHnim_step. intros. apply H. right. apply H1.
      }
      destruct H1 as [h [H1 H2]]. destruct p; contradiction.
  - destruct p; contradiction.
Qed.

(* It ends up being convenient to specialize this.  *)

Example one_empty_pile_nim_is_0 : 
  nim [0] 00.
Proof.
  apply all_0_nim_is_0. intros. destruct H; easy.
Qed.

(* We can also recognize * as the nim game with 1 stone. This makes sense - the 
 * one stone game can only move to a zero stone game, just as * can only move to 00. *)

Example singleton_nim_is_star : 
  nim [1] *.
Proof.
  constructor; intros.
  - inversion H; subst. 
    + assert (m = 0) by lia; subst. 
      exists 00. split.
      * apply all_0_nim_is_0; intros. destruct H0; auto. contradiction.
      * apply star_yields_0.
    + inversion H3.
  - destruct p; inversion H; subst; try contradiction.
    ++ exists [0]. split. { apply all_0_nim_is_0; intros. destruct H0; auto; contradiction. }
       constructor. lia.
    ++ exists [0]. split. { apply all_0_nim_is_0; intros. destruct H0; auto; contradiction. } 
       constructor. lia.
Qed.

(* ASIDE: We can name all of the singleton games analogously. This game is 1* or *, 
 * the game is a 2 stone pile is 2*, and so on. 0* is simply 0. 
 * Note: 2* is distinct from * + *, which is 0. Don't let Winning Ways' notation confuse 
 * you, I also though it was multiplication at first. *)

(* I've claimed that Nim is impartial. There is not a lot of value for us to define
 * impartiality generally, but we will use a key property of impartiality: nim negates
 * itself. *)

Theorem nim_negates_self : forall g1 g2 ls,
  nim ls g1 -> nim ls g2 -> negation g1 g2.
Proof.
  specialize game_induction with 
    (P := fun g1 => forall g2 ls, nim ls g1 -> nim ls g2 -> negation g1 g2)
  as H. apply H; clear H.
  intros g1 IH g2 l H H0.
  constructor; intros.
  - inversion H; subst. apply H3 in H1 as H4. clear H2 H3. destruct H4 as [l' [H4 H5]].
    inversion H0; subst. specialize H2 with (p := !p). apply H2 in H5.
    clear H2 H3. destruct H5 as [h' [H5 H6]].
    exists h'. split. 
    + intuition.
    + eauto.
  - inversion H0; subst. apply H3 in H1 as H4. clear H2 H3. destruct H4 as [l' [H4 H5]].
    inversion H; subst. specialize H2 with (p := !p). apply H2 in H5.
    clear H2 H3. destruct H5 as [h [H5 H6]].
    exists h. split.
    + intuition.
    + eauto.
Qed.

(* Relatedly, the negation of a game of nim is a game of nim for the same board. *)

Theorem neg_nim_nim : forall g1 g2 l, 
  nim l g1 -> negation g1 g2 -> nim l g2.
Proof.
  specialize game_induction with 
    (P := fun g1 => forall g2 l, nim l g1 -> negation g1 g2 -> nim l g2)
  as H. apply H; clear H.
  - intros g1 IH. constructor; intros.
    + inversion H; subst. apply H2 with (!p) _ in H1 as H4. clear H2 H3. destruct H4 as [h [H4 H5]].
      inversion H0. assert (HSaved := H5). apply H2 in H5 as [h' [H5 H6]].
      exists h'. rewrite double_opponent in *; eauto.
    + rename h into h'. inversion H0. apply H3 in H1 as [h [H1 H4]]. clear H2 H3.
      inversion H; subst. assert (HSaved := H1). apply H3 in H1 as [ls2 [H1 H5]].
      exists ls2; split; eauto.
Qed.

(* From here, is is quick to show that all games of nim for the same board are 
 * equivalent. *)

Theorem nim_equiv : forall g1 g2 ls,
  nim ls g1 -> nim ls g2 -> g1 ~ g2.
Proof.
  intros. intros g2' H1 g12' H2.
  eapply neg_nim_nim in H1; eauto.
  specialize nim_negates_self with g1 g2' ls as H3.
  eapply sum_with_neg_is_zero; eauto. apply combination_comm. auto.
Qed.

(* Because nim negates itself, it is impossible that a nim game is positive or 
 * negative. Thus, all nim games are zero, or they are fuzzy. *)

Theorem nim_zero_or_fuzzy : forall g ls,
  nim ls g -> zero_value g \/ fuzzy_value g.
Proof.
  intros.
  specialize nim_negates_self with (g) (g) (ls) as H2.
  specialize classes_exclusive with g as H3. 
  specialize classes_complete with g as [H1|[H1|[H1|H1]]]; try intuition.
  - apply neg_positive_negative in H2; intuition.
  - apply neg_negative_positive in H2; intuition.
Qed.

(* So far, we have seen how nim games interact with equivalence and negation. What
 * about combination? It turns out that the combination of two Nim games is simply
 * the Nim game with both lists of piles appended. However, for our purposes, we 
 * need only show the case where a singleton game (one pile) is added onto another 
 * game. This is our next main goal, and we will need some other proofs along the 
 * way. *)

(* First, we prove the general rule involving append for the nim relation. This 
 * is easy enough. *)

Theorem nim_step_append : forall l3 l1 l2,
  (app l1 l2) --> l3 -> 
  (exists l1', l3 = (app l1' l2)) \/ (exists l2', l3 = (app l1 l2')).
Proof.
  induction l3; intros.
  - intros. inversion H.
  - intros. inversion H; subst; clear H.
    + destruct l1; try rewrite app_nil_l in *.
      * subst. right. exists (a :: l3). auto.
      * injection H0; intros; subst. left. exists (a :: l1). auto.
    + destruct l1; try rewrite app_nil_l in *.
      * subst. right. exists (a :: l3). auto.
      * injection H0; intros; subst. apply IHl3 in H2.
        destruct H2 as [[l1' H] | [l2' H]]; subst.
        -- left. exists (n :: l1'). auto.
        -- right. exists l2'. auto.
Qed.

(* Singelton games admit some simple convenience theorems. Here we show that any
 * singelton game can move to a game with a smaller pile. *)

Theorem nim_pile_can_shrink : forall gn p n m,
  nim [n] gn -> n > m -> 
  exists gm, nim [m] gm /\ p @ gn => gm.
Proof.
  intros.
  inversion H; subst. eapply H1.
  constructor. auto.
Qed.

(* While here we show that if a singeton game moved, it did move to a game with a 
 * smaller pile. *)

Theorem nim_pile_did_shrink : forall gn gn' n p,
  nim [n] gn -> p @ gn => gn' -> exists m, m < n /\ nim [m] gn'.
Proof.
  intros.
  inversion H; subst. eapply H2 in H0 as [ls2 [H3 H4]].
  inversion H4; subst.
  - exists m; split; auto.
  - inversion H7.
Qed.

(* Any singeton game other than the 0 one is fuzzy. We already know the 0 one has
 * value zero. *)

Theorem nonzero_pile_fuzzy : forall n g,
  nim [n] g -> n <> 0 <-> fuzzy_value g.
Proof.
  split; intros.
  - assert ([n] --> [0]). { constructor. lia. }
    intros p.
    inversion H; subst. apply (H2 p _) in H1. destruct H1 as [g' [H1 H4]]. clear H2 H3.
    econstructor; eauto.
    rewrite win_second_opponent_loses_first.
    specialize one_empty_pile_nim_is_0 as H5.
    eapply nim_equiv in H5; try apply H1.
    apply zero_value_if_equiv_00; eauto.
  - intros C; subst.
    specialize one_empty_pile_nim_is_0 as H1.
    eapply nim_equiv in H1; try apply H.
    apply zero_value_if_equiv_00 in H1.
    specialize classes_exclusive with g as H2.
    intuition.
Qed.

(* Time for the big result: If you have a combination of a singleton nim game with 
 * an arbitrary nim game, then that combination is the nim game for the two other
 * games cons'd together. *)

Theorem nim_cons_combinatation : forall gnl n l gn gl ,
  nim [n] gn -> nim l gl -> gn ++ gl == gnl -> nim (n :: l) gnl.
Proof.
  specialize game_induction with
    (P := fun gnl => forall n l gn gl, nim [n] gn -> nim l gl -> gn ++ gl == gnl -> nim (n :: l) gnl)
  as H. apply H; clear H.
  intros gnl IH. intros.
  constructor; intros.
  - inversion H2; subst.
    + eapply nim_pile_can_shrink in H as [gm [H7 H8]]; eauto.
      inversion H1. apply H4 in H8 as [g' [H8 H9]].
      exists g'. eauto.
    + inversion H0; subst. eapply H3 in H6 as [h [H6 H7]]. clear H3 H4.
      inversion H1. apply H5 in H7 as [g' [H7 H8]]. clear H3 H4 H5.
      exists g'. eauto.
  - inversion H1. assert(HSaved := H2). apply H3 in H2 as [g' [[H6 H7]|[H6 H7]]]; clear H3 H4 H5.
    + inversion H; subst. apply H3 in H6 as [ls2 [H8 H9]]; clear H2 H3.
      inversion H9; subst. 2: inversion H5.
      exists (m :: l). split; eauto.
      constructor; eauto.
    + inversion H0; subst. apply H3 in H6 as [ls2 [H8 H9]]. clear H2 H3.
      exists (n :: ls2); split; eauto.
      constructor; eauto.
Qed.

(* Finally, we would like to be able to show a game for any nim position. We first 
 * show games for singleton positions, then we use the previous theorem to combine
 * them together to get games for arbitrary positions. *)

(* We first work on showing that any single pile game exists. This is the inductive 
 * helper lemma. *)

Lemma nim_pile_exists_helper: forall n m,
  m <= n -> exists g, nim [m] g.
Proof.
  induction n; intros.
  - assert (m = 0) by lia. subst.
    exists 00. constructor; intros.
    + inversion H0; subst. { lia. } inversion H4.
    + destruct p; contradiction.
  - assert (m = S n \/ m <= n) by lia. destruct H0 as [H0 | H0]; try eauto.
    clear H; subst.
    
    assert (exists ls, 
        (forall g, In g ls -> exists m, m < S n /\ nim [m] g) /\ 
        (forall m, m < S n -> exists g, In g ls /\ nim [m] g)). {
      revert IHn. induction n.
      - intros. exists [00]. split; intros.
        + exists 0. split; try lia. destruct H as [H | []]. subst. apply all_0_nim_is_0.
          intros. destruct H as [H | []]. auto.
        + assert (m <= 0) by lia. apply IHn in H0.
          exists 00. split. { left. reflexivity. }
          assert (m = 0) by lia. subst. apply all_0_nim_is_0. intros.
          destruct H1 as [H1 | []]. auto.
      - intros. assert (HDup := IHn0).
        specialize HDup with (S n). assert (S n <= S n) by lia.
        apply HDup in H as [gSn h].
        assert (forall m : nat, m <= n -> exists g : game, nim [m] g).
        { intros. assert (m <= S n) by lia. apply IHn0 in H0. auto. }
        apply IHn in H as [ls [H1 H2]].
        exists (gSn :: ls). split; intros.
        + destruct H.
          * subst. exists (S n). split; try lia; assumption.
          * apply H1 in H as [m H]. exists m. split; try lia; intuition.
        + inversion H. 
          -- exists gSn. split; try assumption. left. auto.
          -- assert (m < S n) by lia. apply H2 in H4 as [g H4].
              exists g. split. { right. auto. intuition. } intuition. 
    }

    destruct H as [ls [H H0]].
    exists {ls | ls}.
    constructor; intros.
    + inversion H1; subst.
      * apply H0 in H5 as [g [H5 H6]]. exists g. intuition. destruct p; apply H5.
      * inversion H5.
    + destruct p.
      * apply H in H1 as [m [H1 H2]]. exists [m]. split; auto.
        constructor; auto.
      * apply H in H1 as [m [H1 H2]]. exists [m]. split; auto.
        constructor; auto.
Qed.

(* Here is the main lemma showing a given singleton game exists. *)

Theorem nim_pile_exists : forall n, 
  exists g, nim [n] g.
Proof.
  intros. eapply nim_pile_exists_helper.
  assert (n <= n) by lia. auto.
Qed.

(* Now showing arbitary nim games exists. Here is another inductive helper lemma, 
 * this time inductive on the list. *)

Lemma nim_exists_with_length : forall n l,
  length l <= n -> exists g, nim l g.
Proof.
  induction l; intros.
  - exists 00. apply empty_nim_is_0.
  - assert (exists g : game, nim l g). { apply IHl. simpl in H. lia. }
    destruct H0 as [gl H0]. clear IHl H.
    specialize nim_pile_exists with a as [ga H].
    specialize combination_exists with ga gl as [gal H1].
    exists gal.
    eapply nim_cons_combinatation; eauto.
Qed.

(* And finally, we show that a game exists for each nim position. *)

Theorem nim_exists : forall l,
  exists g, nim l g.
Proof.
  intros. eapply nim_exists_with_length. constructor.
Qed.

(* Now for the imporant part - it turns out that two pile games add to be equivalent
 * to another pile game. For instance, 5* + 6* = 3*. (Try playing 5* + 6* + 3* to 
 * check. The first player should lose.) In other words, Nimbers (what Winning Ways 
 * calls the values associated to each single pile game) are closed under addition! *)

(* But what operation tells us how nimbers add? If you work out an addition table, 
 * you might spot something strange - Nimbers add by doing bitwise exlcusive or!
 * This fact is kinda scary on its own: why would they do this, it seems impossible 
 * that binary representation would be related to nim addition, and yet here it is. *)

(* Coq calls bitwise xor [lxor]. Before we proceed, we must prove three rather 
 * strange properties about lxor. No one would choose these properties in advance, 
 * you have to start the [nimber_add_xor] proof to figure out which properties you
 * need, by working backwards. *)

(* IMPORTANT: I have chosen not complete the proof for the first xor property. I 
 * searched  the standard library for lemmas about lxor, testbit, and < and <=, 
 * and I have not found the right tools to prove this without adding a substantial
 * section to the project devoted to a topic wholly unrelated to games. For these 
 * reasons, we will just admit the property. *)

(* However, the property is quite unintuitive, so one might be rightfully skeptical
 * that it is even true. To alleviate this, I will give an informal proof. *)

Theorem xor_prop_1 : forall m n1 n2, m < lxor n1 n2 -> 
  (exists m1, m1 < n1 /\ lxor m1 n2 = m)
  \/ (exists m2, m2 < n2 /\ lxor n1 m2 = m).
Proof.
  (* Let ⨁ denote the bitwise xor operation.
   *
   * Consider the value n1 ⨁ n2 ⨁ m. This value shows which bits are changed
   * to get from n1 ⨁ n2 to m. Let b be the position of the most significant bit
   * of n1 ⨁ n2 ⨁ m. Such a position must exist (and be a 1), since n1 ⨁ n2 and
   * m differ. Since it is a 1, it must be set in either n1 ⨁ n2 or in m, but not
   * both. Of course, since m < n1 ⨁ n2, we conclude that b is set in n1 ⨁ n2 but
   * not in m (otherwise, the most significant bit that changed when going from n1 ⨁ n2
   * to m changed from a 0 to a 1, so m would be larger, a contradiction).
   *
   * We know b is set in n1 ⨁ n2, so it must be set in one of n1 or n2 (but not both).
   * Without loss of generality, suppose it is set in n1, but not n2. We will now prove
   * that there exists m1 such that m1 < n1 and m1 ⨁ n2 = m, the left side of the 
   * goal (of course, if the bit was set in n2, we would prove the right side, 
   * which is analogous).
   * 
   * Choose m1 = n1 ⨁ (n1 ⨁ n2 ⨁ m). b is set in n1, and in (n1 ⨁ n2 ⨁ m), so we
   * conclude that b is not set in m1 = n1 ⨁ (n1 ⨁ n2 ⨁ m). Since all bits that are
   * more significant than b are zero in (n1 ⨁ n2 ⨁ m), we see that b is the largest 
   * bit where n1 and n1 ⨁ (n1 ⨁ n2 ⨁ m) differ, and it is set in n1. In other 
   * words, m1 = n1 ⨁ (n1 ⨁ n2 ⨁ m) < n1, as required.
   *
   * Finally, we show m1 ⨁ n2 = m. 
   *
   * m1 ⨁ n2
   *         = (n1 ⨁ (n1 ⨁ n2 ⨁ m)) ⨁ n2
   *         = (n1 ⨁ n1) ⨁ (n2 ⨁ n2) ⨁ m        (Associativity and Commutativity of ⨁)
   *         = 0 ⨁ 0 ⨁ m                         (⨁ is nilpotent)
   *         = m                                  (0 is neutral for ⨁)
   *
   * This completes the proof. *)
Admitted.

(* The first xor property is sufficent to prove the other two using basic properties 
 * of lxor, which are in the Coq standard library. *)

Theorem xor_prop_2 : forall m1 n1 n2, m1 < n1 ->
  (exists m2, m2 < n2 /\ lxor n1 n2 = lxor m1 m2)
  \/ (lxor m1 n2 < lxor n1 n2).
Proof.
  intros.
  specialize classic with (lxor m1 n2 < lxor n1 n2) as [H1 | H1]; intuition.
  left. assert (lxor n1 n2 <= lxor m1 n2) by lia. inversion H0.
  - clear H1 H0. destruct n2.
    * repeat rewrite lxor_0_r in *. subst. lia.
    * exists 0; split; try lia.
      assert (lxor (lxor n1 (S n2)) (S n2) = lxor (lxor m1 (S n2)) (S n2)). { 
        rewrite H3. reflexivity.
      }
      repeat rewrite lxor_assoc in H0. rewrite lxor_nilpotent in H0.
      repeat rewrite lxor_0_r in H0.
      lia.
  - assert (lxor n1 n2 < lxor m1 n2) by lia. clear H1 H0 m H3 H2.
    rewrite lxor_comm with m1 _ in H4.
    apply xor_prop_1 in H4 as [[m2 [H1 H2]]|[m2 [H1 H2]]].
    + exists m2; split; auto. rewrite <- H2. apply lxor_comm.
    + rewrite lxor_comm in H2. assert (lxor (lxor m2 n2) n2 = lxor (lxor n1 n2) n2). {
        rewrite H2. reflexivity.
      }
      repeat rewrite lxor_assoc in H0. rewrite lxor_nilpotent in H0.
      repeat rewrite lxor_0_r in H0.
      lia.
Qed.

Theorem xor_prop_3 : forall m2 n1 n2, m2 < n2 ->
  (exists m1, m1 < n1 /\ lxor n1 n2 = lxor m1 m2)
  \/ (lxor n1 m2 < lxor n1 n2).
Proof.
  intros. 
  apply xor_prop_2 with (n2 := n1) in H as [[m1 [H1 H2]]|H1].
  - left. exists m1; intuition.
    rewrite lxor_comm. rewrite H2. rewrite lxor_comm. reflexivity.
  - right.
    rewrite lxor_comm. rewrite lxor_comm with _ n2. auto.
Qed.

(* Now for the inductive helper lemma for the main proof below. We induct on the
 * total size of the game, i.e. the number of stones. Then we play a single round
 * to show that we can always make a move to maintain the lxor property. *)

Theorem nimbers_xor_inductive : forall s g1 g2 g3 s12 s12_3 n1 n2,
  n1 + n2 + (lxor n1 n2) < s ->
  nim [n1] g1 -> nim [n2] g2 -> nim [lxor n1 n2] g3 ->
  g1 ++ g2 == s12 -> s12 ++ g3 == s12_3 ->
  zero_value s12_3.
Proof.
  induction s; intros. 1: lia.
  intros p. rewrite lose_first_opponent_win_second.
  constructor; intros. rewrite double_opponent in *.
  rename g' into s12_3'.
  assert (exists s12_3'', (!p) @ s12_3' => s12_3'' /\ zero_value s12_3''). {
    inversion H4. apply H6 in H5 as [gi' [[H10 H11]|[H10 H11]]]; clear H6 H7 H8.
    - rename gi' into s12'.
      inversion H3. apply H5 in H10 as [gi' [[H12 H13]|[H12 H13]]]; clear H5 H6 H7.
      + rename gi' into g1'. 
        eapply nim_pile_did_shrink in H12 as [m1 [H14 H15]]; eauto.
        assert (HSaved := H14). apply xor_prop_2 with _ _ n2 in H14 as [[m2 [H16 H17]]| H16].
        * eapply nim_pile_can_shrink in H16 as H18; eauto. destruct H18 as [g2'' [H18 H19]].
          inversion H13. apply H7 in H19 as [s12'' [H19 H20]]. clear H5 H6 H7.
          inversion H11. apply H6 in H19 as [s12_3'' [H21 H22]]. clear H5 H6 H7.
          exists s12_3''. split; eauto.
          apply IHs with g1' g2'' g3 s12'' m1 m2; eauto. 
          -- lia.
          -- rewrite <- H17. auto.
        * eapply nim_pile_can_shrink in H16 as H18; eauto. destruct H18 as [g3'' [H18 H19]].
          inversion H11. apply H7 in H19 as [s12_3'' [H20 H21]]. clear H5 H6 H7.
          exists s12_3''. split; eauto.
          apply IHs with g1' g2 g3'' s12' m1 n2; eauto.
          lia.
      + rename gi' into g2'.
        eapply nim_pile_did_shrink in H12 as [m2 [H14 H15]]; eauto.
        assert (HSaved := H14). apply xor_prop_3 with _ n1 _ in H14 as [[m1 [H16 H17]]| H16].
        * eapply nim_pile_can_shrink in H16 as H18; eauto. destruct H18 as [g1'' [H18 H19]].
          inversion H13. apply H6 in H19 as [s12'' [H19 H20]]. clear H5 H6 H7.
          inversion H11. apply H6 in H19 as [s12_3'' [H21 H22]]. clear H5 H6 H7.
          exists s12_3''. split; eauto.
          apply IHs with g1'' g2' g3 s12'' m1 m2; eauto. 
          -- lia.
          -- rewrite <- H17. auto.
        * eapply nim_pile_can_shrink in H16 as H18; eauto. destruct H18 as [g3'' [H18 H19]].
          inversion H11. apply H7 in H19 as [s12_3'' [H20 H21]]. clear H5 H6 H7.
          exists s12_3''. split; eauto.
          apply IHs with g1 g2' g3'' s12' n1 m2; eauto.
          lia.
    - rename gi' into g3'.
      eapply nim_pile_did_shrink in H10 as [m [H12 H13]]; eauto.
      assert (HSaved := H12). apply xor_prop_1 with m n1 n2 in H12 as [[m1 [H14 H15]]|[m2 [H14 H15]]].
      + eapply nim_pile_can_shrink in H14 as HTemp; eauto. destruct HTemp as [g1'' [H16 H17]].
        inversion H3. apply H6 in H17 as [s12'' [H18 H19]]. clear H5 H6 H7.
        inversion H11. apply H6 in H18 as [s12_3'' [H20 H21]]. clear H5 H6 H7.
        exists s12_3''; split; eauto.
        apply IHs with g1'' g2 g3' s12'' m1 n2; subst; eauto.
        lia.
      + eapply nim_pile_can_shrink in H14 as HTemp; eauto. destruct HTemp as [g2'' [H16 H17]].
        inversion H3. apply H7 in H17 as [s12'' [H18 H19]]. clear H5 H6 H7.
        inversion H11. apply H6 in H18 as [s12_3'' [H20 H21]]. clear H5 H6 H7.
        exists s12_3''; split; eauto.
        apply IHs with g1 g2'' g3' s12'' n1 m2; subst; eauto.
        lia.
  }
  destruct H6 as [s12_3'' [H7 H8]].
  econstructor; eauto.
  apply win_second_opponent_loses_first.
  apply H8.
Qed.   

(* And now for the main proof: Nimbers add by xor-ing their stone counts. *)

Theorem nimber_add_xor: forall g1 g2 g3 s12 n1 n2,
  nim [n1] g1 -> nim [n2] g2 -> nim [lxor n1 n2] g3 -> g1 ++ g2 == s12 
  -> s12 ~ g3.
Proof.
  intros. intros neg_g3 H4 s12_3 H5.
  eapply neg_nim_nim in H4; eauto.
  eapply nimbers_xor_inductive.
  1: assert (n1 + n2 + lxor n1 n2 < 1 + n1 + n2 + lxor n1 n2) by lia; apply H3.
  1-5: eauto.
Qed.

(* Now it is clear how to write a decision procedure to solve Nim. *)

(* As we've seen, all nim games are either zero or fuzzy, i.e. either a first player
 * win or a second player win. We now give an algorithm to decide if a given nim 
 * game is a first player win or a second player win. In essence, this algorithm 
 * solves nim. *)

Definition check_first_player_win (ls : list nat) : bool := 
  negb (fold_right (lxor) 0 ls =? 0).

(* All that remains is proving this is correct. Here is the inductive helper proof. *)

Theorem nim_equiv_fold_xor_piles : forall ls gls gn,
  nim ls gls -> nim [fold_right (lxor) 0 ls] gn -> gls ~ gn.
Proof.
  induction ls; intros.
  - simpl in H0. 
    specialize empty_nim_is_0 as H1.
    apply nim_equiv with _ gls _ in H1; eauto.
    rewrite <- H1.
    specialize all_0_nim_is_0 with [0] as H2.
    specialize one_empty_pile_nim_is_0 as H3.
    apply nim_equiv with _ gn _ in H3;
    eauto.
  - specialize nim_exists with [a] as [ga H1].
    specialize nim_exists with ls as [gls' H2].
    specialize combination_exists with ga gls' as [G H3].
    specialize nim_cons_combinatation with G a ls ga gls' as H4.
    assert (nim (a :: ls) G) by auto.
    eapply nim_equiv with gls G (a :: ls) in H5; eauto. rewrite H5.
    clear H H4 H5.
    specialize nim_exists with ([fold_right lxor 0 ls]) as [g_lxor_ls].
    eapply IHls in H2; eauto.
    simpl in H0.
    specialize combination_exists with ga g_lxor_ls as [G' H4].
    specialize nimber_add_xor with ga g_lxor_ls gn G' a (fold_right lxor 0 ls) as H5.
    assert (G' ~ gn) by auto.
    rewrite <- H6.
    eapply equiv_sum_right; eauto.
Qed.

(* And here is the real deal. *)

Theorem check_first_player_win_correct : forall ls g p,
  nim ls g ->
  check_first_player_win ls = true <-> wins_first p g.
Proof.
  split; intros.
  - unfold check_first_player_win in H0.
    assert (fold_right lxor 0 ls <> 0). {
      intros C. rewrite C in H0. easy. (* easy beats auto here? *)
    }
    specialize nim_exists with [fold_right lxor 0 ls] as [g'].
    eapply nim_equiv_fold_xor_piles in H; eauto.
    erewrite outcome_preservation; eauto.
    eapply nonzero_pile_fuzzy in H1; 
    eauto.
  - revert H0. apply contrapositive; intros.
    unfold check_first_player_win in H0.
    rewrite negb_true_iff in H0.
    assert (fold_right lxor 0 ls = 0). {
      destruct (fold_right lxor 0 ls =? 0) eqn:E.
      - rewrite <- eqb_eq; auto.
      - contradiction.
    }
    specialize nim_exists with [fold_right lxor 0 ls] as [g']. 
    eapply nim_equiv_fold_xor_piles in H; eauto.
    erewrite outcome_preservation; eauto.
    rewrite H1 in H2.
    specialize all_0_nim_is_0 with [0] as H3.
    specialize one_empty_pile_nim_is_0 as H4.
    eapply nim_equiv in H2; eauto.
    apply equiv_symm in H2.
    apply zero_value_if_equiv_00 in H2.
    auto.
Qed.

(* Thus, we have done all that we've set out to do. We've demonstrated a lot of 
 * basic properties of games in general, and then we've used those properties to
 * solve Nim. *)



(* Fin. *)
