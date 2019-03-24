From mathcomp Require Import ssreflect ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Equivalence.
  Structure mixin_of T :=
    Mixin {
        op : T -> T -> bool;
        symmetricity : forall (f g : T), op f g = op g f;
        transitivity : forall (f g h : T), op f g -> op g h -> op f h;
        reflexivity : forall (f : T), op f f;
      }.
End Equivalence.

(* locally small category *)
Module Category.
Structure category :=
  Category {
      objects : Type;
      morphisms : objects -> objects -> Set;
      equivMixin : forall {A B : objects}, Equivalence.mixin_of (morphisms A B);
      comp : forall {A B C : objects}, morphisms B C -> morphisms A B -> morphisms A C;
      id : forall {A : objects}, morphisms A A;
      associativity_of_morphisms :
         forall {D E F G : objects},
           let equals := Equivalence.op equivMixin in
           forall (h : morphisms D E)
                  (i : morphisms E F)
                  (j : morphisms F G),
             equals (comp (comp j i) h) (comp j (comp i h));
      identity_morphism_is_right_identity :
        forall {A B : objects},
          let equals := Equivalence.op equivMixin in
          forall (f : morphisms A B), equals (comp f id) f;
      identity_morphism_is_left_identity :
        forall {A B : objects},
          let equals := Equivalence.op equivMixin in
          forall (f : morphisms A B), equals (comp id f) f;
      compatibility_left :
        forall {D E F : objects} (f f': morphisms D E) (g : morphisms E F),
          Equivalence.op equivMixin f f' ->
          Equivalence.op equivMixin (comp g f) (comp g f');
      compatibility_right :
        forall {D E F : objects} (f : morphisms D E) (g g' : morphisms E F),
          Equivalence.op equivMixin g g' ->
          Equivalence.op equivMixin (comp g' f) (comp g f);
    }.

Local Notation "'Ob' C" := (objects C) (at level 2).
Local Notation "'Mor' ( M , N )" := (morphisms M N) (at level 3).
Local Notation "f '\comp' g" := (comp f g) (at level 40).
Definition equals {C : category} {A B : Ob C} :=
  Equivalence.op (@equivMixin C A B).
Local Notation "f '==' g" := (equals f g) (at level 70, no associativity).

Inductive functor (domain codomain : category) : Type :=
  Functor :
    forall (map_of_objects : Ob domain -> Ob codomain)
           (map_of_morphisms : forall {A B : Ob domain}, Mor (A, B) -> Mor (map_of_objects A, map_of_objects B)),
           (forall {A : Ob domain}, (@map_of_morphisms A A id) == id) ->
           (forall {A B C : Ob domain} (f : Mor (A, B)) (g : Mor (B, C)),
            map_of_morphisms (g \comp f) == map_of_morphisms g \comp map_of_morphisms f) ->
           (forall {A B : Ob domain} (f f' : Mor (A, B)),
               f == f' -> map_of_morphisms f == map_of_morphisms f') -> 
      functor domain codomain.

Local Notation "'Fun' ( C , D )" := (functor C D).
Definition map_of_objects (C C' : category) (F : Fun (C, C')) :=
  match F with
  | Functor map_of_objects map_of_morphisms _ _ _ =>
    map_of_objects
  end.
Definition map_of_morphisms {C C' : category} {A B : Ob C} (F : Fun (C, C')) :
  Mor (A, B) -> Mor (map_of_objects F A, map_of_objects F B) :=
  match F with
  | Functor _ map_of_morphisms _ _ _ =>
    map_of_morphisms A B
  end.
Coercion map_of_objects : functor >-> Funclass.
Local Notation "' F " := (map_of_morphisms F) (at level 1).

Inductive isomorphisms {C : category} {A B : Ob C} : Mor (A, B) -> Mor (B, A) -> Type :=
  Isomorphisms : forall (f : Mor (A, B)) (g : Mor (B, A)),
    (g \comp f) == id -> (f \comp g) == id -> isomorphisms f g.

Definition solution_of_diagram {Ic C : category} (F : Fun (Ic, C)) (L : Ob C) :=
  sig (fun (s : (forall (A : Ob Ic), Mor (L, F A))) =>
         forall (A B : Ob Ic) (f : Mor (A, B)), ('F f) \comp (s A) == (s B)).

Local Notation "` F " := (proj1_sig F) (at level 1).

Definition universal_morphism {Ic C : category} {F : Fun (Ic, C)} {L L': Ob C}
           (sL : solution_of_diagram F L) (sL' : solution_of_diagram F L') :=
    sig (fun (l : Mor (L', L)) => forall (A : Ob Ic), (`sL' A) == (`sL A) \comp l).

Inductive limit {Ic C : category} (F : Fun (Ic, C)) (L : Ob C) : Type :=
  Limit : forall (sL : solution_of_diagram F L)
                 (u : (forall (L' : Ob C) (sL' : solution_of_diagram F L'), universal_morphism sL sL')),
    (forall (L' : Ob C) (sL' : solution_of_diagram F L')
            (u' :  Mor (L', L)),
            (forall (A : Ob Ic), (`sL' A) == (`sL A) \comp u') -> ` (u L' sL') == u') -> limit F L.

Lemma identity_morphism_is_the_unique {C : category} {A : Ob C} (id' : Mor (A, A)) :
  (forall {B : Ob C} (f : Mor (A, B)), (f \comp id') == f) -> id' == id.
Proof.
move => H; move: (H _ id).
rewrite /equals Equivalence.symmetricity => H'.
move:(identity_morphism_is_left_identity id') => def.
rewrite Equivalence.symmetricity (Equivalence.transitivity H' def) //.
Qed.

Definition composition_of_functors {C D E : category} (F : Fun (C, D)) (G : Fun (D, E)) : Fun (C, E).
refine (Functor (map_of_objects:=fun x => G (F x)) (map_of_morphisms:=fun A B (f : Mor (A, B)) => 'G ('F f)) _ _ _);
case:F => fo fm fid fcomp fmc /=;
case:G => go gm gid gcomp gmc /=.
+move=>A.
 apply: (Equivalence.transitivity _ (gid (fo A))).
 apply gmc, fid.
+move=>F G H f g.
 apply: (Equivalence.transitivity _ (gcomp _ _ _ (fm F G f) (fm G H g))).
 apply gmc, fcomp.
+move=>A B f f' feq.
 apply gmc, fmc, feq.
Defined.

(* Local Notation "A \simeq B" := (@isomorphisms _ A B) (at level 3). *)

Definition canonical_solution {Ic C : category} (F : Fun (Ic, C)) (L : Ob C) (lim : limit F L) :=
  match lim with
  | Limit sol _ _ => sol
  end.

Definition universality {Ic C : category} (F : Fun (Ic, C)) (L : Ob C) (lim : limit F L) :
  forall (L' : Ob C) (sL' : solution_of_diagram F L'),
    universal_morphism (canonical_solution lim) sL' :=
  match lim with
  | Limit _ u _ => u
  end.

Lemma subst_right_up_to_equals {C : category} (D E F : Ob C) (f f' : Mor (D, E)) (g : Mor (E, F)) (h : Mor (D, F)) :
  f == f' -> (h == g \comp f) = (h == g \comp f').
Proof.
  move => H1.
  have : (g \comp f) == (g \comp f')
  by rewrite /equals compatibility_left //.
  rewrite /equals => H3.
  apply/implyP; case: ifP => H2.
   apply/implyP.
   move: H2; rewrite /equals Equivalence.symmetricity => H2.
   rewrite Equivalence.symmetricity (Equivalence.transitivity H3 H2) //.
  move/implyP: H2 => H2 H4; apply H2.
  move: H3; rewrite Equivalence.symmetricity => H3.
  move: H4; rewrite Equivalence.symmetricity => H4.
  rewrite Equivalence.symmetricity (Equivalence.transitivity H3 H4) //.
Qed.

Lemma subst_left_up_to_equals {C : category} (D E F : Ob C) (f : Mor (D, E)) (g g' : Mor (E, F)) (h : Mor (D, F)) :
  g == g' -> (h == g \comp f) = (h == g' \comp f).
Proof.
  move => H1.
  have : (g \comp f) == (g' \comp f)
  by rewrite /equals compatibility_right // Equivalence.symmetricity //.
  rewrite /equals => H3.
  apply/implyP; case: ifP => H2.
   apply/implyP.
   move: H2; rewrite /equals Equivalence.symmetricity => H2.
   rewrite Equivalence.symmetricity (Equivalence.transitivity H3 H2) //.
  move/implyP: H2 => H2 H4; apply H2.
  move: H3; rewrite Equivalence.symmetricity => H3.
  move: H4; rewrite Equivalence.symmetricity => H4.
  rewrite Equivalence.symmetricity (Equivalence.transitivity H3 H4) //.
Qed.

Lemma associativity_lhs {C : category} (D E F H : Ob C) (f : Mor (D, E)) (g : Mor (E, F)) (h : Mor (F, H)) (i : Mor (D, H)) :
  h \comp (g \comp f) == i = ((h \comp g) \comp f == i).
Proof.
  apply/implyP; case:ifP.
  rewrite /equals => H1.
  apply/implyP.
  move: (associativity_of_morphisms f g h) => H2.
  move: H2; rewrite Equivalence.symmetricity => H2.
  rewrite (Equivalence.transitivity H2 H1) //.
  move/implyP; rewrite /equals => H1 H2.
  apply H1.
  move: (associativity_of_morphisms f g h) => H3.
  rewrite (Equivalence.transitivity H3 H2) //.
Qed.

Lemma associativity_rhs {C : category} (D E F H : Ob C) (f : Mor (D, E)) (g : Mor (E, F)) (h : Mor (F, H)) (i : Mor (D, H)) :
  i == h \comp (g \comp f) = (i == (h \comp g) \comp f).
Proof.
  rewrite /equals Equivalence.symmetricity -/equals.
  rewrite associativity_lhs.
  rewrite /equals Equivalence.symmetricity //.
Qed.

Lemma add_loop {Ic C : category} (F : Fun (Ic, C)) (L : Ob C) (limL : limit F L) (f : Mor (L, L)) :
  let sL := canonical_solution limL in
  (forall (A B : Ob Ic) (g : Mor (A, B)),
    ('F g) \comp (` sL A \comp f) == (` sL B \comp f)) ->
    (forall A : Ob Ic, ` sL A == ` sL A \comp f) ->
  f == id.
Proof.
  case: limL => sL uL pL /= H H'.
  have: ` (uL L sL) == f.
  apply pL, H'.
  have: ` (uL L sL) == id.
  apply pL.
  move => A.
  rewrite /equals Equivalence.symmetricity.
  rewrite identity_morphism_is_right_identity //.
  rewrite /equals Equivalence.symmetricity.
  move => H1 H2.
  rewrite Equivalence.symmetricity.
  apply (Equivalence.transitivity H1 H2).
Qed.

Lemma limit_is_the_unique {Ic C : category} (F : Fun (Ic, C)) (L L' : Ob C) :
  forall (limL : limit F L)
         (limL' : limit F L'),
      let sL := canonical_solution limL in
      let sL' := canonical_solution limL' in
      let f := universality limL sL' in
      let g := universality limL' sL in
      isomorphisms `f `g.
Proof.
  move=> limL limL';
  apply Isomorphisms.
  apply (@add_loop _ _ F _ limL').
  move => A B g.
  rewrite associativity_lhs /equals compatibility_right // Equivalence.symmetricity -/equals (proj2_sig (canonical_solution limL')) //.
  move => A.
  rewrite associativity_rhs.
  case: limL => sL uL pL;
  have H1 : (` (canonical_solution (Limit pL)) A) == ` (canonical_solution limL') A \comp ` (universality limL' (canonical_solution (Limit pL))).
  rewrite (proj2_sig (universality limL' (canonical_solution (Limit pL))) A) //.
  rewrite -(subst_left_up_to_equals _ _ (proj2_sig (universality limL' (canonical_solution (Limit pL))) A)).
  rewrite (proj2_sig (universality (Limit pL) (canonical_solution limL')) A) //.
  
  apply (@add_loop _ _ F _ limL).
  move => A B g.
  rewrite associativity_lhs /equals compatibility_right // Equivalence.symmetricity -/equals (proj2_sig (canonical_solution limL)) //.
  move => A.
  rewrite associativity_rhs.
  case: limL' => sL uL pL;
  have H1 : (` (canonical_solution (Limit pL)) A) == ` (canonical_solution limL) A \comp ` (universality limL (canonical_solution (Limit pL))).
  rewrite (proj2_sig (universality limL (canonical_solution (Limit pL))) A) //.
  rewrite -(subst_left_up_to_equals _ _ (proj2_sig (universality limL (canonical_solution (Limit pL))) A)).
  rewrite (proj2_sig (universality (Limit pL) (canonical_solution limL)) A) //.
Qed.

End Category.




Definition empty : Set := False -> False.
Example cat0 :=
  {| objectss := empty; morphisms:=(fun _ => empty) |}.
