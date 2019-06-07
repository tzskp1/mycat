From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Equivalence.
Structure mixin_of T :=
  Mixin {
      op : T -> T -> Prop;
      symmetricity : forall (f g : T), op f g <-> op g f;
      transitivity : forall (f g h : T), op f g -> op g h -> op f h;
      reflexivity : forall (f : T), op f f;
    }.

Definition eqTypeMixin (T : eqType) : mixin_of T.
  refine (@Mixin T
         eq_op
         _
         (fun (f g h : T) (V : f == g) => eq_ind_r (fun x : T => g == h -> x == h) (fun x : g == h => x) (elimTF eqP V))
         (@eqxx T)).
  intros; by rewrite eq_sym.
Defined.

Definition trivialMixin T : mixin_of T :=
  @Mixin _ (fun _ _ => true) (fun _ _ => conj id id) (fun _ _ _ _ x => x) (fun _ => eqxx true).
Definition falseMixin : mixin_of false := trivialMixin false.
Definition unitMixin : mixin_of unit := trivialMixin unit.
Definition trueMixin : mixin_of true := trivialMixin true.
Definition eq_and {x y} {z w} (H:@eq _ x y) (H':@eq _ z w) :=
  match H in @eq _ _ a return @eq _ (x && z) (a && w) with
  | @Logic.eq_refl =>
    match H' in @eq _ _ b return @eq _ (x && z) (x && b) with
    | @Logic.eq_refl => @Logic.eq_refl _ (x && z)
    end
  end.
Definition prodMixin s e (Ms : mixin_of s) (Me : mixin_of e) : mixin_of (s * e).
refine (@Mixin (s * e)
               (fun s' e' : s * e =>
                  let (s1, e1) := s' in
                  let (s2, e2) := e' in
                  op Ms s1 s2 /\ op Me e1 e2)
               _ _ _).
case => [s1 e1] [s2 e2].
by move: (symmetricity Ms s1 s2) (symmetricity Me e1 e2) => -> ->.
case => [s1 e1] [s2 e2] [s3 e3].
case => Hs12 He12.
case => Hs23 He23.
split.
apply (@transitivity _ Ms _ _ _ Hs12 Hs23).
apply (@transitivity _ Me _ _ _ He12 He23).
case => [s1 e1].
split;
  first exact: reflexivity Ms s1.
exact: reflexivity Me e1.
Defined.
Definition natMixin s : mixin_of (ordinal s).
refine (@Mixin _
               (fun a b =>
                  match a, b with
                  | Ordinal a' _, Ordinal b' _ => a' == b'
                  end)
               _ _ _) => //=.
case => [? ?] [? ?].
rewrite eq_sym //.
case => [? ?] [? ?] [? ?].
move/eqP => -> //.
case => [? ?] //.
Defined.
End Equivalence.

(* locally small category *)
Module Axioms.
Section Equiv.
 Import Equivalence.
 Variable objects : Type.
 Variable morphisms : objects -> objects -> Type.
 Variable id : forall (A : objects), morphisms A A.
 Variable comp : forall {A B C : objects}, morphisms B C -> morphisms A B -> morphisms A C.
 Variable cmp: forall (A B : objects), mixin_of (morphisms A B).
 Local Notation "f '\comp' g" := (comp f g) (at level 40).
 Local Notation "f == g" := (op (cmp _ _) f g).
 Local Definition associativity_of_morphisms :=
   forall D E F G
          (h : morphisms D E)
          (i : morphisms E F)
          (j : morphisms F G),
   (j \comp i) \comp h == j \comp (i \comp h).
 Local Definition identity_morphism_is_right_identity :=
   forall A B (f : morphisms A B), f == f \comp id A.
 Local Definition identity_morphism_is_left_identity :=
   forall A B (f : morphisms A B), f == id B \comp f.
 Local Definition compatibility_left :=
   forall D E F (f f': morphisms D E) (g : morphisms E F),
   f == f' -> g \comp f == g \comp f'.
 Local Definition compatibility_right :=
   forall D E F (f : morphisms D E) (g g' : morphisms E F),
   g == g' -> g \comp f == g' \comp f.
End Equiv.
Module Exports.
Polymorphic Structure category :=
  Category {
      objects : _;
      morphisms : _;
      equiv: _;
      id: _;
      comp: _;
      associativity : @associativity_of_morphisms objects morphisms comp equiv;
      right_idem : @identity_morphism_is_right_identity objects morphisms id comp equiv;
      left_idem : @identity_morphism_is_left_identity objects morphisms id comp equiv;
      comp_left : @compatibility_left objects morphisms comp equiv;
      comp_right : @compatibility_right objects morphisms comp equiv;
    }.
Notation "f '\comp' g" := (comp f g) (at level 40).
Notation "f == g" := (Equivalence.op (equiv _ _) f g).
Notation "'Ob' C" := (objects C) (at level 1).
Notation "'Mor' ( M , N )" := (morphisms M N) (at level 5).
Arguments id [c A].
End Exports.
End Axioms.
Export Axioms.Exports.
  
Structure functor (domain codomain : category) :=
  Functor {
      map_of_objects :> Ob domain -> Ob codomain;
      map_of_morphisms : forall (A B : Ob domain), Mor (A, B) -> Mor (map_of_objects A, map_of_objects B);
      _ : forall (A : Ob domain),
          (@map_of_morphisms A A id) == id;
      _ : forall (A B C : Ob domain) (f : Mor (A, B)) (g : Mor (B, C)),
          (map_of_morphisms (g \comp f)) == (map_of_morphisms g \comp (map_of_morphisms f));
      _ : forall (A B : Ob domain) (f f' : Mor (A, B)),
          f == f' ->
          (map_of_morphisms f) == (map_of_morphisms f');
    }.
Notation "'Fun' ( C , D )" := (functor C D).
Notation "' F " := (map_of_morphisms F) (at level 1).

Inductive isomorphisms {C : category} {A B : Ob C} (f : Mor (A, B)) (g : Mor (B, A)) : Prop :=
  Isomorphisms : (g \comp f) == id -> (f \comp g) == id -> isomorphisms f g.

Hint Resolve (proj1 (Equivalence.symmetricity _ _ _)) Equivalence.reflexivity.
Polymorphic Hint Resolve right_idem left_idem.

Lemma comp0m C (D E : Ob C) (f : Mor (D, E)) : f == id \comp f.
Proof.
  info_auto.
    by apply Equivalence.symmetricity, identity_morphism_is_left_identity. Qed.

Lemma compm0 C (D E : Ob C) (f : Mor (D, E)) : f == f \comp id.
Proof. by apply Equivalence.symmetricity, identity_morphism_is_right_identity. Qed.


Lemma subst_right_up_to_equals {C : category} (D E F : Ob C) (f f' : Mor (D, E)) (g : Mor (E, F)) (h : Mor (D, F)) :
  f == f' -> (h == g \comp f) <-> (h == g \comp f').
Proof.
move => H1.
have : (g \comp f) == (g \comp f') by rewrite /equals; apply: compatibility_left.
rewrite /equals => H3.
split => H2;
 (apply: Equivalence.transitivity;
   first by apply: H2);
 by auto.
Qed.

Lemma subst_left_up_to_equals {C : category} (D E F : Ob C) (f : Mor (D, E)) (g g' : Mor (E, F)) (h : Mor (D, F)) :
  g == g' -> (h == g \comp f) <-> (h == g' \comp f).
Proof.
move => H1.
have : (g \comp f) == (g' \comp f) by rewrite /equals; apply: compatibility_right; auto.
rewrite /equals => H3.
split => H2;
 (apply: Equivalence.transitivity;
   first by apply: H2);
 by auto.
Qed.

(* Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2. *)

Lemma congr_up_to_equals
      {C : category}
      (D E F G : Ob C)
      (f : Mor (D, E))
      (f' : Mor (D, F))
      (g : Mor (E, G))
      (g' : Mor (F, G))
      (h : Mor (E, F)) (i : Mor (F, E)) (I : isomorphisms h i) :
  h \comp f == f' ->
  g == g' \comp h ->
  g \comp f == g' \comp f'.
Proof.
  move => H1 H2.
  case: I => lid rid.
  have: g' \comp (h \comp f) == g' \comp f'.
  rewrite subst_right_up_to_equals; last first.
  apply Equivalence.symmetricity.
  apply: H1.
  exact: Equivalence.reflexivity.
  apply: 
  auto.
  info_auto.
  eauto.
  
  
  g \comp 
  Check (g' \comp h \comp i \comp f').
  have (g' \comp (h \comp f)) == g' \comp h \comp i \comp f'.
  have : g \comp i \comp h \comp f == g' \comp h \comp i \comp f'.
  apply transitivity_lhs.
  rewrite -comp0m.
  About identity_morphism_is_right_identity.
  rewrite -identity_morphism_is_right_identity.
  rewrite subst_right_up_to_equals; last first.
  apply Equivalence.symmetricity.
  apply H1.
  rewrite subst_left_up_to_equals; last first.
  apply Equivalence.symmetricity; apply H2.
  by apply: Equivalence.reflexivity.
Qed.

Definition solution_of_diagram {Ic C : category} (F : Fun (Ic, C)) (L : Ob C) :=
  sig (fun (s : (forall (A : Ob Ic), Mor (L, F A))) =>
         forall (A B : Ob Ic) (f : Mor (A, B)), ('F f) \comp (s A) == (s B)).

Notation "` F " := (proj1_sig F) (at level 1).

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
rewrite /equals /= Equivalence.symmetricity => H'.
move:(identity_morphism_is_left_identity id') => def.
rewrite Equivalence.symmetricity.
by apply: Equivalence.transitivity; first by apply: H'.
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

Lemma associativity_lhs {C : category} (D E F H : Ob C) (f : Mor (D, E)) (g : Mor (E, F)) (h : Mor (F, H)) (i : Mor (D, H)) :
  h \comp (g \comp f) == i <-> ((h \comp g) \comp f == i).
Proof.
split.
rewrite /equals => H1.
by apply: Equivalence.transitivity;
 first apply: associativity_of_morphisms.
move=> H1.
by apply: Equivalence.transitivity;
 first by (apply Equivalence.symmetricity; apply: associativity_of_morphisms).
Qed.

Lemma associativity_rhs {C : category} (D E F H : Ob C) (f : Mor (D, E)) (g : Mor (E, F)) (h : Mor (F, H)) (i : Mor (D, H)) :
  i == h \comp (g \comp f) <-> (i == (h \comp g) \comp f).
Proof.
rewrite /equals Equivalence.symmetricity -/equals.
rewrite associativity_lhs //.
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
apply: identity_morphism_is_right_identity.
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
apply associativity_lhs, compatibility_right.
apply Equivalence.symmetricity, (proj2_sig (canonical_solution limL')).
move => A.
rewrite associativity_rhs.
case: limL => sL uL pL;
have H1 : (` (canonical_solution (Limit pL)) A) == ` (canonical_solution limL') A \comp ` (universality limL' (canonical_solution (Limit pL))).
by apply: (proj2_sig (universality limL' (canonical_solution (Limit pL))) A).
rewrite -(subst_left_up_to_equals _ _ (proj2_sig (universality limL' (canonical_solution (Limit pL))) A)).
by apply (proj2_sig (universality (Limit pL) (canonical_solution limL')) A).

apply (@add_loop _ _ F _ limL).
move => A B g.
apply associativity_lhs, compatibility_right.
apply Equivalence.symmetricity, (proj2_sig (canonical_solution limL)).
move => A.
rewrite associativity_rhs.
case: limL' => sL uL pL;
have H1 : (` (canonical_solution (Limit pL)) A) == ` (canonical_solution limL) A \comp ` (universality limL (canonical_solution (Limit pL))).
by apply: (proj2_sig (universality limL (canonical_solution (Limit pL))) A).
rewrite -(subst_left_up_to_equals _ _ (proj2_sig (universality limL (canonical_solution (Limit pL))) A)).
by apply (proj2_sig (universality (Limit pL) (canonical_solution limL)) A).
Qed.

Inductive natural_transformation {C D : category} (F : Fun (C, D)) (G : Fun (C, D)) : Type :=
  NaturalTransformation : forall (n : forall {X : Ob C}, Mor (F(X), G(X))), 
    (forall (A A' : Ob C) (B B' : Ob D) (f : Mor (A, A')), n \comp 'F(f) == 'G(f) \comp n) ->
    natural_transformation F G.

Notation "'Nat' ( M , N )" := (natural_transformation M N) (at level 5).

Definition map_of_objects_n {C D : category} {F G : Fun (C, D)} (n : Nat (F, G)) :=
  match n with
  | NaturalTransformation n _ => fun x => @n x
  end.
Coercion map_of_objects_n : natural_transformation >-> Funclass.

(* TODO: write about natural transformations. *)
(* TODO: write about adjunctions. *)

From mathcomp Require Import eqtype fintype seq finset ssrnat.

(*
0 --> 1
|     |
>     >
2 --> 3
*)
Definition catn_base n (x y : ordinal n) :=
  match x, y with
  | Ordinal i _, Ordinal j _ => i <= j : Type
  end.

Definition catn_comp n
           (x y z : ordinal n)
           (g : catn_base y z)
           (f : catn_base x y) : catn_base x z.
case: x y z f g => [x Hx] [y Hy] [z Hz] /=.
exact: leq_trans.
Defined.

Definition catn_id n (x : ordinal n) : catn_base x x.
case: x => [x Hx] /=.
exact: leqnn.
Defined.

Example catn (n :  nat) : category.
refine (@Category (ordinal n)
                  (@catn_base n)
                  (fun A B => Equivalence.trivialMixin (catn_base A B))
                  (@catn_comp n)
                  (@catn_id n)  _ _ _ _ _) => //.
Defined.

Example cat0 : category := catn 0.
Example cat1 : category := catn 1.
Example cat2 : category := catn 2.
Example cat4 : category := catn 4.
Notation square := cat4.

Section Limit.
Variable C : category.
Example trivial_embedding1 (A : Ob C) : Fun(cat1, C).
refine (@Functor _ _ (fun _ => A) (fun _ _ _ => id) _ _ _) => //; intros.
+ rewrite /equals; apply Equivalence.reflexivity.
+ rewrite /equals Equivalence.symmetricity.
  apply identity_morphism_is_right_identity.
+ rewrite /equals; apply Equivalence.reflexivity.
Defined.

Definition trivial_embedding0_ob (A : Ob cat0) : Ob C.
case: A => [] //.
Defined.

Definition trivial_embedding0_mor (A B : Ob cat0) :
  Mor(A, B) ->
  Mor(trivial_embedding0_ob A, trivial_embedding0_ob B).
case: A => [] //.
Defined.

Example trivial_embedding0 : Fun(cat0, C).
refine (@Functor _ _ trivial_embedding0_ob trivial_embedding0_mor _ _ _)
        => //; case => //.
Defined.

Definition trivial_embedding2_ob {T : Type} (E F : T) (A : Ob cat2) :=
  match A with
  | Ordinal 0 _ => E
  | Ordinal 1 _ => F
  | Ordinal _ _ => F (* absurd case *)
  end.

Definition trivial_embedding2_mor (A B : Ob C) (g : Mor(A, B)) (E F : Ob cat2) (f : Mor(E, F)) :
    Mor(trivial_embedding2_ob A B E, trivial_embedding2_ob A B F).
case: E F f => [m Hm] [n Hn] f.
case: m Hm f => [|m] Hm f.
 case: n Hn f => [|n] Hn f.
  apply id.
 case: n Hn f => [|n] Hn f.
  apply g.
 case: n Hn f => //.
case: m Hm f => [|m] Hm f.
 case: n Hn f => [|n] Hn //= f.
 case: n Hn f => [|n] Hn //= f.
 apply id.
case: m Hm f => //.
Defined.

Example trivial_embedding2 (A B : Ob C) (f : Mor(A, B)) : Fun(cat2, C).
refine (@Functor _ _ (trivial_embedding2_ob A B)
                 (@trivial_embedding2_mor A B f)
                 _ _ _) => //.
case => m Hm.
repeat case:m Hm => [|m] Hm //=; apply Equivalence.reflexivity.
case => [m Hm] [n Hn] [p Hp] h i.
repeat case:m Hm h => [|m] Hm h //=;
repeat case:n Hn i h => [|n] Hn i h //=;
repeat case:p Hp i h => [|p] Hp i h //=;
rewrite /equals Equivalence.symmetricity;
try apply identity_morphism_is_left_identity;
apply identity_morphism_is_right_identity.
case => [m Hm] [n Hn] h i H.
repeat case:m Hm i h H => [|m] Hm i h H //=;
repeat case:n Hn i h H => [|n] Hn i h H //=;
repeat case:p Hp i h H => [|p] Hp i h H //=;
apply Equivalence.reflexivity.
Defined.

Definition opposite_category : category.
refine (@Category (Ob C)
                  (fun A B => Mor(B, A))
                  (fun A B => @equivMixin C B A)
                  (fun _ _ _ f g => g \comp f)
                  (@id C) _ _ _ _ _) => //.
move => D E F G /= h i j.
rewrite Equivalence.symmetricity.
apply associativity_of_morphisms.
move => A B /= f.
apply identity_morphism_is_left_identity.
move => A B /= f.
apply identity_morphism_is_right_identity.
move => D E F /= f f' g Eq.
apply compatibility_right.
rewrite Equivalence.symmetricity //.
move => D E F /= f f' g Eq.
apply compatibility_left.
rewrite Equivalence.symmetricity //.
Defined.

Definition final_object L := limit trivial_embedding0 L.
Definition kernel A B (f : Mor(A, B)) L := limit (trivial_embedding2 f) L.
End Limit.

Notation "'Op' C" := (opposite_category C) (at level 1).

Section CoLimit.
Variable C : category.
Definition initinal_object L := limit (@trivial_embedding0 (Op C)) L.
Definition cokernel A B (f : Mor(A, B)) L :=
  limit (@trivial_embedding2 (Op C) _ _ f) L.
End CoLimit.

Example pushout {C D : category} (F : Fun (C, D)) : category.
refine (@Category { B : Ob D | exists (A : Ob C), F (A) = B }
                  (fun A B => Mor (proj1_sig A, proj1_sig B))
                  (fun A B => @equivMixin D (proj1_sig A) (proj1_sig B))
                  (fun A B C => @comp D (proj1_sig A) (proj1_sig B) (proj1_sig C))
                  _ _ _ _ _ _); intros.
by apply: associativity_of_morphisms.
by apply: identity_morphism_is_right_identity.
by apply: identity_morphism_is_left_identity.
by apply: compatibility_left.
by apply: compatibility_right.
Defined.

Inductive natural_isomorphisms
  {C D : category}
  {F G : Fun (C, D)}
  : Nat (F, G) -> Nat (G, F) -> Prop :=
  NaturalIsomorphisms :
    forall (n : Nat (F, G)) (m : Nat (G, F)),
    (forall (X : Ob C), isomorphisms (n X) (m X)) -> 
    natural_isomorphisms n m.

Variable nat_isom_decidable :
  forall (C D : category)
         (F G : Fun (C, D)),
  decidable (exists (N : Nat (F, G)) (M : Nat (G, F)), natural_isomorphisms N M).

Lemma ni_sym C D (F G : Fun (C, D)) (N : Nat (F, G)) (M : Nat (G, F)) :
  natural_isomorphisms N M <-> natural_isomorphisms M N.
Proof.
  case neq : N => [n ne]; case meq : M => [m me].
  rewrite -neq -meq; split => H;
  case: H neq meq => ? ? H neq meq;
  apply: NaturalIsomorphisms;
  move: neq meq H => -> -> H X;
  apply: Isomorphisms;
  by case: (H X).
Qed.

Lemma nid_sym C D (F G : Fun (C, D)) :
  nat_isom_decidable F G <-> nat_isom_decidable G F.
Proof.
  split; move/sumboolP => H; apply/sumboolP;
  case: H => N [M] H; do! apply: ex_intro;
  rewrite ni_sym; by apply: H.
Qed.

Definition composition_of_natural_transformations
           {C D : category}
           {F G H : Fun (C, D)}
           (N : Nat (F, G)) (M : Nat (G, H)) : Nat (F, H).
apply (@NaturalTransformation _ _ _ _ (fun X => M X \comp N X)).
case: N => [N ne]; case: M => [M me].
move => A A' B B' f /=.
apply associativity_lhs.

apply congr_up_to_equals.
apply associativity_rhs.

apply associativity_lhs.
apply associativity_lhs.
apply: Equivalence.transitivity.
apply Equivalence.symmetricity.
rewrite -/equals.
rewrite subst_left_up_to_equals.
apply: ne.
rewrite subst_right_up_to_equals.
apply: me.

move: (me A A' B B' f) => /= H''.
exact : H''.
apply H''.

apply associativity_rhs.


rewrite subst_left_up_to_equals.
rewrite subst_right_up_to_equals.
rewrite subst_right_up_to_equals.

apply: me.
apply: subst_right_up_to_equals.
apply: me.
apply (ne A A' B B' f).
intros.

apply Equivalence.symmetricity.
rewrite -ne.
rewrite ne.
apply associativity_lhs.
apply associativity_rhs.

  apply NaturalTransformation .
refine (NaturalTransformation _).
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

Definition natIsomMixin C D : Equivalence.mixin_of (Fun (C, D)).
   refine (@Equivalence.Mixin _
                              (@nat_isom_decidable C D)
                              (@nid_sym C D)
                              _
                              _).
   move => f g h /sumboolP [N1 [M1 H1]] /sumboolP [N2 [M2 H2]].
   apply/sumboolP; do! apply: ex_intro.
   move: H1 H2;
   case n1eq : N1 => [n1 n1e];
   case n2eq : N2 => [n2 n2e];
   case m1eq : M1 => [m1 m1e];
   case m2eq : M2 => [m2 m2e];
   rewrite -n1eq -m1eq -n2eq -m2eq => H1 H2.
   case: H1 n1eq m1eq => ? ? H1 n1eq m1eq.
   case: H2 n2eq m2eq => ? ? H2 n2eq m2eq.
   move: n1eq m1eq n2eq m2eq H1 H2 => -> -> -> -> H1 H2.
   About NaturalIsomorphisms .
   apply: NaturalIsomorphisms => X;
   apply: Isomorphisms.
   case: (H1 X); case: (H2 X); intros;
   do 2 apply: Equivalence.transitivity.
   apply: n1e.
   apply: associativity_rhs.
   apply: transitivity.
   case.
   
   
   
   case: (H1 X) => [? ? H1' H1''].
   case: (H2 X) => [? ? H2' H2''].
   apply: n1e;
   apply: m2e;
   apply: m1e;
   apply: n2e.
   
   apply: H2''.
   
   
   apply: H1'.
   ; case: (H2 X) => //.
   intros.
   move => [].
   => []. H1 H2.
   move => H1 H2.
   apply: 
  case: H neq meq => ? ? H neq meq;
   by [].
   move => f g.
   split.
   rewrite /=.
   by [].
   Print decidable .
   rewrite /nat_isom_decidable.

About Equivalence.Mixin.
  
Example categories : category.
refine (@Category category
                  functor
                  (fun C D =>
                     Equivalence.Mixin
                       _
                       _ _: Equivalence.mixin_of (Fun (C, D)))
                  _ _ 
                  _ _ _ _ _).
intros.

Definition trivial_embedding2_ob {T : Type} (E F : T) (A : Ob cat2) :=
  match A with
  | Ordinal 0 _ => E
  | Ordinal 1 _ => F
  | Ordinal _ _ => F (* absurd case *)
  end.

Example pair (C D : category) : category.


refine (@Category (Ob C * Ob D)
                  (fun (A B : Ob C * Ob D) => (Mor (fst A, fst B) * Mor (snd A, snd B)))
                  (fun A B => (@equivMixin C (fst A) (fst B), @equivMixin D (snd A) (snd B)))
                  (fun A B C => (@comp C (fst A) (fst B) (fst C), @comp D (snd A) (snd B) (snd C)))
                  _ _ _ _ _ _).
intros; by apply: associativity_of_morphisms.
intros; by apply: identity_morphism_is_right_identity.
intros; by apply: identity_morphism_is_left_identity.
intros; by apply: compatibility_left.
intros; by apply: compatibility_right.
Defined.

Inductive adjunction {C D : category} (F : Fun (C, D)) (G : Fun (D, C)) (f : Nat (F, G)) : Type :=
  Adjunction : forall (A : Ob C)
                      (B : Ob D)
                      (f : Hom (A , G(B)) -> Hom (F(A), B)),
    injective f ->
    surjective f -> adjunction 
    
                      
    
  
Inductive limit {Ic C : category} (F : Fun (Ic, C)) (L : Ob C) : Type :=
  Limit : forall (sL : solution_of_diagram F L)
                 (u : (forall (L' : Ob C) (sL' : solution_of_diagram F L'), universal_morphism sL sL')),
    (forall (L' : Ob C) (sL' : solution_of_diagram F L')
            (u' :  Mor (L', L)),
            (forall (A : Ob Ic), (`sL' A) == (`sL A) \comp u') -> ` (u L' sL') == u') -> limit F L.
  
End Category.