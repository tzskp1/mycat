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

From mathcomp Require Import eqtype fintype seq finset ssrnat.

Definition eqTypeMixin (T : eqType) : mixin_of T :=
  @Mixin T
         eq_op
         (@eq_sym T)
         (fun (f g h : T) (V : f == g) => eq_ind_r (fun x : T => g == h -> x == h) (fun x : g == h => x) (elimTF eqP V))
         (@eqxx T).
Definition trivialMixin T : mixin_of T :=
  @Mixin _ (fun _ _ => true) (fun _ _ => eqxx true) (fun _ _ _ _ x => x) (fun _ => eqxx true).
Definition falseMixin : mixin_of false := trivialMixin false.
Definition unitMixin : mixin_of unit := trivialMixin unit.
Definition trueMixin : mixin_of true := trivialMixin true.
(* Canonical Structure equivMixin_of_prod s e (Ms : mixin_of s) (Me : mixin_of e) : mixin_of (s * e). *)
Print rel.
(* Check (pred Type). *)
(* Lemma test (a b c d : bool) : a = b -> c = d -> a = c -> b = d. *)
(* Proof. *)
(*   move => H1 H2 H3. *)
(*   move:(boolP  *)
(*   move:transitive . *)
Canonical Structure prodMixin s e (Ms : mixin_of s) (Me : mixin_of e) : mixin_of (s * e).
(* Definition prodMixin s e (Ms : mixin_of s) (Me : mixin_of e) : mixin_of (s * e). *)
refine (@Mixin (s * e)
               (fun s' e' : s * e =>
                  let (s1, e1) := s' in
                  let (s2, e2) := e' in
                  op Ms s1 s2 && op Me e1 e2)
               _ _ _).
(* Print eq_refl. *)
(* Print Logic.eq_refl. *)
(* Print eq_refl. *)
(* Print eq. *)
(* Print Logic.eq_refl. *)
(* Check (eq_refl 1). *)
(* Check (@eq _ _ 1). *)
(* Check (match (eq_refl (1,2)) in @eq _ _ x return (x = _) with *)
(*        | Logic.eq_refl => Logic.eq_refl *)
(*        end). *)
(* Definition eq_sym (A:Type) (x y:A) (H:@eq A x y) : @eq A y x := *)
(* Definition eq_sym (A:Type) (x y:A) (H:@eq A x y) := *)
(* match H in @eq _ _ z return @eq A z x with *)
(* | @Logic.eq_refl => *)
(*   @Logic.eq_refl _ x *)
(* end. *)
(* Print conj . *)
(* Definition eq_andr {x y} (z: bool) (H:@eq _ x y) := *)
(* match H in @eq _ _ w return @eq _ (x && z) (w && z) with *)
(* | @Logic.eq_refl => *)
(*   @Logic.eq_refl _ (x && z) *)
(* end. *)
(* Print pair. *)
(* Definition letlet s e (f g : s * e) S W := (let (_, _) return (let (_, _) := f in let (_, _) := g in S) := f in (let (_, _) return (let (_, _) := g in S) := g in W)). *)
(* Arguments letlet /. *)
Definition eq_and {x y} {z w} (H:@eq _ x y) (H':@eq _ z w) :=
  match H in @eq _ _ a return @eq _ (x && z) (a && w) with
  | @Logic.eq_refl =>
    match H' in @eq _ _ b return @eq _ (x && z) (x && b) with
    | @Logic.eq_refl => @Logic.eq_refl _ (x && z)
    end
  end.
(* Definition eq_letlet {s e} {A : Type} {x y : A} (f g : s * e) (H:@eq A x y) := *)
(*   let letlet s e (f g : s * e) S W := (let (_, _) return (let (_, _) := f in let (_, _) := g in S) := f in (let (_, _) return (let (_, _) := g in S) := g in W)) in *)
(*   match H in @eq _ _ b return @eq _ (letlet _ _ f g A x) (letlet _ _ f g A b) with *)
(*   | @Logic.eq_refl => @Logic.eq_refl _ (letlet _ _ f g A x) *)
(*   end. *)

(* Print eq_letlet. *)

(* refine (fun f g =>  *)
(*           eq_letlet f g (eq_and (symmetricity Ms (fst f) (fst g)) (symmetricity Me (snd f) (snd g)))). *)
(*           in @eq _ x y *)
(*           return @eq _ (@letlet _ _ f g x _) (@letlet _ _ f g y _) *)
(*           with *)
(*           | @Logic.eq_refl => *)
(*             @Ligic.eq_refl _ (@letlet _ _ f g x _) *)
(*           end). *)

(* move => f g. *)
(* About fst. *)
(* Print letlet. *)
(* Check (let (_, _) return (let (_, _) := f in let (_, _) := g in bool) := f in (let (_, _) return (let (_, _) := g in bool) := g in I)). *)
(* Check (let (_, _) return (let (_, _) := f in let (_, _) := g in True) := f in (let (_, _) return _ := g in I)). *)
(*   eq_andr (op Me e1 e2) (symmetricity Ms s1 s2))). *)
(* exact (eq_and (symmetricity Ms (fst f) (fst g)) (symmetricity Me (snd f) (snd g))). *)
(*          r (op Me (snd f) (snd g)) ). *)
(* Check (let (s1, e1) return (let (s1, e1) := f in let (s2, e2) := g in _) := f in *)
(*  (let (s2, e2) return let (s2, e2) := g in _ := g in *)
(*   eq_andr (op Me e1 e2) (symmetricity Ms s1 s2))). *)
(* exact  *)


(* match eqxx *)
(*       (let (s1, e1) := f in let (s2, e2) := g in op Ms s1 s2 && op Me e1 e2) *)
(*       in @eq _ _ z return  *)
(*       @eq _ z (let (s1, e1) := g in let (s2, e2) := f in op Ms s1 s2 && op Me e1 e2) *)
(* with *)
(* | @Logic.eq_refl => *)
(*   @Logic.eq_refl _ (let (s1, e1) := g in let (s2, e2) := f in op Ms s1 s2 && op Me e1 e2) *)
          
(* refine (eq_refl _). *)
(* have: (let (s0, e0) := f in let (s3, e3) := g in True). *)
(* exact (let (_, _) return (let (s0, e0) := f in let (s3, e3) := g in True) := f in (let (_, _) return _ := g in)). *)
(*   (let (_, _) return _ := g in I). *)

(* Check (symmetricity Ms s1 s2). *)
(* Check (symmetricity Me e1 e2). *)
(* Check  *)
(*               (@eq_sym  _ _)). *)

(* (*                         move:(symmetricity Ms) . *) *)
(* Check (elimTF eqP (@eq_sym _ _ _)). *)
(* Print eq_refl. *)
(* Print eq. *)
(* Check elimTF . *)
(* e *)
(* About eq_sym. *)
(* Check (fun x (y : x == 2) => *)
(* match y return x == 1 with *)
(* | e => e *)
         
(* end *)
(* ). *)

(* refine (fun f g =>  *)
(*           let (s1, e1) return _  := f in *)
(*           let (s2, e2) return _  := g in *)
(*           _). *)
  
(* forall f g : s * e, (let (s1, e1) := f in let (s2, e2) := g in op Ms s1 s2 && op Me e1 e2) = (let (s1, e1) := g in let (s2, e2) := f in op Ms s1 s2 && op Me e1 e2) *)
(*                         (symmetricity Ms) *)
(*                           s1 s2 && op Me e1 e2) *)
                          
   
(* move => t. *)
(* move: (fun *)
(*     evar_0 : forall (a : s) (b : e), *)
(*       (fun p : s * e => *)
(*          forall g : s * e, *)
(*            (let (s1, e1) := p in *)
(*             let (s2, e2) := g in *)
(*             op Ms s1 s2 && op Me e1 e2) = *)
(*            (let (s1, e1) := g in *)
(*             let (s2, e2) := p in *)
(*             op Ms s1 s2 && op Me e1 e2))  *)
(*         (a, b) => *)
(*     let *)
(*       (x, x0) as p *)
(*       return *)
(*       ((fun p0 : s * e => *)
(*           forall g : s * e, *)
(*             (let (s1, e1) := p0 in *)
(*              let (s2, e2) := g in op Ms s1 s2 && op Me e1 e2) = *)
(*             (let (s1, e1) := g in *)
(*              let (s2, e2) := p0 in op Ms s1 s2 && op Me e1 e2)) p) := *)
(*       t in *)
(*     evar_0 x x0). *)
(* Check  *)
(* (fun (t : s * e) (evar_0 : forall (a : s) (b : e), *)
(*       (fun p : s * e => *)
(*          forall g : s * e, *)
(*            (let (s1, e1) := p in *)
(*             let (s2, e2) := g in *)
(*             op Ms s1 s2 && op Me e1 e2) = *)
(*            (let (s1, e1) := g in *)
(*             let (s2, e2) := p in *)
(*             op Ms s1 s2 && op Me e1 e2)) *)
(*         (a, b) => *)
(*     let (x, x0) as p return *)
(*       ((fun p0 : s * e => *)
(*           forall g : s * e, *)
(*             (let (s1, e1) := p0 in *)
(*              let (s2, e2) := g in op Ms s1 s2 && op Me e1 e2) = *)
(*             (let (s1, e1) := g in *)
(*              let (s2, e2) := p0 in op Ms s1 s2 && op Me e1 e2)) p) := *)
(*         t in *)
(*     evar_0 x x0). *)
case => [s1 e1] [s2 e2].
apply (eq_and (symmetricity Ms s1 s2) (symmetricity Me e1 e2)).

case => [s1 e1] [s2 e2] [s3 e3].
case/andP => Hs12 He12.
case/andP => Hs23 He23.
apply/andP; split.
apply (@transitivity _ Ms _ _ _ Hs12 Hs23).
apply (@transitivity _ Me _ _ _ He12 He23).

case => [s1 e1].
rewrite (reflexivity Ms) (reflexivity Me) //.
Defined.
Print prodMixin.

fun (s e : Type) (Ms : mixin_of s) (Me : mixin_of e) =>
{|
op := fun s' e' : s * e =>
      let (s1, e1) := s' in let (s2, e2) := e' in op Ms s1 s2 && op Me e1 e2;
symmetricity := fun _top_assumption_ : s * e =>
                (fun
                   _evar_0_ : forall (a : s) (b : e),
                              (fun p : s * e =>
                               forall g : s * e,
                               (let (s1, e1) := p in
                                let (s2, e2) := g in
                                op Ms s1 s2 && op Me e1 e2) =
                               (let (s1, e1) := g in
                                let (s2, e2) := p in
                                op Ms s1 s2 && op Me e1 e2)) 
                                (a, b) =>
                 let
                   (x, x0) as p
                    return
                      ((fun p0 : s * e =>
                        forall g : s * e,
                        (let (s1, e1) := p0 in
                         let (s2, e2) := g in op Ms s1 s2 && op Me e1 e2) =
                        (let (s1, e1) := g in
                         let (s2, e2) := p0 in op Ms s1 s2 && op Me e1 e2)) p) :=
                   _top_assumption_ in
                 _evar_0_ x x0)
                  (fun (s1 : s) (e1 : e) (__top_assumption_ : s * e) =>
                   (fun
                      _evar_0_ : forall (a : s) (b : e),
                                 (fun p : s * e =>
                                  (let (s2, e2) := p in
                                   op Ms s1 s2 && op Me e1 e2) =
                                  (let (s2, e2) := p in
                                   op Ms s2 s1 && op Me e2 e1)) 
                                   (a, b) =>
                    let
                      (x, x0) as p
                       return
                         ((fun p0 : s * e =>
                           (let (s2, e2) := p0 in op Ms s1 s2 && op Me e1 e2) =
                           (let (s2, e2) := p0 in op Ms s2 s1 && op Me e2 e1))
                            p) := __top_assumption_ in
                    _evar_0_ x x0)
                     (fun (s2 : s) (e2 : e) =>
                      (fun
                         _evar_0_ : op Ms s2 s1 && op Me e1 e2 =
                                    op Ms s2 s1 && op Me e2 e1 =>
                       eq_ind_r
                         (fun _pattern_value_ : bool =>
                          _pattern_value_ && op Me e1 e2 =
                          op Ms s2 s1 && op Me e2 e1) _evar_0_
                         (symmetricity Ms s1 s2))
                        ((fun
                            _evar_0_ : op Ms s2 s1 && op Me e2 e1 =
                                       op Ms s2 s1 && op Me e2 e1 =>
                          eq_ind_r
                            (fun _pattern_value_ : bool =>
                             op Ms s2 s1 && _pattern_value_ =
                             op Ms s2 s1 && op Me e2 e1) _evar_0_
                            (symmetricity Me e1 e2)) Logic.eq_refl)));
transitivity := fun _top_assumption_ : s * e =>
                (fun
                   _evar_0_ : forall (a : s) (b : e),
                              (fun p : s * e =>
                               forall g h : s * e,
                               (let (s1, e1) := p in
                                let (s2, e2) := g in
                                op Ms s1 s2 && op Me e1 e2) ->
                               (let (s1, e1) := g in
                                let (s2, e2) := h in
                                op Ms s1 s2 && op Me e1 e2) ->
                               let (s1, e1) := p in
                               let (s2, e2) := h in
                               op Ms s1 s2 && op Me e1 e2) 
                                (a, b) =>
                 let
                   (x, x0) as p
                    return
                      ((fun p0 : s * e =>
                        forall g h : s * e,
                        (let (s1, e1) := p0 in
                         let (s2, e2) := g in op Ms s1 s2 && op Me e1 e2) ->
                        (let (s1, e1) := g in
                         let (s2, e2) := h in op Ms s1 s2 && op Me e1 e2) ->
                        let (s1, e1) := p0 in
                        let (s2, e2) := h in op Ms s1 s2 && op Me e1 e2) p) :=
                   _top_assumption_ in
                 _evar_0_ x x0)
                  (fun (s1 : s) (e1 : e) (__top_assumption_ : s * e) =>
                   (fun
                      _evar_0_ : forall (a : s) (b : e),
                                 (fun p : s * e =>
                                  forall h : s * e,
                                  (let (s2, e2) := p in
                                   op Ms s1 s2 && op Me e1 e2) ->
                                  (let (s2, e2) := p in
                                   let (s3, e3) := h in
                                   op Ms s2 s3 && op Me e2 e3) ->
                                  let (s2, e2) := h in
                                  op Ms s1 s2 && op Me e1 e2) 
                                   (a, b) =>
                    let
                      (x, x0) as p
                       return
                         ((fun p0 : s * e =>
                           forall h : s * e,
                           (let (s2, e2) := p0 in op Ms s1 s2 && op Me e1 e2) ->
                           (let (s2, e2) := p0 in
                            let (s3, e3) := h in op Ms s2 s3 && op Me e2 e3) ->
                           let (s2, e2) := h in op Ms s1 s2 && op Me e1 e2) p) :=
                      __top_assumption_ in
                    _evar_0_ x x0)
                     (fun (s2 : s) (e2 : e) (__top_assumption_0 : s * e) =>
                      (fun
                         _evar_0_ : forall (a : s) (b : e),
                                    (fun p : s * e =>
                                     op Ms s1 s2 && op Me e1 e2 ->
                                     (let (s3, e3) := p in
                                      op Ms s2 s3 && op Me e2 e3) ->
                                     let (s3, e3) := p in
                                     op Ms s1 s3 && op Me e1 e3) 
                                      (a, b) =>
                       let
                         (x, x0) as p
                          return
                            ((fun p0 : s * e =>
                              op Ms s1 s2 && op Me e1 e2 ->
                              (let (s3, e3) := p0 in
                               op Ms s2 s3 && op Me e2 e3) ->
                              let (s3, e3) := p0 in
                              op Ms s1 s3 && op Me e1 e3) p) :=
                         __top_assumption_0 in
                       _evar_0_ x x0)
                        (fun (s3 : s) (e3 : e)
                           (_top_assumption_0 : op Ms s1 s2 && op Me e1 e2)
                         =>
                         (fun
                            _evar_0_ : forall (a : op Ms s1 s2)
                                         (b : op Me e1 e2),
                                       (fun _ : op Ms s1 s2 /\ op Me e1 e2 =>
                                        op Ms s2 s3 && op Me e2 e3 ->
                                        op Ms s1 s3 && op Me e1 e3)
                                         (conj a b) =>
                          match
                            elimTF andP _top_assumption_0 as a
                            return
                              ((fun _ : op Ms s1 s2 /\ op Me e1 e2 =>
                                op Ms s2 s3 && op Me e2 e3 ->
                                op Ms s1 s3 && op Me e1 e3) a)
                          with
                          | conj x x0 => _evar_0_ x x0
                          end)
                           (fun (Hs12 : op Ms s1 s2) 
                              (He12 : op Me e1 e2)
                              (_top_assumption_1 : 
                               op Ms s2 s3 && op Me e2 e3) =>
                            (fun
                               _evar_0_ : forall (a : op Ms s2 s3)
                                            (b : op Me e2 e3),
                                          (fun _ : op Ms s2 s3 /\ op Me e2 e3
                                           =>
                                           is_true
                                             (op Ms s1 s3 && op Me e1 e3))
                                            (conj a b) =>
                             match
                               elimTF andP _top_assumption_1 as a
                               return
                                 ((fun _ : op Ms s2 s3 /\ op Me e2 e3 =>
                                   is_true (op Ms s1 s3 && op Me e1 e3)) a)
                             with
                             | conj x x0 => _evar_0_ x x0
                             end)
                              (fun (Hs23 : op Ms s2 s3) (He23 : op Me e2 e3)
                               =>
                               (fun
                                  _evar_0_ : if true
                                             then op Ms s1 s3 /\ op Me e1 e3
                                             else
                                              ~ (op Ms s1 s3 /\ op Me e1 e3)
                                => introTF andP _evar_0_)
                                 (conj (transitivity Hs12 Hs23)
                                    (transitivity He12 He23)))))));
reflexivity := fun _top_assumption_ : s * e =>
               (fun
                  _evar_0_ : forall (a : s) (b : e),
                             (fun p : s * e =>
                              is_true
                                (let (s1, e1) := p in
                                 let (s2, e2) := p in
                                 op Ms s1 s2 && op Me e1 e2)) 
                               (a, b) =>
                let
                  (x, x0) as p
                   return
                     ((fun p0 : s * e =>
                       is_true
                         (let (s1, e1) := p0 in
                          let (s2, e2) := p0 in op Ms s1 s2 && op Me e1 e2))
                        p) := _top_assumption_ in
                _evar_0_ x x0)
                 (fun (s1 : s) (e1 : e) =>
                  (fun _evar_0_ : true && op Me e1 e1 =>
                   eq_ind_r
                     (fun _pattern_value_ : bool =>
                      _pattern_value_ && op Me e1 e1) _evar_0_
                     (reflexivity Ms s1))
                    ((fun _evar_0_ : true && true =>
                      eq_ind_r
                        (fun _pattern_value_ : bool =>
                         true && _pattern_value_) _evar_0_
                        (reflexivity Me e1)) is_true_true)) |}
     : forall s e : Type, mixin_of s -> mixin_of e -> mixin_of (s * e)

Arguments s, e are implicit
Argument scopes are [type_scope type_scope _ _]

(* move: (op Ms). *)
(* move: (op Me). *)
(* Check (fun a : nat * nat => let (t, _) := a in t). *)
(* Check  *)
(* (fun s' e' : s * e => *)
(*    let (s1, e1) := s' in *)
(*    let (s2, e2) := e' in *)
(*    op Ms s1 s2 && op Me e1 e2). *)
   
(*     _ _ => ) *)

              (fun _ _ => )).
              (fun _ _ => eqxx true) (fun _ _ _ _ x => x) (fun _ => eqxx true)).
Definition equivMixin_of_nat_prod s e : Equivalence.mixin_of (ordinal s * ordinal e)%type :=
  @Equivalence.Mixin _ (fun _ _ => true) (fun _ _ => eqxx true) (fun _ _ _ _ x => x) (fun _ => eqxx true).
End Equivalence.

(* locally small category *)
Module Category.
Structure category :=
  Category {
      objects : Type;
      morphisms : objects -> objects -> Type;
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

Local Notation "'Ob' C" := (objects C) (at level 1).
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
(* TODO: write about natural transformations. *)
(* TODO: write about adjunctions. *)

From mathcomp Require Import eqtype fintype seq finset ssrnat.

Example cat0 : category :=
  @Category unit
            (fun _ _ : unit => unit)
            (fun _ _ => Equivalence.equivMixin_of_unit)
            (fun _ _ _ _ _ => tt)
            (fun _ : unit => tt)
            (fun _ _ _ _ _ _ _ => eqxx true)
            (fun _ _ _ => eqxx true)
            (fun _ _ _ => eqxx true)
            (fun _ _ _ _ _ _ _ => eqxx true)
            (fun _ _ _ _ _ _ _ => eqxx true).

Definition omap s e :=
  (ordinal s * ordinal e)%type.

Definition square_base (x y : ordinal 4) :=
  match x, y with
  | Ordinal 0 _, Ordinal 1 _ => omap 0 1
  | Ordinal 1 _, Ordinal 2 _ => omap 1 2
  | Ordinal 3 _, Ordinal 2 _ => omap 3 2
  | Ordinal 4 _, Ordinal 3 _ => omap 4 3
  | Ordinal z _, Ordinal w _ => 
    if eqn z w
    then omap z z 
    else True
  end.

Definition equivMixin_of_square_base A B : Equivalence.mixin_of (square_base A B).
  case: A B => [m mH] [n nH].
  case: m n mH nH => [|m] [|n] mH nH /=.
  apply equivMixin
  rewrite /omap.

Example square : category.
Check (@Category (ordinal 4)
                  square_base
                  _ _ _ _ _ _ _ _).
refine (@Category (ordinal 4)
                  square_base
                  _ _ _ _ _ _ _ _).

move => D E F G h i j.
rewrite /=.




End Category.




Definition empty : Set := False -> False.
Example cat0 :=
  {| objectss := empty; morphisms:=(fun _ => empty) |}.
