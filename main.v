From mathcomp Require Import all_ssreflect.
Require Import equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Category.
(* locally small category *)
Section Axioms.
Variable objects : Type.
Variable morphisms : objects -> objects -> equivType.
Variable id : forall A, morphisms A A.
Variable comp : forall {A B C}, morphisms B C -> morphisms A B -> morphisms A C.
Local Notation "f '\comp' g" := (comp f g) (at level 40).
Local Notation "f == g" := (@equiv_op (morphisms _ _) f g).
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
End Axioms.
Polymorphic Structure mixin_of objects :=
  Mixin {
      morphisms : _;
      id: _;
      compm: _;
      associativity : @associativity_of_morphisms objects morphisms compm;
      right_idem : @identity_morphism_is_right_identity objects morphisms id compm;
      left_idem : @identity_morphism_is_left_identity objects morphisms id compm;
      comp_left : @compatibility_left objects morphisms compm;
      comp_right : @compatibility_right objects morphisms compm;
    }.

Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Polymorphic Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.
Module Exports.
Coercion sort : type >-> Sortclass.
Notation category := type.
Notation CatMixin := Mixin.
Notation CatType T m := (@pack T m).
Arguments id {objects m A}.
Notation id := (@Category.id _ (class _) _).
Notation morphisms := morphisms.
Notation compm := compm.
Notation compmA := associativity.
Notation right_idem := right_idem.
Notation left_idem := left_idem.
Notation comp_left := comp_left.
Notation comp_right := comp_right.
Arguments compm {objects m A B C} _ _.
Notation "f '\compm' g" := (compm f g) (at level 40).
Notation "'Ob' C" := (sort C) (at level 1).
Notation "'Mor' ( M , N )" := (@morphisms _ (class _) M N) (at level 5).
Notation "[ 'CatMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'CatMixin'  'of'  T ]") : form_scope.
Notation "[ 'category' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'category'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'category' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'category'  'of'  T ]") : form_scope.
End Exports.
End Category.
Export Category.Exports.

Local Notation "f == g" := (@equiv_op (@morphisms _ _ _ _) f g).
Lemma comp0m C (D E : Ob C) (f : Mor (D, E)) : f == id \compm f.
Proof. by apply left_idem. Qed.

Lemma compm0 C (D E : Ob C) (f : Mor (D, E)) : f == f \compm id.
Proof. by apply right_idem. Qed.

Lemma compm_comp c (A B C : Ob c) : @Congruence.compatible
                                      (Mor (B, C))
                                      (Mor (A, B))
                                      (Mor (A, C))
                                     compm.
Proof.
  move => f g h i H1 H2.
  apply: Equivalence.trans;
    first by apply comp_left, H2.
  by apply comp_right, H1.
Qed.
Local Notation subst_left := (Congruence.subst_left (@compm_comp _ _ _ _)).
Local Notation subst_right := (Congruence.subst_right (@compm_comp _ _ _ _)).

Hint Resolve comp0m compm0.

Module Functor.
Section Axioms.
Variables domain codomain : category.
Variable map_of_objects : Ob domain -> Ob codomain.
Variable map_of_morphisms : forall A B,
    Mor (A, B) -> Mor (map_of_objects A, map_of_objects B).
Local Definition maps_identity_to_identity :=
  forall A, @map_of_morphisms A A id == id.
Local Definition preserve_composition :=
  forall A B C (f : Mor (A, B)) (g : Mor (B, C)),
  map_of_morphisms (g \compm f) == map_of_morphisms g \compm (map_of_morphisms f).
Local Definition preserve_equivalence :=
  forall A B (f f' : Mor (A, B)),
    f == f' -> map_of_morphisms f == map_of_morphisms f'.
End Axioms.
Module Exports.
Structure functor dom cod :=
  Functor {
      map_of_objects : Ob dom -> Ob cod;
      map_of_morphisms : forall A B,
          Mor (A, B) -> Mor (map_of_objects A, map_of_objects B);
      id_id : @maps_identity_to_identity dom cod map_of_objects map_of_morphisms;
      pres_comp : @preserve_composition dom cod map_of_objects map_of_morphisms;
      pres_equiv : @preserve_equivalence dom cod map_of_objects map_of_morphisms;
    }.
Coercion map_of_objects : functor >-> Funclass.
Notation "'Fun' ( C , D )" := (functor C D).
Notation "' F " := (@map_of_morphisms _ _ F _ _) (at level 1).
Section Composition.
Variables (C D E : category) (G : Fun (D, E)) (F : Fun (C, D)).
Definition compfo x := G (F x).
Definition compfm A B (f : Mor (A, B)) := 'G ('F f).
Lemma compf_id_id : @maps_identity_to_identity _ _ compfo compfm.
Proof.
move=> ?.
apply: Congruence.etrans;
 last by apply: id_id.
by apply pres_equiv, id_id.
Defined.
Lemma compf_pres_comp : @preserve_composition _ _ compfo compfm.
Proof.
move=> ? ? ? ? ?.
apply: Congruence.etrans;
 last by apply: pres_comp.
by apply pres_equiv, pres_comp.
Defined.
Lemma compf_pres_equiv : @preserve_equivalence _ _ compfo compfm.
Proof.
move=>? ? ? ? ?;
 by do !apply: pres_equiv.
Defined.
Definition composition_of_functors :=
  @Functor _ _
          compfo
          compfm
          compf_id_id
          compf_pres_comp
          compf_pres_equiv.
End Composition.
Notation "F \compf G" := (composition_of_functors F G) (at level 40).
Section Identity.
Variables C : category.
Definition idfo := @id C.
Definition idfm (A B : Ob C) (f : Mor (A, B)) := f.
Lemma idf_id_id : @maps_identity_to_identity _ _ idfo idfm.
Proof. rewrite /= /idfm => ?. by apply/reflP. Defined.
Lemma idf_pres_comp : @preserve_composition _ _ idfo idfm.
Proof. rewrite /= /idfm => ?????. by apply/reflP. Defined.
Lemma idf_pres_equiv : @preserve_equivalence _ _ idfo idfm.
Proof. by rewrite /= /idfm => ?????. Defined.
Definition identity_of_functor :=
  @Functor _ _
          idfo
          idfm
          idf_id_id
          idf_pres_comp
          idf_pres_equiv.
End Identity.
Notation idf := identity_of_functor.
End Exports.
End Functor.
Export Functor.Exports.

Module NaturalTransformation.
Section Axioms.
Variables C D : category.
Variables F G : Fun (C, D).
Variable map : forall X, Mor (F(X), G(X)).
Arguments map {X}.
Local Definition naturality_axiom :=
  forall A A' (f : Mor (A, A')), map \compm 'F f == 'G f \compm map.
End Axioms.
Module Exports.
Structure natural_transformation {C D} (F G : Fun (C, D)) :=
  NaturalTransformation {
      natural_map :> _;
      naturality : @naturality_axiom C D F G natural_map;
    }.
Notation "'Nat' ( M , N )" := (natural_transformation M N) (at level 5).
Section Composition.
Variables C D : category.
Variables F G H : Fun (C, D).
Variables (N : Nat (F, G)) (M : Nat (G, H)).
Definition compn_map X := M X \compm N X.
Lemma compn_naturality : naturality_axiom compn_map.
Proof.
move => ? ? ?.
apply: Congruence.etrans;
 first by apply: compmA.
apply: Congruence.etrans;
  first (apply: subst_right; by apply: (naturality N)).
apply: Congruence.etrans;
 last by apply: compmA.
apply: Congruence.etrans;
  last (apply: subst_left; by apply: (naturality M)).
apply: Congruence.etrans;
 first (apply/symP; by apply: compmA).
by apply/reflP.
Defined.
Definition composition_of_natural_transformations :=
  @NaturalTransformation _ _ _ _ compn_map compn_naturality.
End Composition.
Notation "N \compn M" := (composition_of_natural_transformations N M)  (at level 40).
Section Identity.
Variables C D : category.
Variable F : Fun (C, D).
Definition idn_map X := @Category.id D (Category.class D) (F X).
Lemma idn_map_naturality : naturality_axiom idn_map.
Proof.
  rewrite /idn_map => ? ? ?.
  apply: Congruence.etrans;
    last by apply: right_idem.
  apply/symP; apply left_idem.
Defined.
Definition identity_natural_transformation :=
  @NaturalTransformation _ _ _ _ idn_map idn_map_naturality.
End Identity.
Notation idn := identity_natural_transformation.
Section Composition.
Variables C D E : category.
Variables F G : Fun (C, D).
Variables H : Fun (D, E).
Variables N : Nat (F, G).
Definition compfn_map X := 'H (N X).
Lemma compfn_naturality : @naturality_axiom C E (H \compf F) (H \compf G) compfn_map.
Proof.
move => ? ? ? /=.
apply: Congruence.etrans;
first (apply/symP; by apply pres_comp).
apply/symP.
apply: Congruence.etrans;
first (apply/symP; by apply pres_comp).
apply pres_equiv.
apply/symP; by apply naturality.
Defined.
Definition composition_of_natural_transformation_functor :=
  @NaturalTransformation C E (H \compf F) (H \compf G) compfn_map compfn_naturality.
End Composition.
Notation "F \compfn N" := (composition_of_natural_transformation_functor F N)  (at level 40).
Section Composition.
Variables C D E : category.
Variables F G : Fun (D, E).
Variables N : Nat (F, G).
Variables H : Fun (C, D).
Definition compnf_map X := N (H X).
Lemma compnf_naturality : @naturality_axiom C E (F \compf H) (G \compf H) compnf_map.
Proof.
move => ? ? ? /=.
apply: naturality.
Defined.
Definition composition_of_functor_natural_transformation :=
  @NaturalTransformation C E (F \compf H) (G \compf H) compnf_map compnf_naturality.
End Composition.
Notation "N \compnf F" := (composition_of_functor_natural_transformation N F)  (at level 40).
End Exports.
End NaturalTransformation.
Export NaturalTransformation.Exports.

Inductive isomorphisms {C} {A B: Ob C} (f : Mor (A, B)) (g : Mor (B, A)) : Prop :=
  Isomorphisms : (g \compm f) == id -> (f \compm g) == id -> isomorphisms f g.

Inductive natural_isomorphisms
          {C D} {F G : Fun (C, D)}
          (N : Nat (F, G)) (M : Nat (G, F)) : Prop :=
  NaturalIsomorphisms :
    (forall (X : Ob C), isomorphisms (N X) (M X)) -> 
    natural_isomorphisms N M.

Lemma ni_sym C D (F G : Fun (C, D)) (N : Nat (F, G)) (M : Nat (G, F)) :
  natural_isomorphisms N M <-> natural_isomorphisms M N.
Proof.
  split; case => H;
  apply: NaturalIsomorphisms => X;
  by case: (H X).
Defined.

Lemma ni_refl C D (F : Fun (C, D)) :
  natural_isomorphisms (@idn _ _ F) (@idn _ _ F).
Proof.
  apply: NaturalIsomorphisms => X.
  apply: Isomorphisms => /=;
  apply/symP; by apply left_idem.
Defined.

Lemma ni_trans C D (F G H : Fun (C, D))
      (N1 : Nat (F, G)) (M1 : Nat (G, F))
      (N2 : Nat (G, H)) (M2 : Nat (H, G)) :
  natural_isomorphisms N1 M1
  -> natural_isomorphisms N2 M2
  -> natural_isomorphisms (N1 \compn N2) (M2 \compn M1).
Proof.
  move=> [H1] [H2].
  apply: NaturalIsomorphisms => X.
  apply: Isomorphisms => /=;
  [ case: (H1 X) => HX _;
    case: (H2 X) => ? _
  | case: (H1 X) => _ ?;
    case: (H2 X) => _ HX ];
  (apply: Congruence.etrans;
   first (by apply: compmA));
  (apply/symP; apply: Congruence.etrans;
    first (by apply/symP; apply HX));
  apply: subst_right;
  (apply: Congruence.etrans; last (by apply: compmA));
  (apply: Congruence.etrans; first (by apply: left_idem));
  apply: subst_left; by apply/symP.
Defined.

Section CategoryOfCategories.
Definition is_there_nat_isom C D (F G : Fun (C, D)) :=
 exists (N : Nat (F, G)) (M : Nat (G, F)), natural_isomorphisms N M.
Section LocalArg.
Variables C D : category.
Local Notation itn := (@is_there_nat_isom C D).
Lemma itn_sym :
  Equivalence.symmetricity itn.
Proof.
  rewrite /itn => ? ?.
  split; move=> [N [M H]];
  do !apply: ex_intro;
  rewrite ni_sym; by apply: H.
Defined.

Lemma itn_refl :
  Equivalence.reflexivity itn.
Proof.
  rewrite /itn => ?.
  do !apply: ex_intro.
  exact: ni_refl.
Defined.

Lemma itn_trans :
  Equivalence.transitivity itn.
Proof.
  rewrite /itn => ? ? ?.
  move => [N1 [M1 H1]] [N2 [M2 H2]].
  do !apply: ex_intro.
  apply ni_trans; first (by apply H1);
  by apply H2.
Defined.

Definition itn_equivMixin := EquivMixin itn_sym itn_trans itn_refl.
Canonical itn_equivType := Eval hnf in EquivType (Fun (C, D)) itn_equivMixin.
End LocalArg.

Lemma cats_associativity : @Category.associativity_of_morphisms category _ composition_of_functors.
Proof.
  move => /= C D E F h i j.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ ((j \compf i) \compf h) (j \compf (i \compf h)) (natural_map (idn _)) (idn_map_naturality _))
                              (@NaturalTransformation _ _ (j \compf (i \compf h)) ((j \compf i) \compf h) (natural_map (idn _)) (idn_map_naturality _))).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.

Lemma cats_right_idem : @Category.identity_morphism_is_right_identity category _ idf composition_of_functors.
Proof.
  move => /= C D f.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ f (f \compf idf _) (natural_map (idn _)) (idn_map_naturality _))
                              (@NaturalTransformation _ _ (f \compf idf _) f (natural_map (idn _)) (idn_map_naturality _))).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.

Lemma cats_left_idem : @Category.identity_morphism_is_left_identity category _ idf composition_of_functors.
Proof.
  move => /= C D f.
  do !apply: ex_intro.
  apply (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ f (idf _ \compf f) (natural_map (idn _)) (idn_map_naturality _))
                              (@NaturalTransformation _ _ (idf _ \compf f) f (natural_map (idn _)) (idn_map_naturality _))).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: compm0.
Defined.

Lemma cats_comp_left : @Category.compatibility_left category _ composition_of_functors.
Proof.
  move => ? ? ? f f' g /= [] N [] M [H].
  do !apply: ex_intro.
  refine (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ (g \compf f) (g \compf f')
                                                      (natural_map (g \compfn N)) (compfn_naturality _ _))
                              (@NaturalTransformation _ _ (g \compf f') (g \compf f) 
                                                      (natural_map (g \compfn M)) (compfn_naturality _ _)) _) => X.
  apply: Isomorphisms => /=;
  (apply: Congruence.etrans;
   first by (apply/symP; apply pres_comp));
  (apply: Congruence.etrans;last by apply id_id);
  apply: pres_equiv; by case: (H X).
Defined.

Lemma cats_comp_right : @Category.compatibility_right category _ composition_of_functors.
Proof.
  move => ? ? ? f g g' /= [] N [] M [H].
  do !apply: ex_intro.
  refine (@NaturalIsomorphisms _ _ _ _
                              (@NaturalTransformation _ _ (g \compf f) (g' \compf f)
                                                      (natural_map (N \compnf f)) (compnf_naturality _ _))
                              (@NaturalTransformation _ _ (g' \compf f) (g \compf f)
                                                      (natural_map (M \compnf f)) (compnf_naturality _ _)) _) => X.
  apply: Isomorphisms => /=;
  by case: (H (f X)).
Defined.

Definition cats_catMixin := CatMixin cats_associativity cats_right_idem cats_left_idem cats_comp_left cats_comp_right.
Canonical cats_catType := Eval hnf in CatType category cats_catMixin.
Notation cats := cats_catType.
End CategoryOfCategories.

Section Pushout.
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
End Pushout.

(* TODO: write about natural transformations. *)
(* TODO: write about adjunctions. *)

(* Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2. *)

(* Lemma congr_up_to_equals *)
(*       {C : category} *)
(*       (D E F G : Ob C) *)
(*       (f : Mor (D, E)) *)
(*       (f' : Mor (D, F)) *)
(*       (g : Mor (E, G)) *)
(*       (g' : Mor (F, G)) *)
(*       (h : Mor (E, F)) (i : Mor (F, E)) (I : isomorphisms h i) : *)
(*   h \comp f == f' -> *)
(*   g == g' \comp h -> *)
(*   g \comp f == g' \comp f'. *)
(* Proof. *)
(*   move => H1 H2. *)
(*   case: I => lid rid. *)
(*   have: g' \comp (h \comp f) == g' \comp f'. *)
(*   rewrite subst_right_up_to_equals; last first. *)
(*   apply Equivalence.symmetricity. *)
(*   apply: H1. *)
(*   exact: Equivalence.reflexivity. *)
(*   apply:  *)
(*   auto. *)
(*   info_auto. *)
(*   eauto. *)
  
  
(*   g \comp  *)
(*   Check (g' \comp h \comp i \comp f'). *)
(*   have (g' \comp (h \comp f)) == g' \comp h \comp i \comp f'. *)
(*   have : g \comp i \comp h \comp f == g' \comp h \comp i \comp f'. *)
(*   apply transitivity_lhs. *)
(*   rewrite -comp0m. *)
(*   About identity_morphism_is_right_identity. *)
(*   rewrite -identity_morphism_is_right_identity. *)
(*   rewrite subst_right_up_to_equals; last first. *)
(*   apply Equivalence.symmetricity. *)
(*   apply H1. *)
(*   rewrite subst_left_up_to_equals; last first. *)
(*   apply Equivalence.symmetricity; apply H2. *)
(*   by apply: Equivalence.reflexivity. *)
(* Qed. *)

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