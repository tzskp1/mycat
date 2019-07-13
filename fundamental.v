From mathcomp Require Import all_ssreflect.
Require Import equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Local Notation "f == g" := (@equiv_op _ f g).

Inductive pairing@{m p} (S T : Type@{m}) (P : S -> T -> Type@{p}) : Type@{p} :=
  Pairing : forall f g, P f g -> pairing P.
Arguments pairing {_ _} _.
Arguments Pairing {_ _ _} _ _.
Notation "p '.1'" := match p with
                     | Pairing f _ _ => f
                     end.
Notation "p '.2'" := match p with
                     | Pairing _ f _ => f
                     end.

Section Pairing.
Variables S T : equivType.
Definition pairing_op P (f g : @pairing S T P) :=
  prod (f.1 == g.1) (f.2 == g.2).
Lemma pairing_reflP P : Equivalence.reflexivity (@pairing_op P).
Proof. move=> [A B h]. by apply: pair; apply/reflP. Qed.

Lemma pairing_symP P : Equivalence.symmetricity (@pairing_op P).
Proof. move=> [hA hB h] [jA jB j] [H1 H2]; by apply: pair; apply/symP. Qed.

Lemma pairing_transP P : Equivalence.transitivity (@pairing_op P).
Proof.
move=> [hA hB h] [jA jB j] [iA iB i] [H1 H2] [H'1 H'2].
apply: pair.
 by apply/transP; first apply: H1.
by apply/transP; first apply: H2.
Qed.
Definition pairing_equivMixin P := EquivMixin (@pairing_symP P) (@pairing_transP P) (@pairing_reflP P).
End Pairing.

Notation "'#' f" := (fun g => comp g f) (at level 3).
Notation "f '#'" := (fun g => comp f g) (at level 3).

Module Category.
Section Axioms.
Universe u.
Variable objects : Type@{u}.
Variable morphisms : objects -> objects -> Type@{u}.
Variable id : forall A, morphisms A A.
Variable comp : forall A B C,
    morphisms B C -> morphisms A B -> morphisms A C.
Variable cat_equivMixin: forall A B, Equivalence.mixin_of (morphisms A B).
Local Notation "f '\comp' g" := (comp f g) (at level 40).
Local Notation "f == g" := (@equiv_op@{u} (EquivType@{u} _ (cat_equivMixin _ _)) f g).

Definition associativity_of_morphisms :=
  forall D E F G
         (h : morphisms D E)
         (i : morphisms E F)
         (j : morphisms F G),
  (j \comp i) \comp h == j \comp (i \comp h).
Definition identity_morphism_is_right_identity :=
  forall A B (f : morphisms A B), f == f \comp id A.
Definition identity_morphism_is_left_identity :=
  forall A B (f : morphisms A B), f == id B \comp f.
Definition compatibility_left :=
  forall D E F (f f': morphisms D E) (g : morphisms E F),
  f == f' -> g \comp f == g \comp f'.
Definition compatibility_right :=
  forall D E F (f : morphisms D E) (g g' : morphisms E F),
  g == g' -> g \comp f == g' \comp f.
End Axioms.

Structure mixin_of@{u} (objects : Type@{u}) :=
  Mixin {
      morphisms; id; compm; equiv;
      compmA: @associativity_of_morphisms@{u} objects morphisms compm equiv;
      compm0 : @identity_morphism_is_right_identity@{u} objects morphisms id compm equiv;
      comp0m : @identity_morphism_is_left_identity@{u} objects morphisms id compm equiv;
      comp_left : @compatibility_left@{u} objects morphisms compm equiv;
      comp_right : @compatibility_right@{u} objects morphisms compm equiv;
    }.

Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type@{u} := Pack {sort; _ : class_of@{u} sort; _ : Type@{u}}.
Universe u.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type@{u}) (cT : type@{u}).
Definition class := let: Pack _ c _ := cT return class_of@{u} cT in c.
Definition pack c := @Pack@{u} T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.
End ClassDef.

Module Notations.
Coercion sort : type >-> Sortclass.
Notation category := type.
Notation CatMixin := Mixin.
Notation CatType T m := (@pack T m).
Arguments id {objects m} A.
Notation id := (@Category.id _ (class _) _).
Notation "'Mor' ( M , N )" := (@morphisms _ (class _) M N) (at level 5).
Definition morph C := @morphisms (sort C) (class C).
Arguments morph _ _ _ : clear implicits.
Notation compm := compm.
Arguments compm {_ _ A B C} _ _: simpl never.
Notation equiv C := (equiv (class C)).
Notation compmA := compmA.
Notation compm0 := compm0.
Notation comp0m := comp0m.
Notation comp_left := comp_left.
Notation comp_right := comp_right.
Notation "f '\compm' g" := (compm f g) (at level 40).
Notation "'Ob' C" := (sort C) (at level 1).
Notation "[ 'CatMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'CatMixin'  'of'  T ]") : form_scope.
Notation "[ 'category' 'of' T 'for' C ]" := (@clone T C _ idfun (fun x => x))
  (at level 0, format "[ 'category'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'category' 'of' T ]" := (@clone T _ _ (fun x => x) (fun x => x))
  (at level 0, format "[ 'category'  'of'  T ]") : form_scope.
End Notations.

Module Equivalence.
Import Notations.
Module PartialEquiv.
Canonical partial_equivType T (C : mixin_of T) (A B : T) :=
  Eval hnf in EquivType _ (Category.equiv C A B).
End PartialEquiv.
Import PartialEquiv.
Lemma compm_comp c (A B C : Ob c) : @Congruence.compatible
                                      (EquivType (Mor (_, _)) (Category.equiv _ B C))
                                      (EquivType (Mor (_, _)) (Category.equiv _ A B))
                                      (EquivType (Mor (_, _)) (Category.equiv _ A C))
                                      compm.
Proof.
  move => f g h i H1 H2.
  apply: Equivalence.trans;
    first by apply comp_left, H2.
  by apply comp_right, H1.
Defined.
Notation subst_left := (Congruence.subst_left (@compm_comp _ _ _ _)).
Notation subst_right := (Congruence.subst_right (@compm_comp _ _ _ _)).
Lemma identity_morphism_is_the_unique (C : category) (A : Ob C) (id' : Mor (A, A)) :
  (forall B (f : Mor (A, B)), (f \compm id') == f) -> id' == Category.id A.
Proof.
move => H.
apply: Congruence.etrans; last by apply H.
apply comp0m.
Defined.

Section trivials.
Lemma compmKK C (a b c : Ob C)
(f : Mor (a, b)) (g : Mor (b, c))
(h : Mor (c, b)) (i : Mor (b, a)) :
 h \compm g == id ->
 i \compm f == id ->
 (i \compm h) \compm (g \compm f) == id.
Proof.
move=> H1 H2.
apply: Congruence.etrans; first apply compmA.
apply: Congruence.etrans; last apply H2.
apply subst_right.
apply/symP; apply: Congruence.etrans; last apply compmA.
apply: Congruence.etrans; first apply comp0m.
apply subst_left; by apply/symP.
Defined.

Lemma compm00m C (a b : Ob C) (f : Mor (a, b)) : f \compm id == id \compm f.
Proof.
apply: Congruence.etrans; last apply comp0m.
apply/symP; apply compm0.
Defined.
Lemma equiv_mm C (a b : Ob C) (f : Mor (a, b)) : f == f.
Proof. apply/reflP. Defined.
Lemma comp0mt C (a b : Ob C) (f : Mor (a, b)) : f == id \compm f.
apply comp0m. Defined.
Lemma compm0t C (a b : Ob C) (f : Mor (a, b)) : f == f \compm id.
apply compm0. Defined.
End trivials.

Section Isomorphism.
Inductive isomorphisms@{u} (C : category@{u}) (A B: Ob C) (f : Mor (A, B)) (g : Mor (B, A)) : Type@{u} :=
  Isomorphisms : (g \compm f) == id -> (f \compm g) == id -> isomorphisms f g.
Arguments isomorphisms {_ _ _} _ _.
Arguments Isomorphisms {_ _ _} _ _ _ _.

Universe u.
Variable C : category@{u}.
Local Notation piso :=
  (fun A B => pairing (@isomorphisms C A B)).
Lemma piso_sym : Equivalence.symmetricity piso.
Proof.
move=> ? ? [N M] [H1 H2];
apply (@Pairing _ _ _ M N);
by constructor.
Defined.

Lemma piso_refl : Equivalence.reflexivity piso.
Proof.
move => ?; apply (Pairing id id).
by constructor; apply/symP; apply comp0m.
Defined.

Lemma piso_trans : Equivalence.transitivity piso.
Proof.
move => ? ? ?.
move => [f1 g1] [H11 H12] [f2 g2] [H21 H22].
apply (Pairing (f2 \compm f1) (g1 \compm g2)).
constructor; by apply compmKK.
Defined.
Definition obs_equivMixin := EquivMixin@{u} piso_sym piso_trans piso_refl.
Definition obs_equivType := Eval hnf in EquivType@{u} (Ob C) obs_equivMixin.
End Isomorphism.
End Equivalence.

Module Exports.
Include Notations.
Include Equivalence.
Hint Resolve equiv_mm compm00m comp0mt compm0t.
End Exports.
End Category.
Export Category.Exports.

Module Functor.
Section Axioms.
Universes u u'.
Import PartialEquiv.
Variable domain : category@{u}.
Variables codomain : category@{u'}.
Variable map_of_objects : Ob domain -> Ob codomain.
Variable map_of_morphisms :
  forall A B, Mor(A, B) -> Mor(map_of_objects A, map_of_objects B).
Definition maps_identity_to_identity :=
  forall A, @map_of_morphisms A A (Category.id A) == (Category.id (map_of_objects A)).
Definition preserve_composition :=
  forall A B C (f : Mor(A, B)) (g : Mor(B, C)),
  map_of_morphisms (g \compm f) == map_of_morphisms g \compm (map_of_morphisms f).
Definition preserve_equivalence :=
  forall A B (f f' : Mor(A, B)),
    f == f' -> map_of_morphisms f == map_of_morphisms f'.
End Axioms.

Structure mixin_of@{u u'}
          (dom : category@{u})
          (cod : category@{u'}) map_of_objects :=
  Mixin {
      map_of_morphisms;
      id_id : @maps_identity_to_identity dom cod map_of_objects map_of_morphisms;
      pres_comp : @preserve_composition dom cod map_of_objects map_of_morphisms;
      pres_equiv : @preserve_equivalence dom cod map_of_objects map_of_morphisms;
    }.
Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Structure type@{u u'} dom cod :=
  Pack { map; _: @class_of@{u u'} dom cod map; _: Type@{u}; _: Type@{u'} }.
Universes u u'.
Variables (domT : category@{u})
          (codT : category@{u'})
          (cT : @type domT codT)
          (mapT : Ob domT -> Ob codT).
Definition class := let: Pack _ c _ _ := cT return @class_of@{u u'} _ _ (map cT) in c.
Definition pack c := @Pack domT codT mapT c (Ob domT) (Ob codT).
Definition clone (c : mixin_of mapT) (_ : phant_id (pack c) cT) := pack c.
End ClassDef.

Module Notations.
Definition app_fun_mor (dom cod : category) (f : type dom cod) :=
  @map_of_morphisms _ _ _ (class f).
Arguments app_fun_mor /.
Notation "' F" := (@app_fun_mor _ _ F _ _) (at level 1).
Coercion map: type >-> Funclass.
Notation functor := type.
Notation FunMixin := Mixin.
Notation FunType C D m := (@pack C D _ m).
Notation id_id := (id_id (class _)).
Notation pres_comp := (pres_comp (class _)).
Notation pres_equiv := (pres_equiv (class _)).
Notation "'Fun' ( C , D )" := (@type C D).
End Notations.

Module Composition.
Import Notations.
Section compf.
Variables (C D E : category) (G : Fun (D, E)) (F : Fun (C, D)).
Definition compfm A B (f : Mor(A, B)) : Mor((G \o F) A, (G \o F) B) := 'G ('F f).
Lemma compf_id_id : maps_identity_to_identity compfm.
Proof.
move=> ?.
apply: Congruence.etrans;
 last by apply: id_id.
by apply pres_equiv, id_id.
Defined.
Lemma compf_pres_comp : preserve_composition compfm.
Proof.
move=> ? ? ? ? ?.
apply: Congruence.etrans;
 last by apply: pres_comp.
by apply pres_equiv, pres_comp.
Defined.
Lemma compf_pres_equiv : preserve_equivalence compfm.
Proof.
move=>? ? ? ? ?;
 by do !apply: pres_equiv.
Defined.
Definition compf_Mixin :=
  FunMixin compf_id_id compf_pres_comp compf_pres_equiv.
Definition compf := FunType _ _ compf_Mixin.
End compf.
Section trivials.
Variables C D : category. 
Variable F : Fun (C, D).
Import PartialEquiv.
Lemma compf0m a b (f : Mor (a, F b))
  : f == Functor.map_of_morphisms (Functor.class F) id \compm f.
Proof.
apply: Congruence.etrans; last first.
 apply: subst_left.
 apply/symP; apply: id_id.
apply comp0m.
Defined.
Lemma compmf0 a b (f : Mor (F a, b))
  : f == f \compm Functor.map_of_morphisms (Functor.class F) id.
Proof.
apply: Congruence.etrans; last first.
 apply: subst_right;
 apply/symP; apply: id_id.
apply compm0.
Defined.
End trivials.
Notation "F \compf G" := (compf F G) (at level 40).
End Composition.

Module Identity.
Import Notations.
Section idf.
Variable C : category.
Definition idfm (A B : Ob C) (f : Mor (A, B)) := f.
Definition idf_id_id := (fun _  => reflP) : maps_identity_to_identity idfm.
Definition idf_pres_comp := (fun _ _ _ _ _ => reflP) : preserve_composition idfm.
Definition idf_pres_equiv := (fun _ _ _ _ => (fun x => x)) : preserve_equivalence idfm.
Definition idf_Mixin := FunMixin idf_id_id idf_pres_comp idf_pres_equiv.
Definition idf := FunType _ _ idf_Mixin.
End idf.
End Identity.

Module Exports.
Include Notations.
Include Composition.
Include Identity.
Hint Resolve compf0m compmf0.
End Exports.
End Functor.
Export Functor.Exports.

Module NaturalTransformation.
Import PartialEquiv.
Section Axioms.
Universes u u'.
Variable C : category@{u}.
Variable D : category@{u'}.
Variable Fo Go : Ob C -> Ob D.
Variable Fm : forall A B, Mor (A, B) -> Mor (Fo A, Fo B).
Variable Gm : forall A B, Mor (A, B) -> Mor (Go A, Go B).
Variable map : forall X, Mor (Fo X, Go X).
Arguments map {X}.
Definition naturality_axiom :=
  forall A A' (f : Mor (A, A')), map \compm Fm f == Gm f \compm map.
End Axioms.

Structure mixin_of@{u u'} (C : category@{u}) (D : category@{u'}) Fo Go Fm Gm natural_map :=
  Mixin { naturality : @naturality_axiom C D Fo Go Fm Gm natural_map }.

Local Notation class_of := mixin_of (only parsing).

Definition axiom C D (F G : Fun(C, D))
           (map : forall X, Mor(F X, G X)) :=
  forall (A A' : Ob C) (f : Mor (A, A')),
    map _ \compm 'F f == 'G f \compm map _.

Section ClassDef.
Universes u u'.
Variable dom : category@{u}.
Variable cod : category@{u'}.
Structure type domfo codfo domfm codfm := Pack { map; _ : @class_of@{u u'} dom cod domfo codfo domfm codfm map; _ : Type@{u'} }.
Variables (domfT codfT : functor@{u u'} dom cod)
          (cT : @type (Functor.map domfT) (Functor.map codfT) (fun _ _ => 'domfT) (fun _ _ => 'codfT))
          (mapT : forall X , Mor(domfT X, codfT X)).
Definition class := let: Pack _ c _ := cT return @class_of dom cod
                                                           (Functor.map domfT) (Functor.map codfT)
                                                           (fun _ _ => 'domfT) (fun _ _ => 'codfT)
                                                           (map cT) in c.
Definition pack c := @Pack _ _ (fun _ _ => 'domfT) (fun _ _ => 'codfT) mapT c (forall X, Mor(domfT X, codfT X)).
End ClassDef.

Module Notations.
Coercion map : type >-> Funclass.
Notation natural_transformation F G := (type (fun _ _ => 'F) (fun _ _ => 'G)).
Notation "'Nat' ( M , N )" := (natural_transformation M N) (at level 5).
Notation NatMixin := Mixin.
Notation NatType F G m := (@pack _ _ F G _ m).
Definition naturality' C D F G N :=
  @naturality C D _ _ (fun _ _ => 'F) (fun _ _ => 'G) _ (class N).
Notation naturality :=  naturality'.
Notation "[ 'NatMixin' 'of' T 'to' S ]" := (class _ : @mixin_of _ _ T S)
  (at level 0, format "[ 'NatMixin'  'of'  T 'to' S ]") : form_scope.
End Notations.

Module Identity.
Import Notations.
Section idn.
Universes u u'.
Variable C : category@{u}.
Variable D : category@{u'}.
Variable F : functor@{u u'} C D.
Definition idn_map X := @Category.id@{u'} _ (Category.class D) (F X).
Lemma idn_map_naturality : axiom idn_map.
move=> ? ? ? /=.
apply: Congruence.etrans; last apply: compm0.
by apply/symP; apply: comp0m.
Defined.
Definition idn := NatType F F (NatMixin@{u u'} idn_map_naturality).
End idn.
End Identity.

Module Composition.
Import Notations.
Section compn.
Universes u u'.
Variable C : category@{u}.
Variable D : category@{u'}.
Variables F G H : functor@{u u'} C D.
Variable M : natural_transformation@{u u'} G H.
Variable N : natural_transformation@{u u'} F G.
Definition compn_map X := M X \compm N X.
Lemma compn_naturality : axiom compn_map.
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
Definition compn := NatType _ _ (NatMixin compn_naturality).
End compn.
Notation "N \compn M" := (compn N M)  (at level 40).

Section compfn.
Import Notations.
Universes u u' u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Variable E : category@{u''}.
Variable F G : functor@{u u'} C D.
Variable H : functor@{u' u''} D E.
Variable N : natural_transformation@{u u'} F G.
Definition compfn_map X := 'H (N X).
Lemma compfn_naturality : @axiom C E (H \compf F) (H \compf G) compfn_map.
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
Definition compfn :=
  NatType _ _ (NatMixin compfn_naturality).
End compfn.
Notation "F \compfn N" := (compfn F N) (at level 40).

Section compnf.
Universes u u' u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Variable E : category@{u''}.
Variable F G : functor@{u' u''} D E.
Variable N : natural_transformation@{u' u''} F G.
Variable H : functor@{u u'} C D.
Definition compnf_map X := N (H X).
Lemma compnf_naturality : @axiom C E (F \compf H) (G \compf H) compnf_map.
Proof.
move => ? ? ? /=.
apply: naturality.
Defined.
Definition compnf :=
  NatType _ _ (NatMixin compnf_naturality).
End compnf.
Notation "N \compnf F" := (compnf N F)  (at level 40).
End Composition.

Module Exports.
Include Notations.
Include Identity.
Include Composition.
End Exports.
End NaturalTransformation.
Export NaturalTransformation.Exports.

Section Funs.
Section Isomorphism.
Universes u u' u''.
Constraint u <= u''.
Constraint u' <= u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Variables F G : functor@{u u'} C D.
Import PartialEquiv.
Local Notation fniso :=
  (fun (N M : natural_transformation@{u u'} F G)
   => forall X, N X == M X).
Lemma fniso_sym : Equivalence.symmetricity@{u''} fniso.
Proof. move => ? ? ? ?. by apply/symP. Defined.

Lemma fniso_refl : Equivalence.reflexivity@{u''} fniso.
Proof. move => ? ?. by apply/reflP. Defined.

Lemma fniso_trans : Equivalence.transitivity@{u''} fniso.
Proof. move => ? ? ? H ? ?. by (apply/transP; first by apply: H). Defined.
Definition nats_equivMixin := Eval hnf in EquivMixin@{u''} fniso_sym fniso_trans fniso_refl.
Definition nats_equivType := Eval hnf in EquivType@{u''} (natural_transformation@{u u'} F G) nats_equivMixin.
End Isomorphism.

Universes u u' u''.
Constraint u <= u''.
Constraint u' <= u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Lemma funs_compmA : @Category.associativity_of_morphisms@{u''} _ _ (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof. move => C' D' E F h i j X /=. apply compmA. Defined.

Lemma funs_compm0 : @Category.identity_morphism_is_right_identity@{u''} _ _ (@idn C D) (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof. move => C' D' f X. apply compm0. Defined.

Lemma funs_comp0m : @Category.identity_morphism_is_left_identity@{u''} _ _ (@idn C D) (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof. move => C' D' f X. apply comp0m. Defined.

Lemma funs_comp_left : @Category.compatibility_left@{u''} _ _ (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_left.
  rewrite /=.
  move: f f' H => [f ? ?] [f' ? ?] H.
  apply H.
Defined.

Lemma funs_comp_right : @Category.compatibility_right@{u''} _ _ (@compn C D) (@nats_equivMixin@{u u' u''} C D).
Proof.
  move => ? ? ? f f' g /= H X.
  apply comp_right.
  move: f f' H => [f ? ?] [f' ? ?] H.
  apply H.
Defined.
Canonical funs_catMixin := CatMixin@{u''} funs_compmA funs_compm0 funs_comp0m funs_comp_left funs_comp_right.
Canonical funs := Eval hnf in CatType@{u''} (functor@{u u'} C D) funs_catMixin.
Canonical funs_obs_equivType := Eval hnf in EquivType@{u''} (functor@{u u'} C D) (obs_equivMixin funs).
End Funs.
Notation "'Fun' ( C , D )" := (funs C D).

Section Cats.
Universes u u' u'' u'''.
Constraint u <= u'''.
Constraint u' <= u'''.
Constraint u'' <= u'''.
Import PartialEquiv.
Definition funs_equivMixin C D := obs_equivMixin (funs C D).
Lemma cats_compmA : @Category.associativity_of_morphisms@{u'''} _ _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => /= C D E F h i j.
  apply: (Pairing 
           (NatType _ _ (@NatMixin _ _ ((j \compf i) \compf h) (j \compf (i \compf h)) _ _ (fun _ => id) (@idn_map_naturality _ _ _)))
           (NatType _ _ (@NatMixin _ _ (j \compf (i \compf h)) ((j \compf i) \compf h) _ _ (fun _ => id) (@idn_map_naturality _ _ _)))).
  apply: Isomorphisms => X;
  apply/symP; by apply: comp0m.
Defined.

Lemma compf0 C D (f : Fun (C, D)) :
  f == f \compf idf _.
Proof.
set L := NatType _ _ (@NatMixin _ _ f (f \compf idf _) _ _ (idn _) (idn_map_naturality _)).
set R := NatType _ _ (@NatMixin _ _ (f \compf idf _) f _ _ (idn _) (idn_map_naturality _)).
apply: (Pairing L R);
apply: Isomorphisms => X /=;
apply/symP; by apply: comp0m.
Defined.

Lemma comp0f C D (f : Fun (C, D)) :
  f == idf _ \compf f.
Proof.
set L := NatType _ _ (@NatMixin _ _ f (f \compf idf _) _ _ (idn _) (idn_map_naturality _)).
set R := NatType _ _ (@NatMixin _ _ (f \compf idf _) f _ _ (idn _) (idn_map_naturality _)).
apply: (Pairing L R);
apply: Isomorphisms => X /=;
apply/symP; by apply: comp0m.
Defined.

Lemma cats_compm0 : @Category.identity_morphism_is_right_identity@{u'''} category _ idf compf@{u u' u''} funs_equivMixin.
Proof. move=> C D f. apply compf0. Defined.

Lemma cats_comp0m : @Category.identity_morphism_is_left_identity@{u'''} category _ idf compf@{u u' u''} funs_equivMixin.
Proof. move=> C D f. apply comp0f. Defined.

Lemma compfnD C E F
  (f f' : Fun (C, E))
  (g : Fun (E, F))
  (N : Mor (f, f'))
  (M : Mor (f', f)) :
  forall X, ((g \compfn M) \compn (g \compfn N)) X == (g \compfn (M \compn N)) X.
Proof.
  move=> x /=.
  apply: Congruence.etrans.
  apply/symP; apply: pres_comp.
  apply/reflP.
Defined.

Lemma cats_comp_left : @Category.compatibility_left@{u'''} category _ compf@{u u' u''} funs_equivMixin.
Proof.
move => C ? ? f f' g [N M [H1 H2]].
apply: (Pairing (g \compfn N) (g \compfn M)).
apply: Isomorphisms => X; move: (H1 X) (H2 X) => H1' H2';
 (apply: Congruence.etrans; first apply compfnD);
 (apply: Congruence.etrans; last by apply id_id);
 apply: pres_equiv;
 by apply: Congruence.etrans; last (apply/symP; apply id_id).
Defined.

Lemma compnfD C E F
  (f : Fun (C, E))
  (g g' : Fun (E, F))
  (N : Mor (g, g'))
  (M : Mor (g', g)) :
  forall X, ((M \compnf f) \compn (N \compnf f)) X == (M \compn N) (f X).
Proof. move=> x; by apply/reflP. Defined.

Lemma cats_comp_right : @Category.compatibility_right@{u'''} category _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => ? ? ? f g g' [N M] [H1 H2].
  apply: (Pairing (N \compnf f) (M \compnf f)).
  apply: Isomorphisms => X.
  apply: Congruence.etrans; first apply: compnfD.
   by apply: (H1 (f X)).
  by apply: (H2 (f X)).
Defined.
Canonical cats_catMixin := Eval hnf in CatMixin cats_compmA cats_compm0 cats_comp0m cats_comp_left cats_comp_right.
Canonical cats := Eval hnf in CatType@{u'''} category cats_catMixin.
Canonical cats_obs_equivType := Eval hnf in EquivType category (obs_equivMixin cats).
Canonical obs_equivType.
End Cats.

Section funaltE.
Import PartialEquiv.
Variables C D : category.
Variables F G : Fun (C, D).
Variable Ho : forall A, F A == G A.
Variable Hm : forall X Y (f : Mor (X, Y)), (Ho Y).1 \compm 'F f \compm (Ho X).2 == 'G f.
Local Definition La : NaturalTransformation.axiom (fun X => (Ho X).1) :=
fun A A' f => 
transP
(transP (transP (compm0 ((Ho A').1 \compm ' F f))
        (subst_right match Ho A as p return (id == p.2 \compm p.1) with
                     | Pairing L R (Isomorphisms H _) => symP H
                     end))
(symP (compmA (Ho A).1 (Ho A).2 ((Ho A').1 \compm Functor.map_of_morphisms (Functor.class F) f))))
(subst_left (Hm f)).

Local Definition Ra : NaturalTransformation.axiom (fun X => (Ho X).2) :=
fun A A' f =>
transP (subst_right (symP (Hm f)))
(transP (symP (compmA (Ho A).2 ((Ho A').1 \compm ' F f) (Ho A').2))
(transP (subst_left (symP (compmA (' F f) (Ho A').1 (Ho A').2)))
(transP (subst_left (subst_left match Ho A' as p return (p.2 \compm p.1 == id) with
                                | Pairing L R (Isomorphisms H _) => H
                                end))
(transP (compmA (Ho A).2 (' F f) id) (symP (comp0m (' F f \compm (Ho A).2))))))).

Lemma funaltE : F == G.
apply: (Pairing
          (NatType _ _ (NatMixin La))
          (NatType _ _ (NatMixin Ra))).
apply: Isomorphisms=> X;
compute; by case: (Ho X) => ? ? [].
Defined.
End funaltE.
Arguments funaltE {C D F G} Ho Hm.

(* universe cancel functors *)
Module Down.
Section Down.
Universes t u.
Constraint t < u.
Definition down (C : category@{t}) : category@{u}.
case: C => c m _.
apply (@Category.Pack@{u} c) => //.
case: m => mo mm cm ce ca ir il cl cr.
set ce' := (fun a b => Equivalence.down@{t u} (ce a b)).
apply (@Category.Mixin@{u} c mo mm cm ce').
+ move=> a b e f h i j.
  move: (ca a b e f h i j).
  by rewrite !equivE Equivalence.downK.
+ move=> a b f.
  move: (ir a b f).
  by rewrite !equivE Equivalence.downK.
+ move=> a b f.
  move: (il a b f).
  by rewrite !equivE Equivalence.downK.
+ move=> a b e f f' g.
  move: (cl a b e f f' g).
  rewrite !equivE Equivalence.downK => H H'.
  move: (H H'); by rewrite Equivalence.downK.
+ move=> a b e f f' g.
  move: (cr a b e f f' g).
  rewrite !equivE Equivalence.downK => H H'.
  move: (H H'); by rewrite Equivalence.downK.
Defined.
Lemma downK (C : category@{t}) :
  Category.sort C = Category.sort (down C).
Proof. by case: C. Defined.
Definition get_down (C : category@{t}) (s : Category.sort C) : Category.sort (down C).
by rewrite -downK. Defined.
Lemma downK_mor (C : category@{t}) (a b : Category.sort C) :
  morph C a b = morph (down C) (get_down a) (get_down b).
by case: C a b => ? []. Defined.
Definition get_down_mor (C : category@{t}) (a b : Category.sort C) (f : Mor(a, b)) :
  morph (down C) (get_down a) (get_down b).
by rewrite -downK_mor.
Defined.
Definition get_up (C : category@{t}) (s : Category.sort (down C)) : Category.sort C.
move: s; by rewrite -downK. Defined.
Definition get_up_mor (C : category@{t}) (a b : Category.sort (down C))
           (f : morph (down C) a b) : morph C (get_up a) (get_up b).
case: C a b f => ? [] //=.
Defined.
Lemma up_down C (X : Ob (Down.down C)) : Down.get_down (Down.get_up X) = X.
by case: C X => ? [] /=. Defined.
Lemma down_up C (X : Ob C) : Down.get_up (Down.get_down X) = X.
by case: C X => ? [] /=. Defined.
End Down.
End Down.

Definition down C : Fun (C, Down.down C).
apply: (FunType _ _ (@FunMixin _ _ _ (@Down.get_down_mor C) _ _ _)).
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros.
move=> ? ? ? ? H; by rewrite equivE /= Equivalence.downK.
Defined.
Definition up C : functor (Down.down C) C.
apply: (@Functor.pack (Down.down C) C).
apply: (@FunMixin _ _ (@Down.get_up C) (@Down.get_up_mor C) _ _ _).
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros.
move=> ? ? ? ?; by rewrite equivE /= Equivalence.downK.
Defined.

Lemma down_upK C : down C \compf up C == idf (Down.down C).
Proof.
apply (funaltE (fun (A : Down.down C) =>
Congruence.suff_eq (Down.up_down A) : (down C \compf up C) A == idf _ A)).
case: C => ? [??????????] X Y f.
apply: Congruence.etrans; apply/symP;
first apply compm0.
by apply comp0m.
Defined.
Coercion Down.down : category >-> category.

Lemma compfE C D E (F : Fun(C, D)) (G : Fun(D, E)) :
  G \compf F == G \compm F.
Proof. by apply/reflP. Defined.

Lemma compfA C D E I
      (h : Fun(C, D)) (i : Fun(D, E)) (j : Fun (E, I)) :
  j \compf (i \compf h) == (j \compf i) \compf h.
Proof.
apply: (Pairing (NatType _ _ (@NatMixin _ _ ((j \compf i) \compf h) (j \compf (i \compf h)) _ _ (fun _ => id) (@idn_map_naturality _ _ _)))
                (NatType _ _ (@NatMixin _ _ (j \compf (i \compf h)) ((j \compf i) \compf h) _ _ (fun _ => id) (@idn_map_naturality _ _ _)))).
apply Isomorphisms => X;
apply/symP; by apply: comp0m.
Defined.

Lemma pres_isom C D A B
      (i1 : Mor (A, B))
      (i2 : Mor (B, A))
      (F : Fun (C, D)) :
  isomorphisms i1 i2 -> isomorphisms ('F i1) ('F i2).
Proof.
case => H1 H2.
apply: Isomorphisms;
(apply: Congruence.etrans; first (apply/symP; apply: pres_comp));
(apply: Congruence.etrans; last apply: id_id);
by apply: pres_equiv.
Defined.

Lemma fun_inj C D A B (F : Fun (C, D)) :
  A == B -> F A == F B.
Proof.
case=> f g H; apply (Pairing _ _ (pres_isom F H)).
Defined.

Lemma isomK C D A
      (i1 : Fun (C, D))
      (i2 : Fun (D, C)) :
  isomorphisms i1 i2 -> i2 (i1 A) == A.
Proof.
case=> H ?.
 apply (Pairing (H.1 A) (H.2 A)).
 constructor;
 by case: H => f g [] /(_ A) ? /(_ A) ?.
Defined.

Section trivials.
Import PartialEquiv.
Lemma compfmE C D E (F : Fun(C, D)) (G : Fun(D, E))
      a b (f : Mor (a, b))
  : '(G \compf F) f == ('G \o 'F) f.
Proof. by apply/reflP. Defined.
Lemma isomNm C D
      (i1 i2 : Fun (C, D))
      a b (f g : Mor (a, b)) :
  i1 == i2 -> 'i1 f == 'i1 g -> 'i2 f == 'i2 g.
Proof.
move=> [ll lr] [rl rr] H.
apply: Congruence.etrans; first apply: compm0.
apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: rr).
apply: Congruence.etrans; first (apply/symP; apply: compmA).
apply: Congruence.etrans; first (apply: subst_left; apply/symP; apply: naturality).
apply: Congruence.etrans; first (apply: subst_left; apply: subst_right; apply: H).
apply: Congruence.etrans; first (apply: subst_left; apply: naturality).
apply: Congruence.etrans; first apply: compmA.
apply: Congruence.etrans; first (apply: subst_right; apply: rr).
apply: Congruence.etrans; first (apply/symP; apply: compm0).
apply/reflP.
Defined.

Lemma isomKm C D
      (i1 : Fun (C, D))
      (i2 : Fun (D, C))
      a b (f g : Mor (a, b)) :
  isomorphisms i1 i2 ->
  'i1 f == 'i1 g -> f == g.
Proof.
case=> H1 H2 H.
have H': '(i2 \compf i1) f == '(i2 \compf i1) g.
 apply: Congruence.etrans; first apply: compfmE.
 apply: Congruence.etrans; last (apply/symP; apply: compfmE).
 rewrite /=; by apply: pres_equiv.
suff: '(idf _) f == '(idf _) g => //.
by apply (isomNm H1).
Defined.

Lemma isom_sym C (b c : Ob C) (i1 : Mor (b, c)) i2 : 
  isomorphisms i1 i2 -> isomorphisms i2 i1.
Proof.
  case=> H1 H2.
  apply: (Isomorphisms H2 H1).
Defined.
Hint Resolve isom_sym.

Lemma isomKL C (a b c : Ob C) (f : Mor (a, b)) (g : Mor (a, c)) i1 i2 : 
  isomorphisms i1 i2 -> g == i1 \compm f -> i2 \compm g == f.
Proof.
case=> H1 H2 H.
apply: Congruence.etrans; first (apply: subst_right; apply: H).
apply: Congruence.etrans; first (apply/symP; apply: compmA).
apply: Congruence.etrans; first (apply: subst_left; apply H1).
apply/symP. apply comp0m.
Defined.

Lemma isomKR C (a b c : Ob C) (f : Mor (a, b)) (g : Mor (c, b)) i1 i2 : 
  isomorphisms i1 i2 -> g == f \compm i1 -> g \compm i2 == f.
Proof.
case=> H1 H2 H.
apply: Congruence.etrans; first (apply: subst_left; apply: H).
apply: Congruence.etrans; first apply: compmA.
apply: Congruence.etrans; first (apply: subst_right; apply H2).
apply/symP. apply compm0.
Defined.
End trivials.

Section Product.
Variable C D : category.
Definition prod_mor (a b : Ob C * Ob D) := prod (Mor(fst a, fst b)) (Mor(snd a, snd b)).
Definition prod_id (a : Ob C * Ob D) : prod_mor a a := (@Category.id _ _ (fst a), @Category.id _ _ (snd a)).
Definition prod_comp (a b c : Ob C * Ob D) (bc : prod_mor b c) (ab : prod_mor a b) : prod_mor a c :=
  (fst bc \compm fst ab, snd bc \compm snd ab).
Definition prod_cat_equivMixin A B := prod_equivMixin (@equiv C (fst A) (fst B)) (@equiv D (snd A) (snd B)).

Arguments prod_comp /.
Lemma prod_associativity : @Category.associativity_of_morphisms _ prod_mor prod_comp prod_cat_equivMixin.
Proof. by move=> [??] [??] [??] [??] [??] [??] [??]; split; apply compmA. Qed.

Lemma prod_compm0 : @Category.identity_morphism_is_right_identity _
                                                                  prod_mor
                                                                  prod_id
                                                                  prod_comp
                                                                  prod_cat_equivMixin.
Proof. by move=> [??] [??] [??]; split; apply compm0. Defined.
Lemma prod_comp0m : @Category.identity_morphism_is_left_identity _
                                                                  prod_mor
                                                                  prod_id
                                                                  prod_comp
                                                                  prod_cat_equivMixin.
Proof. by move=> [??] [??] [??]; split; apply comp0m. Defined.

Lemma prod_comp_left : @Category.compatibility_left _ prod_mor prod_comp prod_cat_equivMixin.
Proof. move=> [??] [??] [??] [??] [??] [??] [??]; split; by apply: comp_left. Defined.

Lemma prod_comp_right : @Category.compatibility_right _ prod_mor prod_comp prod_cat_equivMixin.
Proof. move=> [??] [??] [??] [??] [??] [??] [??]; split; by apply: comp_right. Defined.
Canonical prod_catMixin := (CatMixin prod_associativity prod_compm0 prod_comp0m prod_comp_left prod_comp_right).
Canonical prod_catType := Eval hnf in CatType (Ob C * Ob D) prod_catMixin.
Definition pfst : Fun(prod_catType, C).
  apply: (FunType _ _ (@FunMixin prod_catType C fst (fun _ _ => fst) _ _ _)).
+ move=> ?; by apply/reflP.
+ move=> ? ? ? ? ?; by apply/reflP.
+ by move=> ? ? [??] [??] [??].
Defined.

Definition psnd : Fun(prod_catType, D).
  apply: (FunType _ _ (@FunMixin prod_catType D snd (fun _ _ => snd) _ _ _)).
+ move=> ?; by apply/reflP.
+ move=> ? ? ? ? ?; by apply/reflP.
+ by move=> ? ? [??] [??] [??].
Defined.
End Product.
Notation "a * b" := (prod_catType a b).
Arguments pfst / {_ _}.
Arguments psnd / {_ _}.

Section Comma. 
Variables C D E : category.
Variable F : Fun(C, D).
Variable G : Fun(E, D).
Import PartialEquiv.
Structure comma_ob :=
  CommaOb { domL; domR; mor :> Mor (F domL, G domR) }.
Definition comma_mor (o1 o2 : comma_ob) :=
  @pairing Mor(domL o1, domL o2) Mor(domR o1, domR o2)
           (fun mc me => 'G me \compm o1 == o2 \compm 'F mc).
Definition comma_comp o1 o2 o3
(j : comma_mor o2 o3) (i : comma_mor o1 o2) : comma_mor o1 o3 :=
Pairing (j.1 \compm i.1) (j.2 \compm i.2)
match i, j with
| Pairing i1 i2 fg, Pairing j1 j2 gh =>
  transP (subst_left (pres_comp i2 j2))
 (transP (compmA o1 _ _)
 (transP (subst_right fg)
 (transP (symP (compmA _ o2 _))
 (transP (subst_left gh)
 (transP (transP (compmA _ _ o3) reflP)
 (subst_right (symP (pres_comp i1 j1))))))))
end.

Definition comma_id o : comma_mor o o :=
Pairing id id (transP (subst_left (id_id _))
              (transP (transP ([eta symP] (comp0m _)) (compm0 _))
              (subst_right ([eta symP] (id_id _))))).

Definition comma_equivMixin f g :=
  let S := @partial_equivType (Ob C) (Category.class C) (domL f) (domL g) in
  let T := @partial_equivType (Ob E) (Category.class E) (domR f) (domR g) in
  @pairing_equivMixin S T.

Lemma comma_compmA : @Category.associativity_of_morphisms _ _ comma_comp (fun a b => @comma_equivMixin a b _).
Proof.
move => /= f g h i [j1 j2 jH] [k1 k2 kH] [l1 l2 lH].
by apply: pair; apply: compmA.
Defined.
Lemma comma_compm0 : @Category.identity_morphism_is_right_identity _ _ comma_id comma_comp (fun a b => @comma_equivMixin a b _).
Proof.
move => /= f g h.
by apply: pair; apply: compm0.
Defined.
Lemma comma_comp0m : @Category.identity_morphism_is_left_identity _ _ comma_id comma_comp (fun a b => @comma_equivMixin a b _).
Proof.
move => /= f g h.
by apply: pair; apply: comp0m.
Defined.
Lemma comma_comp_left : @Category.compatibility_left _ _ comma_comp (fun a b => @comma_equivMixin a b _).
Proof.
move => ? ? ? [f1 f2 Hf] [f'1 f'2 Hf'] [g1 g2 Hg] [ff'1 ff'2].
by apply: pair; apply: comp_left.
Defined.
Lemma comma_comp_right : @Category.compatibility_right _ _ comma_comp (fun a b => @comma_equivMixin a b _).
Proof.
move => ? ? ? [f1 f2 Hf] [f'1 f'2 Hf'] [g1 g2 Hg] [ff'1 ff'2].
by apply: pair; apply: comp_right.
Defined.
Canonical comma_catMixin := Eval hnf in CatMixin comma_compmA comma_compm0 comma_comp0m comma_comp_left comma_comp_right.
Canonical com := Eval hnf in CatType comma_ob comma_catMixin.

Definition forget_com_ob (o : comma_ob) := (domL o, domR o).
Definition forget_com_mor (o1 o2 : comma_ob) (f : comma_mor o1 o2)
  : Mor(forget_com_ob o1, forget_com_ob o2) := (f.1, f.2).
Definition forget_com_id_id : Functor.maps_identity_to_identity forget_com_mor.
Proof. move=> ?. apply/reflP. Defined.
Definition forget_com_pres_comp : Functor.preserve_composition forget_com_mor.
Proof. move=> ? ? ? [?? ?] [?? ?]. apply/reflP. Defined.
Definition forget_com_pres_equiv : Functor.preserve_equivalence forget_com_mor.
Proof. move=> ? ? [?? ?] [?? ?] [??]. by constructor. Defined.
Definition forget_comMixin := FunMixin forget_com_id_id forget_com_pres_comp forget_com_pres_equiv.
Definition fcom := FunType _ _ forget_comMixin.
End Comma.
Notation ", A" := (CommaOb A).

Definition smush C D (A : Ob D) :=
  FunType C D (@FunMixin C D (fun _ : Ob C => A)
                         (fun _ _ _ => id)
                         (fun _ : Ob C => reflP)
                         (fun _ _ _ _ _ => comp0m id)
                         (fun _ _ _ _ _ => reflP)).
Section Diag.
Variables I C : category.
Definition diag_ob X := @smush I C X.
Definition diag_mor X Y (f : Mor (X, Y)) : morph (Fun (I, C)) (diag_ob X) (diag_ob Y) :=
  NatType (diag_ob X) (diag_ob Y) (NatMixin (fun _ _ _ => Congruence.etrans ([eta symP] (compm0 f)) (comp0m f))).
Definition diag_id_id : Functor.maps_identity_to_identity diag_mor.
move=> ? ? /=; by apply/reflP.
Defined.
Definition diag_pres_comp : Functor.preserve_composition diag_mor.
move=> ? ? ? ? ? ? /=; by apply/reflP.
Defined.
Definition diag_pres_equiv : Functor.preserve_equivalence diag_mor.
by move=> ? ? ? ? ? /=.
Defined.
Definition diag_Mixin := FunMixin diag_id_id diag_pres_comp diag_pres_equiv.
Definition diag := FunType _ _ diag_Mixin.
End Diag.

Section Point.
Inductive point_ob := pt : point_ob.
Definition point_mor (x y : point_ob) := point_ob.
Definition point_comp (x y z : point_ob) : point_mor y z -> point_mor x y -> point_mor x z := (fun _ _ => pt).
Lemma point_associativity : @Category.associativity_of_morphisms _ _ point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => /= C D E F h i j; by apply/reflP. Defined.
Lemma point_compm0 : @Category.identity_morphism_is_right_identity _ _ (fun _ => pt) point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => /= C D []; by apply/reflP. Defined.
Lemma point_comp0m : @Category.identity_morphism_is_left_identity _ _ (fun _ => pt) point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => /= C D []; by apply/reflP. Defined.
Lemma point_comp_left : @Category.compatibility_left _ _ point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => [] [] [] [] [] [] _; by apply/reflP. Defined.
Lemma point_comp_right : @Category.compatibility_right _ _ point_comp (fun _ _ => trivial_equivMixin point_ob).
Proof. move => [] [] [] [] [] [] _; by apply/reflP. Defined.
Canonical point_catMixin :=
  Eval hnf in CatMixin point_associativity point_compm0 point_comp0m point_comp_left point_comp_right.
Canonical point_catType := Eval hnf in CatType _ point_catMixin.
Coercion pto_pt (_ : point_ob) := point_catType.
Local Notation "f == g" := (equiv_op f g).
Variable C : category.
Local Definition sp := @smush pt C.
Local Definition Fm : forall x y, Mor (x, y) -> Mor(sp x, sp y).
refine (fun x y (f : Mor(x, y)) => (NatType _ _ (@NatMixin _ _ (sp x) (sp y) _ _ (fun _ => f) _))).
move=> ? ? ? /=.
apply: Congruence.etrans.
apply/symP; apply: compm0.
apply: comp0m.
Defined.
Definition ptC_id_id : Functor.maps_identity_to_identity Fm.
move=> ? ? /=; by apply/reflP.
Defined.
Definition ptC_pres_comp : Functor.preserve_composition Fm.
move=> ? ? ? ? ? ? /=; by apply/reflP.
Defined.
Definition ptC_pres_equiv : Functor.preserve_equivalence Fm.
by move=> ? ? ? ? ? /=.
Defined.
Definition ptC_Mixin := FunMixin ptC_id_id ptC_pres_comp ptC_pres_equiv.
Definition ptC := FunType _ _ ptC_Mixin.
Local Definition Gm : forall (x y : Fun(pt, C)), Nat(x, y) -> morph C (x pt) (y pt).
move=> x y f /=.
apply: (f pt).
Defined.
Definition Cpt_id_id : Functor.maps_identity_to_identity Gm.
move=> ? /=; by apply/reflP.
Defined.
Definition Cpt_pres_comp : Functor.preserve_composition Gm.
move=> ? ? ? ? ? /=; by apply/reflP.
Defined.
Definition Cpt_pres_equiv : Functor.preserve_equivalence Gm.
move=> ? ? [f ? ?] [f' ? ?].
apply.
Defined.
Definition Cpt_Mixin := FunMixin Cpt_id_id Cpt_pres_comp Cpt_pres_equiv.
Definition Cpt := FunType _ _ Cpt_Mixin.
Section SpK.
Variable F : Fun(pt, C).
Definition spF x : Mor(sp (F pt) x, F x) :=
  match x with
  | pt => id
  end.
Definition Fsp x : Mor(F x, (smush pt (F pt)) x) :=
  match x with
  | pt => id
  end.

Lemma spK : F == smush pt (F pt).
 have H1: NaturalTransformation.axiom Fsp.
  move=> [] [] [].
  apply: Congruence.etrans.
  apply/symP; apply: comp0m.
  apply: Congruence.etrans; last apply: compm0.
  by apply: id_id.
 have H2: NaturalTransformation.axiom spF.
  move=> [] [] [] /=.
  apply: Congruence.etrans.
  apply/symP; apply: compm0.
  apply: Congruence.etrans; last apply: compm0.
  apply/symP; apply: id_id.
refine (Pairing
          (NatType _ _ (@NatMixin _ _ F (smush pt (F pt)) _ _ Fsp H1))
          (NatType _ _ (@NatMixin _ _ (smush pt (F pt)) F _ _ spF H2)) _).
constructor; case.
+ apply: Congruence.etrans; last (apply/symP; apply comp0m).
  by apply: compm_comp; apply/reflP.
+ apply: Congruence.etrans; last (apply/symP; apply comp0m).
  by apply: compm_comp; apply/reflP.
Defined.
End SpK.
End Point.

Section Point.
Local Notation "f == g" := (equiv_op f g).
Import PartialEquiv.
Lemma pointE C : Fun(pt, C) == C.
apply (Pairing (down C \compf Cpt C)
               (ptC C \compf up C)).
apply: Isomorphisms.
 set Ho :=
 (fun (A : Fun (pt, C)) =>
    eq_rect_r (fun p => sp p == A) ([eta symP] (spK A)) (Down.down_up (A pt))
    : ((ptC C \compf up C) \compf (down C \compf Cpt C)) A == idf _ A).
 apply (funaltE Ho); subst Ho.
 case: C => ? []; intros; case => /=.
 apply: Congruence.etrans; first (apply/symP; apply compm0).
 apply: Congruence.etrans; first (apply/symP; apply comp0m).
 apply/reflP.
set Ho := 
(fun A => eq_rect_r (equiv_op^~ A) reflP (Down.up_down A))
: forall A, ((down C \compf Cpt C) \compf (ptC C \compf up C)) A == (idf _) A.
apply (funaltE Ho); subst Ho.
move=> X Y f.
apply: Congruence.etrans; last first.
apply/symP; apply comp0m.
apply: Congruence.etrans; last first.
apply/symP; apply compm0.
have: (id \compm '(idf _) f) \compm id == (id \compm '(idf _) f) \compm id by apply/reflP.
by case: C X Y f => ? [?????????????].
Defined.
End Point.

Lemma diagW I C x y : diag pt C x == diag pt C y -> diag I C x == diag I C y.
Proof.
move=> H.
apply: (Pairing ('(diag I C) (H.1 pt)) ('(diag I C) (H.2 pt)));
apply: Isomorphisms; case: H => f g [H1 H2]; move: (H1 pt) (H2 pt);
by compute.
Defined.

Lemma diagK I C x y :
  Ob I -> diag I C x == diag I C y -> x == y.
Proof.
move=> z H.
apply: (Pairing (H.1 z) (H.2 z)); apply: Isomorphisms;
case: H => f g [H1 H2]; by move: (H1 z) (H2 z).
Defined.

Lemma diagDL I C D F X : Mor(F \compf (diag I C) X, (diag I D) (F X)).
apply: (NatType (F \compf (diag I C) X) ((diag I D) (F X)) (@NatMixin _ _ _ _ _ _ (fun _ => id) _)).
move=> ? ? ?; apply: subst_right.
apply: Congruence.etrans; last apply: id_id.
apply/reflP.
Defined.

Lemma diagDR I C D (F : Fun (C, D)) X : Mor((diag I D) (F X), F \compf (diag I C) X).
apply: (NatType ((diag I D) (F X)) (F \compf (diag I C) X) (@NatMixin _ _ _ _ _ _ (fun _ => id) _)).
move=> ? ? ?; apply: subst_left.
apply: Congruence.etrans; last (apply/symP; apply: id_id).
apply/reflP.
Defined.

Lemma diagD I C D F X : F \compf (diag I C) X == (diag I D) (F X).
Proof.
apply: (Pairing (diagDL I F X) (diagDR I F X)).
apply: Isomorphisms => x;
apply/symP; apply: compm0.
Defined.

Section Limit.
Variables I C : category.
Variable F : Fun (I, C).
Definition cones :=
  com (diag I C) ((pointE Fun (I, C)).2 F).
Import PartialEquiv.
Definition limit L (Lm : Mor (diag cones cones L, idf _)) :=
  forall S Sm, Sm == Lm S.
Definition vertex (d : Ob cones) : Ob C := domL d.

Lemma vertex_inj L L' : L == L' -> vertex L == vertex L'.
Proof.
move=> H.
apply (Pairing H.1.1 H.2.1);
apply: Isomorphisms;
by case: H => [[f1 ? ?] [f2 ? ?] [[? ?] [? ?]]].
Defined.

Lemma limit_is_the_unique L L' Lm Lm' :
  @limit L Lm -> @limit L' Lm' -> L == L'.
Proof.
move=> limL limL'.
apply (Pairing (Lm L') (Lm' L)); apply: Isomorphisms.
 apply: Congruence.etrans; first
  apply (limL L (Lm' L \compm Lm L')).
 by apply/symP; apply (limL L id).
apply: Congruence.etrans; first
 apply (limL' L' (Lm L' \compm Lm' L)).
by apply/symP; apply (limL' L' id).
Defined.

Definition system (L : Ob C)
 (S : forall i, Mor (L, F i))
 (H : forall i j (f : Mor (i, j)),
     S j == 'F f \compm S i) : Ob cones.
apply: (@CommaOb _ _ _ _ _ L pt).
apply: (NatType _ _ (NatMixin
       (_ : NaturalTransformation.axiom (S : forall i, Mor (diag I C L i, F i))))).
move=> ? ? f; apply (transP (symP (compm0 (S _))) (H _ _ f)).
Defined.
End Limit.
Arguments limit {_ _} F L Lm.
Arguments system {_ _ _ _} S H.

Section Cones.
Variables I C D : category.
Variables (d  : Fun (I, C)) (F : Fun (C, D)).
(* stack overflow !? *)
Definition cones_map_ob (a : cones d) : cones (F \compf d).
 apply ((@CommaOb _ _ _ (diag I D) ((pointE Fun (I, D)).2 (F \compf d)) (F (vertex a)) pt) ((F \compfn mor a) \compn (diagD I F _).2)).
Defined.
Import PartialEquiv.
Definition cones_map_mor (x y : cones d) (f : Mor (x, y)) : Mor (cones_map_ob x, cones_map_ob y).
case: x y f => xd ? xm [] yd ? ym [] xy ? xye.
have xme: xm == ym \compm diag_mor I xy.
 apply: Congruence.etrans.
 apply: comp0m.
 apply: xye.
have ez: forall z, (F \compfn xm) z == (F \compfn (ym \compm diag_mor I xy)) z.
 move=> z.
 apply: Congruence.etrans; first (apply: pres_equiv; apply (xme z)).
 by apply: Congruence.etrans; last apply/symP; apply: pres_comp.
apply: (Pairing ('F xy) pt) => z.
apply: Congruence.etrans.
apply: subst_right.
apply: subst_left.
apply ez.
apply: Congruence.etrans.
apply/symP; apply: comp0m.
apply: Congruence.etrans.
apply/symP; apply: compm0.
apply: Congruence.etrans; first apply: pres_comp.
apply: subst_left.
apply: compm0.
Defined.
Lemma cones_map_id_id : Functor.maps_identity_to_identity cones_map_mor.
Proof.
move=> [] xD [] xm.
constructor.
apply: id_id.
apply/reflP.
Defined.
Lemma cones_map_pres_comp : Functor.preserve_composition cones_map_mor.
Proof.
move=> [] aD [] am [] bD [] bm [] cD [] cm [f1 [] fH] [g1 [] gH].
constructor.
apply: pres_comp.
apply: compm0.
Defined.
Lemma cones_map_pres_equiv : Functor.preserve_equivalence cones_map_mor.
Proof.
move=> [] aD [] am [] bD [] bm [f1 [] fH] [g1 [] gH] [fgH ?].
constructor.
by apply: pres_equiv.
by apply/reflP.
Defined.
Definition cones_mapMixin :=
  FunMixin cones_map_id_id cones_map_pres_comp cones_map_pres_equiv.
Definition cones_map := FunType _ _ cones_mapMixin.
End Cones.
Arguments cones_map {_ _ _} d F.

Section Pointed.
Variable C : category.
Definition pt_ob := option (Ob C).
Local Definition pt_mor (o1 o2 : pt_ob) :=
  match o1, o2 with
  | None, _ => True
  | _, None => False
  | Some o1', Some o2' => morph C o1' o2'
  end.
Local Definition pt_comp o1 o2 o3
(j : pt_mor o2 o3) (i : pt_mor o1 o2) : pt_mor o1 o3.
case: o1 o2 o3 j i => [?|//] [?|//] [?|//].
apply compm.
Defined.
Local Definition pt_id o : pt_mor o o.
case: o => // ?.
apply id.
Defined.
Local Definition pt_op o1 o2 (f g : pt_mor o1 o2) : Type.
case: o1 o2 f g => [a|//] [b|//]; first
apply (@equiv_op (EquivType _ (equiv C a b)));
intros; apply True.
Defined.
Local Definition pt_equivMixin o1 o2 : Equivalence.mixin_of (pt_mor o1 o2).
apply: (EquivMixin (_ : Equivalence.symmetricity (@pt_op o1 o2)) _ _).
case: o1 o2 => [?|//] [?|//] //= ? ?; apply/symP.
case: o1 o2 => [?|//] [?|//] //= ? ? ?; apply/transP.
case: o1 o2 => [?|//] [?|//] //= ?; apply/reflP.
Defined.
Local Lemma pt_compmA : Category.associativity_of_morphisms pt_comp pt_equivMixin.
Proof. move=> [?|] [?|] [?|] [?|] //=; apply compmA. Defined.
Local Lemma pt_compm0 : Category.identity_morphism_is_right_identity pt_id pt_comp pt_equivMixin.
Proof. move=> [?|] [?|] //=; apply compm0. Defined.
Local Lemma pt_comp0m : Category.identity_morphism_is_left_identity pt_id pt_comp pt_equivMixin.
Proof. move=> [?|] [?|] //=; apply comp0m. Defined.
Local Lemma pt_comp_left : Category.compatibility_left pt_comp pt_equivMixin.
Proof. move=> [?|] [?|] [?|] //=; apply: comp_left. Defined.
Local Lemma pt_comp_right : Category.compatibility_right pt_comp pt_equivMixin.
Proof. move=> [?|] [?|] [?|] //=; apply: comp_right. Defined.
Local Definition pt_catMixin :=
  Eval hnf in CatMixin pt_compmA pt_compm0 pt_comp0m pt_comp_left pt_comp_right.
Canonical pointed_cat := Eval hnf in CatType (option (Ob C)) pt_catMixin.

Definition incl_ob (a : Ob C) : pt_ob := Some a.
Definition incl_mor (x y : Ob C) (f : Mor (x, y)) : Mor (incl_ob x, incl_ob y) := f.
Local Lemma incl_id_id : Functor.maps_identity_to_identity incl_mor.
Proof. move=> ?. apply/reflP. Defined.
Local Lemma incl_pres_comp : Functor.preserve_composition incl_mor.
Proof. move=> ? ? ? ? ?; apply/reflP. Defined.
Local Lemma incl_pres_equiv : Functor.preserve_equivalence incl_mor.
Proof. by []. Defined.
Definition incl_Mixin :=
  FunMixin incl_id_id incl_pres_comp incl_pres_equiv.
Definition incl_pt := FunType _ _ incl_Mixin.
End Pointed.

Module Triple.
Local Inductive tri_ob := L | R | C.
Inductive LC : Type := LCC.
Inductive RC : Type := RCC.
Local Definition tri_mor (o1 o2 : tri_ob) :=
  match o1, o2 with
  | L, C => LC
  | R, C => RC
  | L, L | R, R | C, C => True : Type
  | _, _ => False
  end.
Local Definition tri_comp o1 o2 o3
(j : tri_mor o2 o3) (i : tri_mor o1 o2) : tri_mor o1 o3.
by case: o1 o2 o3 j i => [] [] [].
Defined.
Local Definition tri_id o : tri_mor o o.
by case o. Defined.
Definition tri_equivMixin (a b : tri_ob) := trivial_equivMixin (tri_mor a b).
Local Lemma tri_compmA : Category.associativity_of_morphisms tri_comp tri_equivMixin.
Proof. by []. Defined.
Local Lemma tri_compm0 : Category.identity_morphism_is_right_identity tri_id tri_comp tri_equivMixin.
Proof. by []. Defined.
Local Lemma tri_comp0m : Category.identity_morphism_is_left_identity tri_id tri_comp tri_equivMixin.
Proof. by []. Defined.
Local Lemma tri_comp_left : Category.compatibility_left tri_comp tri_equivMixin.
Proof. by []. Defined.
Local Lemma tri_comp_right : Category.compatibility_right tri_comp tri_equivMixin.
Proof. by []. Defined.
Local Definition tri_catMixin :=
  Eval hnf in CatMixin tri_compmA tri_compm0 tri_comp0m tri_comp_left tri_comp_right.
Canonical triple := Eval hnf in CatType _ tri_catMixin.
Definition tri_cones : cones (incl_pt triple).
apply: (@CommaOb _ _ _ _ _ None pt).
have H: forall X : triple,
Mor (((diag triple (pointed_cat triple)) None) X, (((pointE Fun (triple, pointed_cat triple)).2 (incl_pt triple)) pt) X)
 by case.
apply: (NatType _ _ (NatMixin (_ : _ H))).
by move=> [] [] //.
Defined.
Section Assign.
Variable C : category.
Variables l c r : Ob C.
Variable lc : Mor (l, c).
Variable rc : Mor (r, c).
Local Definition asgn_ob x :=
match x with
| L => l | R => r | C => c
end.
Local Definition asgn_mor x y (f : Mor (x, y)) : Mor(asgn_ob x, asgn_ob y).
case: x y f => [] [] // _; apply id.
Defined.
Local Lemma asgn_id_id : Functor.maps_identity_to_identity asgn_mor.
Proof. move=> []; by apply/reflP. Defined.
Local Lemma asgn_pres_comp : Functor.preserve_composition asgn_mor.
Proof.
move=> [] [] [] // ? ?; (try by apply compm0); by apply comp0m.
Defined.
Local Lemma asgn_pres_equiv : Functor.preserve_equivalence asgn_mor.
Proof. move=> [] [] // ? ? ?; by apply/reflP. Defined.
Definition asgn_Mixin :=
  FunMixin asgn_id_id asgn_pres_comp asgn_pres_equiv.
Definition triplef := FunType _ _ asgn_Mixin.
End Assign.
Notation LC' := (LCC : Mor (L, C)).
Notation RC' := (RCC : Mor (R, C)).
Section Lift.
Variable C : category.
Variable F : Fun (triple, C).
Variable ptC : Ob C.
Variable Lm : Mor (ptC, F L).
Variable Rm : Mor (ptC, F R).
Import PartialEquiv.
Variable LRC : 'F LC' \compm Lm == 'F RC' \compm Rm.
Definition Fo' o :=
  match o with
  | None => ptC
  | Some x => F x
  end.
Definition Fm' (o o' : Ob (pointed_cat triple))
           (f : Mor (o, o')) : Mor (Fo' o, Fo' o').
case: o o' f => [?|] [o'|] //= f.
+ apply ('F f).
+ case: o'.
  - apply Lm.
  - apply Rm.
  - apply ('F LC' \compm Lm).
+ apply id.
Defined.
Definition lift_pt : Fun (pointed_cat triple, C).
apply: (FunType _ _ (FunMixin (_ : _ Fm') _ _)).
move=> [] // [] //; apply: id_id.
move=> [[]|] [[]|] [[]|] [] [] //=;
apply pres_comp || apply compf0m.
move=> [[]|] [[]|] // ? ? ?; by apply pres_equiv.
Defined.
End Lift.
End Triple.
Definition triple := Triple.triplef.
Arguments triple {_ _ _ _} _ _.
Notation triple_lift f g f' g' := (@Triple.lift_pt _ (triple f g) _ f' g').

Definition adjunction C D (F : Fun (C, D)) (G : Fun (D, C)) :=
  pairing (fun f g =>
             prod (* (fcom F (idf D) \compf g == fcom (idf C) G) *)
               (@isomorphisms cats (com F (idf D)) (com (idf C) G) f g)
               (fcom (idf C) G \compf f == fcom F (idf D))).
Arguments adjunction {_ _} _ _.

Section Adjunction.
Import PartialEquiv.
Section Unit.
Variables C D : category.
Variables (F : Fun (C, D)) (G : Fun (D, C))
          (adj : adjunction F G).
Lemma domLS1 : forall h, domL (adj.1 h) == domL h.
Proof.
case: adj => ? ? [] ? [fH1 fH2 H] h.
apply (Pairing (fst (fH1 h)) (fst (fH2 h))).
constructor;
by case: H => /(_ h) [] ? ? /(_ h) [] ? ?.
Defined.

Lemma domRS1 : forall h, domR (adj.1 h) == domR h.
Proof.
case: adj => ? ? [] ? [fH1 fH2 H] h.
apply (Pairing (snd (fH1 h)) (snd (fH2 h))).
constructor;
by case: H => /(_ h) [] ? ? /(_ h) [] ? ?.
Defined.

Lemma adj2C : fcom F (idf D) \compf adj.2 == fcom (idf C) G.
Proof.
case: adj=> L R [] H H'.
apply: Congruence.etrans; first (apply: subst_left; apply/symP; apply H').
apply: Congruence.etrans; first apply: compmA.
apply: Congruence.etrans; first (apply: subst_right; case: H => ?; apply).
apply/symP; apply compm0.
Defined.

Lemma domLS2 : forall h, domL (adj.2 h) == domL h.
Proof.
case: adj2C => [fH1 fH2 H] h.
apply (Pairing (fst (fH1 h)) (fst (fH2 h))).
constructor;
by case: H => /(_ h) [] ? ? /(_ h) [] ? ?.
Defined.

Lemma domRS2 : forall h, domR (adj.2 h) == domR h.
Proof.
case: adj2C => [fH1 fH2 H] h.
apply (Pairing (snd (fH1 h)) (snd (fH2 h))).
constructor;
by case: H => /(_ h) [] ? ? /(_ h) [] ? ?.
Defined.

Lemma adj_unit : Nat (idf _, G \compf F).
Proof.
pose id' := @CommaOb _ _ _ F (idf _) _ _ (Category.id (F _)).
have HN: NaturalTransformation.axiom (fun X => 
     'G (domRS1 _).1 \compm (adj.1 (id' X)) \compm (domLS1 _).2
     : Mor (idf _ X, (G \compf F) X)).
rewrite /domRS1 /domLS1 => A A' f.
case: adj => [] L R [] [] ? ? fH.
set fFf := (Pairing f (' F f) (Congruence.etrans ([eta symP] (compm0 _)) (comp0m _))
            : comma_mor (, id' A) (, id' A')).
move: (naturality fH.2 fFf) (naturality fH.1 fFf).
case: fH => e1 e2 ei [e11n e12n] [e21n e22n].
apply: Congruence.etrans; last apply: compmA.
apply: Congruence.etrans; last (apply: subst_left; apply: compmA).
apply: Congruence.etrans; last (do 2!apply: subst_left; apply: pres_comp).
apply: Congruence.etrans; last (do 2!apply: subst_left; apply: pres_equiv; apply: e22n).
apply: Congruence.etrans; last (do 2!apply: subst_left; apply/symP; apply: pres_comp).
apply: Congruence.etrans; first apply: compmA.
apply: Congruence.etrans; first (apply: subst_right; apply: e11n).
rewrite /=; case: (Functor.map_of_morphisms (Functor.class L) fFf)=> /= Lf LfF H.
apply: Congruence.etrans; last (apply: subst_left; apply/symP; apply: compmA).
apply: Congruence.etrans; last (apply: subst_left; apply: subst_right; apply/symP; apply H).
do !(apply: Congruence.etrans; first apply: compmA).
apply: Congruence.etrans; last (apply/symP; apply: compmA).
apply: subst_right.
apply/symP; apply: compmA.
apply: (NatType _ _ (NatMixin HN)).
Defined.

Lemma adj_counit : Nat (F \compf G, idf _).
Proof.
pose id' := @CommaOb _ _ _ (idf _) G _ _ (Category.id (G _)).
have HN: NaturalTransformation.axiom (fun X => 
     (domRS2 _).1 \compm (adj.2 (id' X)) \compm 'F (domLS2 _).2
     : Mor ((F \compf G) X, idf _ X)).
rewrite /domRS2 /domLS2 => A A' f.
case: adj adj2C => [] L R [] [] ? ? ? fH.
set Gff := (Pairing (' G f) f (Congruence.etrans ([eta symP] (compm0 _)) (comp0m _))
            : comma_mor (, id' A) (, id' A')).
move: (naturality fH.2 Gff) (naturality fH.1 Gff).
case: fH => e1 e2 ei [e11n e12n] [e21n e22n].
apply: Congruence.etrans; last apply: compmA.
apply: Congruence.etrans; last (apply: subst_left; apply: compmA).
apply: Congruence.etrans; last (do 2!apply: subst_left; apply: e22n).
apply: Congruence.etrans; first apply: compmA.
apply: Congruence.etrans; first (apply: subst_right;
apply: (_ : _ == ' F (fst (e2 (id' A')) \compm (' G f)));
apply/symP; apply: pres_comp).
apply: Congruence.etrans; first (apply: subst_right; apply: pres_equiv; apply e11n).
do !(apply: Congruence.etrans; first apply: compmA).
do !(apply: Congruence.etrans; last (apply/symP; apply: compmA)).
rewrite /=; case: (Functor.map_of_morphisms (Functor.class R) Gff) => /= RfG Rf H.
apply: subst_right.
apply: Congruence.etrans; last apply: compmA.
apply: Congruence.etrans; last (apply: subst_left; apply/symP; apply: H) .
do !(apply: Congruence.etrans; last (apply/symP; apply: compmA)).
apply: subst_right.
apply: pres_comp.
apply: (NatType _ _ (NatMixin HN)).
Defined.

Lemma adj_unitE a b (f : Mor (F a, idf _ b)) : 
  'G f \compm adj_unit a == 'G (domRS1 _).1 \compm (adj.1 (, f)) \compm (domLS1 _).2.
Proof.
set box := (Pairing (Category.id a) f
(transP (symP (compm0 (' (idf D) f))) (transP (compm0 (' (idf D) f)) (subst_right (symP (id_id a)))))
            : comma_mor (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F a))) (, f)).
rewrite /adj_unit /domLS2 /domRS2 /domLS1 /domRS1 /=.
case: adj adj2C => [] L R [] H [] bH11 bH12 bH1H [] bH21 bH22 bH2H.
apply: Congruence.etrans; first (apply: subst_right; apply: compmA).
do !(apply: Congruence.etrans; first (apply/symP; apply: compmA)).
apply: Congruence.etrans; first (do 2!apply: subst_left; apply/symP; apply: pres_comp).
apply: Congruence.etrans;
 first (do 2!apply: subst_left; apply: pres_equiv;
 case: (naturality bH11 box) => /= n11 n12; apply/symP; apply n12).
apply: Congruence.etrans; last (apply: subst_right; apply/symP; apply: compm0).
apply: Congruence.etrans; last (apply: subst_right;
case: (naturality bH12 box) => /= n21 n22; apply/symP; apply: n21).
apply: Congruence.etrans; first (do 2!apply: subst_left; apply: pres_comp).
do !(apply: Congruence.etrans; first apply: compmA).
do !(apply: Congruence.etrans; last (apply/symP; apply: compmA)).
apply: subst_right.
apply: Congruence.etrans; first (apply/symP; apply: compmA).
apply: Congruence.etrans; last apply: compmA.
apply: subst_left.
by case: (Functor.map_of_morphisms (Functor.class L) box).
Defined.
  
Lemma adj_counitE a b (f : Mor (idf _ a, G b)) : 
  adj_counit b \compm 'F f == (domRS2 _).1 \compm (adj.2 (, f)) \compm 'F (domLS2 _).2.
Proof.
set box := 
  (Pairing f (Category.id b)
           (transP (subst_left (id_id b)) (transP (symP (comp0m (, f))) (comp0m (, f))))
  : comma_mor (, f) (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G b)))).
rewrite /adj_counit /domLS2 /domRS2 /domLS1 /domRS1 /=.
case: adj adj2C => [] L R [] H [] bH11 bH12 bH1H [] bH21 bH22 bH2H.
apply: Congruence.etrans; first apply: compmA.
apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: pres_comp).
apply: Congruence.etrans; first (apply: subst_right; apply: pres_equiv;
case: (naturality bH22 box) => /= n21 n22; apply n21).
apply: Congruence.etrans; last (do 2!apply: subst_left; apply/symP; apply: comp0m).
apply: Congruence.etrans; last (do 2!apply: subst_left;
case: (naturality bH21 box) => /= n21 n22; apply: n22).
do !(apply: Congruence.etrans; first apply: compmA).
do !(apply: Congruence.etrans; last (apply/symP; apply: compmA)).
apply: subst_right.
apply: Congruence.etrans; first (apply: subst_right; apply: pres_comp).
do !(apply: Congruence.etrans; last apply: compmA).
do !(apply: Congruence.etrans; first (apply/symP; apply: compmA)).
apply: subst_left.
apply/symP;
by case: (Functor.map_of_morphisms (Functor.class R) box).
Defined.

Lemma adj_unitK :
  isomorphisms (F \compfn adj_unit : Mor (F, F \compf G \compf F))
               (adj_counit \compnf F).
Proof.
apply: Isomorphisms => X.
apply: Congruence.etrans.
apply: adj_counitE.
move: adj_counitE.
rewrite /adj_unit /domLS2 /domRS2 /domLS1 /domRS1 /=.
case: adj adj2C => [] L R [] H [] bH11 bH12 bH1H [] bH21 bH22 bH2H.
do !(apply: Congruence.etrans; first apply: compmA).
apply: isomKL.
apply: Isomorphisms.
case: bH2H => H1 H2.
set T := , _.
apply (H2 T).
case: bH2H => H1 H2.
apply H1.
apply: isomKR.
apply: pres_isom.
apply: Isomorphisms.
case: bH2H => H1 H2.
set T := , _.
apply (H1 T).
case: bH2H => H1 H2.
set T := , _.
by case: (H2 T).

rewrite /=.
apply: Congruence.etrans.
apply/symP; apply: pres_comp.
apply: Congruence.etrans.
apply: pres_equiv.
case: bH21 bH2H=> /=.
case: bH2H => H1 H2.
apply: (H1 _).

do !(apply: Congruence.etrans; first apply: compmA).

case: bH2H.
apply bH2H.
apply: (isomKL bH2H).
rewrite /=.
apply: (isomKL ( bH2H)).
apply: (isomKL (isom_sym bH2H)).
apply: Congruence.etrans; last first.

Check ((domRS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).1
\compm adj.2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))
\compm 'F (domLS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).2 : Mor (F (G (F X)), F _)).
apply: (_ : 
(domRS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).1
\compm adj.2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))
\compm 'F (domLS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).2 == _).
      (domLS2 (@CommaOb _ _ _ (idf _) G _ _ (adj_unit X))).1.
Check (adj.2 (@CommaOb _ _ _ (idf _) G _ _ (adj_unit X))) == (@CommaOb _ _ _ F (idf _) _ _ id).
      (domLS2 
      (, adj_unit X).
apply (_ : (domRS2 (@CommaOb _ _ _ (idf _) G _ _ (adj_unit X))).2 \compm id \compm 'F (domLS2 (@CommaOb _ _ _ (idf _) G _ _ (adj_unit X))).1 == _).
         (domRS2 (@CommaOb _ _ _ (idf _) G _ _ (adj_unit X))).2 \compm id \compm 'F (domLS2 _).1 == _).
apply/symP.
case: (domRS2 _) => ? ? H.
apply: isom_sym.
apply: H.

apply: Congruence.etrans.

rewrite /=.
apply: (_ : ((domRS2 _).1 \compm adj.2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X)))) \compm 'F (domLS2 _).2) == _).
Check (@CommaOb _ _ _ (idf _) G _ _ (adj_unit X)) == (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X)))).
rewrite /=.
Check  (domRS2 _).1 \compm ' F (domLS2 _).2.
  Check ( (, (adj_unit X))).1 

do !(apply: Congruence.etrans; first apply: compmA).
unfold adj_unit.
Check adj_counit _ \compm 'F _.
apply/reflP.
Check adj_counit (F X) \compm ' F (adj_unit X).
Check  
Check '(adj.1) box.
Check (adj_counit (F X) \compm ' F _).
(adj_unit X)
apply: Congruence.etrans; first (do 2!apply: subst_right;
apply/symP; apply: pres_comp).
apply: Congruence.etrans; first (do 2!apply: subst_right;
apply: pres_comp).
apply: Congruence.etrans; first (apply: subst_right; apply/symP; apply: compmA).
Check 
apply: Congruence.etrans; first (apply/symP; apply: compmA)).

do !(apply: Congruence.etrans; first (apply/symP; apply: compmA)).

apply: Congruence.etrans; first (do 2!apply: subst_right).
apply/symP; apply: pres_comp).


pose box :=
  (Pairing (Category.id (G (F X))) (Category.id (F X)) _
   : comma_mor
       (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))
       (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).

Check (adj_counit (F X) \compm ('F id)) ==
(domRS2 _).1 \compm ((adj.2) (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))) \compm 'F (domLS2 _).2.
      (box _).
Check  \compm  \compm 
       mor (adj.2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).
set box :=
  (Pairing
  (('G (snd (bH11 (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))) \compm L _) \compm fst (bH12 _))
  _
  (Congruence.etrans ([eta symP] (compm0 _)) (comp0m _))
   : comma_mor
       (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X)))
       (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F (G (F X)))))).
Check ( \compnf F) X == mor 
Check 
set Gff := (Pairing id ('F id) (Congruence.etrans ([eta symP] (compm0 _)) (comp0m _))
                    
            : comma_mor (, id' A) (, id' A')).
adj.2 
Check (F \compfn adj_unit \
         Check ((adj_counit \compnf F) \compnf G). X ==
                                                   
(adj.2 (
rewrite /=.
apply: Congruence.etrans; last first.
apply (_ : mor (adj.2 (adj.1 (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))) == _).
apply (_ : _ == mor ).
have: (((adj_counit \compnf F) \compm (F \compfn adj_unit)) X == 

  ((adj_counit \compnf F) \compm (F \compfn adj_unit)) X == id X
(* apply: Congruence.etrans; last ( *)
(* apply: (_ : (domRS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).1 \compm  *)
(*             (domRS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).2 == _); *)
(* by case: (domRS2 _) => ? ? []). *)
(* apply: subst_right. *)
(* apply: Congruence.etrans; first apply: compm0. *)
(* apply: Congruence.etrans; first (apply: subst_right; *)
(* apply: (_ : _ == (domRS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).1 \compm  *)
(*                  (domRS2 (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X))))).2); *)
(* apply/symP; by case: (domRS2 _) => ? ? []). *)
(* apply: Congruence.etrans; last (apply/symP; apply: comp0m). *)
(* do !(apply: Congruence.etrans; first (apply/symP; apply: compmA)). *)
(* apply: subst_left. *)
move: ((naturality adj_counit) _ _ ('F (adj_unit X))).
move: ((naturality adj_unit) _ _ ('G (adj_counit (F X)))).

rewrite /=.
move: (snd (naturality bH11 box)).
rewrite /=.
subst box.
unfold adj_unit.
move: (snd (bH11 _ \compm ' (fcom (idf C) G \compf L) box)).
move: (('G (snd (bH11 (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))) \compm L (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))).
rewrite /=.
move: ((fst (bH22 (@CommaOb _ _ _ (idf _) G _ _ (Category.id ((G (F X)))))))
         \compm 
    ('G (snd (bH11 (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))) \compm L (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))).
rewrite /=.
      \compm fst (bH12 _)).
move:(('G (snd (bH11 (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))) \compm L (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))
      \compm fst (bH12 _)).
Check ' (fcom (idf C) G \compf L) box.
apply: Congruence.etrans.
apply: subst_right.
apply: subst_right.
apply: pres_equiv.
apply: subst_right.
apply: subst_left.
apply (_ : _ == snd (bH11 _ \compm ' (fcom (idf C) G \compf L) box)).
apply: subst_left.
apply: pres_equiv.

apply: (_ : 'psnd (bH11 _) == 'psnd (id \compm bH11 _)).
apply: pres_equiv.
apply: comp0m.
apply: Congruence.etrans.
apply: subst_right.
apply: subst_right.
apply: pres_equiv.
apply: subst_right.
apply: subst_left.
apply: subst_left.
apply: pres_equiv.
apply/symP.
rewrite /=.
ofirst (do !apply: subst_right; apply: pres_comp)).

subst box.
rewrite /=.
unfold compfm.
unfold forget_com_mor.
rewrite /= /domLS2 /domRS2 /domLS1 /domRS1.
rewrite /=.
unfold forget_com_mor.
unfold compfm.
rewrite /=.

case: ('(adj.1) ).

rewrite /=.

           (, id' X) (, id' X)).
rewrite /=.
pose id' := @CommaOb _ _ _ F (idf _) _ _ (Category.id (F _)).

case: adj adj2C => [] L R [] [] l1 r1 [] l2 r2 [] l3 r3 [] l4 r4 [] l5 r5.
rewrite /=.
do !(apply: Congruence.etrans; first (do !apply: subst_right; apply: pres_comp)).
apply: Congruence.etrans; first
(do 2!apply: subst_right; apply/symP; apply: compmA).
case: ('(adj.1) fFf).
apply: subst_left.
have: comma_mor (adj.1 (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))
                (@CommaOb _ _ _ (idf _) G _ _ (Category.id (G (F X)))).
case: ('(adj.1) ((Pairing id (' F id) (Congruence.etrans ([eta symP] (compm0 _)) (comp0m _)))
                 : comma_mor (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X)))
                             (@CommaOb _ _ _ F (idf _) _ _ (Category.id (F X))))).

rewrite /domLS2 /domRS2 /domLS1 /domRS1.
case: adj adj2C => L R [] H [] ? ? ? [] ? ? ?.
case: H=> H1 H2.
apply ((Isomorphisms H2 H1)).
  
Lemma adj_pres_limit I
      (d : Fun (I, C)) Ld dm LFd Fdm
      (limd : limit d Ld dm) (limFd : limit (F \compf d) LFd Fdm)
  : cones_map d F Ld == LFd.
Proof.
  have R: Mor ((cones_map d F) Ld, LFd).
   Check dm Ld.
  Check (, (Category.id (G (vertex LFd))) : cones d).
  
  Mor (vertex Ld, G (vertex LFd))
  Check Mor (F (vertex Ld), vertex LFd).
  Check (mor (adj.1 (@CommaOb _ _ _ G (idf _) _ _ (Category.id (G (vertex LFd)))))).
  case: G adj => Go [Gm ? ? ?] ? ?.
  case: F LFd Fdm limFd => Fo [Fm ? ? ?] ? ? LFd Fdm limFd.
  case: LFd Fdm limFd => LFdD [] /= LFd Fdm limFd.
  case: Ld dm limd => LdD [] /= Ld dm limd.
  move=> adj.
  case: adj => [].
  case.
  rewrite /=.
  case.
  [ [/= ? ? f] [fm ???] ??]. [g [gm ???] ??] H /=.
  
   vm_compute.
  rewrite /=.
  move=> adj.
   apply: (Pairing _ pt) => i.
   case: 
   rewrite /=.
  Check mor 
  (* Check  (cones_map (F \compf d) G LFd). *)
  case: (cones_map (F \compf d) G LFd) => dom [] /= map.
  Check map _.
  Check (@CommaOb _ _ _ (G \compf F) (idf _) _ _ map).
  Check (CommaOb map). : Ob (cones (G \compf (F \compf d)))).
  Check comma_mor.
  cones
  Check (Pairing map pt _ : @comma_mor _ _ _ _ _ _ _).
  
  Check (dm \compnf _).
   Check (( \compfn dm)).
  Check 
  Check cones_map (F \compf d) G LFd.
  
  Check (F \compfn (mor Ld)) _.
  Check mor (adj.1 (@CommaOb _ _ _ G (idf _) _ _ (Category.id (G (vertex LFd))))).
  Check mor (adj.2 (@CommaOb _ _ _ (idf _) F _ _ (Category.id (F (vertex Ld))))).
  
  Check mor (adj.1 (@CommaOb _ _ _ G (idf _) _ _ ((comp0f G).1 _ \compm (Category.id (G (vertex LFd)))))).
  Check mor (adj.1 (@CommaOb _ _ _ G (idf _) _ _ ((Category.id (G (vertex LFd)))))).
  Check mor (adj.2 (@CommaOb _ _ _ (idf _) F _ _ ((Category.id (F (vertex Ld))) \compm (comp0f F).1 _))).
                              ((comp0f F).1 _ \compm (Category.id (G (vertex LFd))))))).
  Check (mor (adj.2 (@CommaOb _ _ _ (idf _) F _ _)
                              ((comp0f F).1 _ \compm (Category.id (G (vertex LFd))))))).
  Check (domL LFd).
   rewrite /comma_mor.
            _).
   rewrite /=.
   Check (diag_mor I).
Check 
  Check (F \compfn Ld).
  move: (Fdm (cones_map d F Ld)).
  move=> L.
  have R : comma_mor (, (F \compfn Ld) \compn diagDR I F LdD) (, LFd) .
  
  (, (F \compfn Ld) \compn diagDR I F LdD)
  == (, LFd)
apply: (Pairing _ L).
  case => /= F [] fH.
  heck (Fdm Ld).
  apply: Pairing.
  Check (dm _).1.
  Check (limd _).
  have: cones d.
  rewrite /=.
   apply: CommaOb.
   apply: (NatType _ _ _).
   apply: (NatMixin _).
   move=> a a' f /=.
   rewrite /=.
   rewrite /=.
     NaturalTransformation.
   apply:
   Check (G (vertex LFd)).
  Check dm (G (vertex LFd)).
  Check .
        \compn _.
Check Fdm.
(* have: domR (adj.1 (, (comp0f G).1 (vertex LFd) \compm id)) = G. *)
(* apply: Isomorphisms. *)
have: domR (adj.1 (, (comp0f G).1 (vertex LFd) \compm id)) = G (vertex LFd).
Check (mor (adj.1 (@CommaOb _ _ _ G (idf _) _ _ ((comp0f G).1 _ \compm (Category.id (G (vertex LFd))))))
: Mor (_, F (G _))).
Check 
Check cones_map.
Check dm.
Check (limd _ (dm _)).
case: limd.
case: adj => [[f ? ? ?] [g ? ? ?] fg] /=.
rewrite /=.
  Check (dm (cones_map d F LFd)).
Check ((cones_map (F \compf d) G) LFd).
Check , '(cones_map _ F) (dm Ld).
move: (mor id').
subst id';
rewrite /=.
Check (G (vertex LFd)).
Check ((cones_map d (G \compf F)) Ld).
Check (cones_map (F \compf d) G) .
Check '(cones_map (F \compf d) G) (dm _).
Check LFd.
Check mor id'.
case: adj => L R [H1 H2].
move: (mor (L (id' (vertex LFd)))); subst id'.
move=> /= H.
Check (cones_map (F \compf d) G) LFd.
Check dm 
rewrite /=.

case: L H1 H2 => m ? ? ? H1 H2 /=.
Check dm _.
Check (H : Mor(vertex LFd, _)).
Check (cones_map (F \compf d) G) ((cones_map d F) Ld).
Check ( LFd).
rewrite /=.
move: (fun a => 
Check .
rewrite /=.
Check '(cones_map d F) 
case: (Fdm (cones_map d F Ld)) => /= f [].
rewrite /=.
rewrite equivE.
rewrite /=.
Check dm Ld.
apply: Congruence.etrans; last first.
 apply: vertex_inj.
 apply: limit_is_the_unique.
  Check limit (F \compf d) (F (vertex Ld)).
 apply/reflP.
Check mor (L (id' _)).
    Check domL (@CommaOb _ _ _ G (idf _) _ _ ((comp0f G).1 _ \compm (Category.id (G _)))).
  Check (G \compfn idn _) _.
  Check , 
  idf F \compf G
  Check F \compf G.
  Check 'L id.
  Check (H2.2 \compnf L) _.
Check '(L \compf (R \compf L)) id .
Check (compfA _ _ _).2 _.
Check (H2.2 \compnf L) _ \compm (compfA _ _ _).2 _ \compm (L \compfn H1.1) _ \compm '(L \compf R \compf L) id \compm (H2.2 \compnf L) _.
  Check (H1.1 \compnf R) _.
  Check H2.2 \compnf L.
  Check 'R (H2.2 _).
  Check 
  Check ('(adj.1) id).
  Check (, 'G id).
  Check (, 'G id).
  Check (, '(G \compf F) id).
  Check (fun X => L X).
  Check ('L id).
  Check adj.1.
  Check (adj.1 (, (Category.id _))).
  Check (adj.1 , ('G (Category.id (F _)))).
  Check (fun X => , ('G (Category.id (F X)))).
  Check (fun X => '(adj.2) (Category.id X)).
  
  com (idf D) F
  Check (fun X => adj.2 X).
  Check adj.1.
  Check (fun X => adj.2 (CommaOb (Category.id (G X)))).
  move: 
  rewrite equivE /=.
  
End Adjunction.
