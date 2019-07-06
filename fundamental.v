From mathcomp Require Import all_ssreflect.
Require Import equivalence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Set Printing Universes.

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
Arguments compm {_ _ A B C} _ _ /.
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
Qed.

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
constructor;
(apply: Congruence.etrans; first by apply: compmA);
[ apply: Congruence.etrans; last by apply H11
| apply: Congruence.etrans; last by apply H22 ];
apply subst_right;
(apply/symP; apply: Congruence.etrans; last by apply compmA);
(apply: Congruence.etrans; first (by apply: comp0m));
apply subst_left; by apply/symP.
Defined.
Definition obs_equivMixin := EquivMixin@{u} piso_sym piso_trans piso_refl.
Definition obs_equivType := Eval hnf in EquivType@{u} (Ob C) obs_equivMixin.
End Isomorphism.
End Equivalence.

Module Exports.
Include Notations.
Include Equivalence.
End Exports.
End Category.
Export Category.Exports.

Section Map.
Variable C : category.
Structure map_ob :=
  MapOb {
    total_dom : Ob C;
    total_cod : Ob C;
    total_mor :> Mor (total_dom, total_cod)
  }.
Local Notation td := total_dom.
Local Notation tc := total_cod.
Local Notation tm := total_mor.
Import PartialEquiv.
Definition map_mor f g :=
  @pairing Mor(td f, td g) Mor(tc f, tc g)
           (fun d c => c \compm tm f == tm g \compm d).
Definition total_op f g (h i : map_mor f g) :=
  prod (h.1 == i.1) (h.2 == i.2).

Lemma total_reflP f g : Equivalence.reflexivity (@total_op f g).
Proof. move=> [A B h]. by apply: pair; apply/reflP. Qed.

Lemma total_symP f g : Equivalence.symmetricity (@total_op f g).
Proof. move=> [hA hB h] [jA jB j] [H1 H2]; by apply: pair; apply/symP. Qed.

Lemma total_transP f g : Equivalence.transitivity (@total_op f g).
Proof.
move=> [hA hB h] [jA jB j] [iA iB i] [H1 H2] [H'1 H'2].
apply: pair.
 by apply/transP; first apply: H1.
by apply/transP; first apply: H2.
Qed.
Definition total_equivMixin f g := EquivMixin (@total_symP f g) (@total_transP f g) (@total_reflP f g).

Definition map_comp f g h (j : map_mor g h) (i : map_mor f g) : map_mor f h.
  apply (Pairing (j.1 \compm i.1) (j.2 \compm i.2)).
  case: i => i1 i2 fg.
  case: j => j1 j2 gh.
  apply: Congruence.etrans; first apply: compmA.
  apply: Congruence.etrans; first (apply: subst_right; apply fg).
  apply: Congruence.etrans; first (apply/symP; apply: compmA).
  apply: Congruence.etrans; first (apply: subst_left; apply gh).
  apply: Congruence.etrans; first apply: compmA.
  apply/reflP.
Defined.

Definition map_id f : map_mor f f.
  apply (Pairing id id).
  apply: Congruence.etrans; last apply: compm0.
  apply/symP; apply: comp0m.
Defined.

Lemma map_compmA : @Category.associativity_of_morphisms _ _ map_comp total_equivMixin.
Proof.
move => /= f g h i [j1 j2 jH] [k1 k2 kH] [l1 l2 lH].
by apply: pair; apply: compmA.
Defined.
Lemma map_compm0 : @Category.identity_morphism_is_right_identity _ _ map_id map_comp total_equivMixin.
Proof.
move => /= f g h.
by apply: pair; apply: compm0.
Defined.
Lemma map_comp0m : @Category.identity_morphism_is_left_identity _ _ map_id map_comp total_equivMixin.
Proof.
move => /= f g h.
by apply: pair; apply: comp0m.
Defined.
Lemma map_comp_left : @Category.compatibility_left _ _ map_comp total_equivMixin.
Proof.
move => ? ? ? [f1 f2 Hf] [f'1 f'2 Hf'] [g1 g2 Hg] [ff'1 ff'2].
by apply: pair; apply: comp_left.
Defined.
Lemma map_comp_right : @Category.compatibility_right _ _ map_comp total_equivMixin.
Proof.
move => ? ? ? [f1 f2 Hf] [f'1 f'2 Hf'] [g1 g2 Hg] [ff'1 ff'2].
by apply: pair; apply: comp_right.
Defined.
Canonical map_catMixin := Eval hnf in CatMixin map_compmA map_compm0 map_comp0m map_comp_left map_comp_right.
Canonical map_catType := Eval hnf in CatType map_ob map_catMixin.
End Map.
Notation Map := map_catType.
Notation "` f" := (MapOb f : Map _) (at level 1).
Notation dom := total_dom.
Notation cod := total_cod.

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
End Exports.
End Functor.
Export Functor.Exports.

Module NaturalTransformation.
Section Axioms.
Universes u u'.
Import PartialEquiv.
Variable C : category@{u}.
Variable D : category@{u'}.
Variables F G : (functor@{u u'} C D).
Variable map : forall X, Mor (F X, G X).
Arguments map {X}.
Definition naturality_axiom :=
  forall A A' (f : Mor (A, A')), map \compm 'F f == 'G f \compm map.
End Axioms.

Structure mixin_of@{u u'} (C : category@{u}) (D : category@{u'}) F G natural_map :=
  Mixin { naturality : @naturality_axiom C D F G natural_map }.

Local Notation class_of := mixin_of (only parsing).

Section ClassDef.
Universes u u'.
Variable dom : category@{u}.
Variable cod : category@{u'}.
Structure type domf codf := Pack { map; _ : @class_of@{u u'} dom cod domf codf map; _ : Type@{u'} }.
Variables (domfT codfT : functor@{u u'} dom cod) (cT : type domfT codfT)
          (mapT : forall X , Mor(domfT X, codfT X)).
Definition class := let: Pack _ c _ := cT return @class_of dom cod domfT codfT (map cT) in c.
Definition pack c := @Pack domfT codfT mapT c (forall X, Mor(domfT X, codfT X)).
End ClassDef.

Module Notations.
Definition app_nat dom cod f g (n : @type dom cod f g) := map n.
Arguments app_nat /.
Notation "'Nat' ( M , N )" := (@type _ _ M N) (at level 5).
Coercion app_nat: type >-> Funclass.
Notation natural_transformation := type.
Notation NatMixin := Mixin.
Notation NatType F G m := (@pack _ _ F G _ m).
Definition naturality' C D F G N := @naturality C D F G _ (class N).
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
Lemma idn_map_naturality : naturality_axiom idn_map.
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
Lemma compnf_naturality : @naturality_axiom C E (F \compf H) (G \compf H) compnf_map.
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

Module Limit.
Section Axioms.
Variables I C : category.
Variable F : Fun (I, C).
Import PartialEquiv.
Notation solution_of_diagram L :=
  (sigT (fun (s : (forall A, Mor (L, F A))) =>
         forall A B (f : Mor (A, B)), ('F f) \compm (s A) == (s B))).
Local Definition proj1_sigT A P (t : sigT P) :=
  match t with
  | existT x _ => x : A
  end.
Local Definition proj2_sigT A P (t : sigT P) :=
  match t as e return P (@proj1_sigT A P e) with
  | existT x y => y
  end.
Definition morphism_of_solutions L L'
      (sL : solution_of_diagram L) (sL' : solution_of_diagram L') :=
    sigT (fun l => forall A, (proj1_sigT sL' A) == (proj1_sigT sL A) \compm l).
Definition universality_axiom L
      (sL : solution_of_diagram L)
      (u : (forall L' (sL' : solution_of_diagram L'), morphism_of_solutions sL sL')) :=
  (forall L' u' (sL' : solution_of_diagram L'),
      (forall A, (proj1_sigT sL' A) == (proj1_sigT sL A) \compm u') -> proj1_sigT (u L' sL') == u').
End Axioms.
Module Exports.
Structure limit I C F :=
  Limit {
      limit_object :> _;
      canonical_solution : _;
      universal_morphism : _;
      universality : @universality_axiom I C F limit_object canonical_solution universal_morphism;
    }.

Notation "- L" := (canonical_solution L).
Import PartialEquiv.
Local Lemma add_loop (I C : category)  (F : Fun (I, C)) (limL : limit F) (f : Mor (limL, limL)) :
  let sL := canonical_solution limL in
  (forall (A B : Ob I) (g : Mor (A, B)),
    ('F g) \compm (proj1_sigT sL A \compm f) == (proj1_sigT sL B \compm f)) ->
    (forall A : Ob I, proj1_sigT sL A == proj1_sigT sL A \compm f) ->
  f == id.
Proof.
case: limL f => L sL uL pL f /= H H'.
have: proj1_sigT (uL L sL) == f.
apply pL, H'.
have: proj1_sigT (uL L sL) == id.
apply pL.
move => A.
apply compm0.
move => H1 H2.
apply: Congruence.etrans; last apply: H1.
by apply/symP.
Defined.
  
Lemma limit_is_the_unique (I C : category) (F : Fun (I, C)) :
  forall (limL : limit F) (limL' : limit F),
    @equiv_op (obs_equivType C) (limit_object limL) (limit_object limL').
Proof.
move => limL limL' /=.
apply: Pairing.
set u := (@universal_morphism _ _ _ limL' _ (canonical_solution limL)).
set u' := (@universal_morphism _ _ _ limL _ (canonical_solution limL')).
apply (@Isomorphisms _ _ _ (proj1_sigT u) (proj1_sigT u')).
  apply (@add_loop I C F limL).
  move => A B g /=.
  apply/symP.
  apply: Congruence.etrans; last apply compmA.
  apply subst_left.
  apply/symP.
  apply (proj2_sigT (canonical_solution limL)).
 move => A.
 apply: Congruence.etrans; last apply compmA.
 apply: Congruence.etrans; first apply (proj2_sigT u A).
 apply subst_left.
 apply: Congruence.etrans; first apply (proj2_sigT u' A).
 apply/reflP.
apply (@add_loop I C F limL').
 move => A B g /=.
 apply/symP.
 apply: Congruence.etrans; last apply compmA.
 apply subst_left.
 apply/symP.
 apply (proj2_sigT (canonical_solution limL')).
move => A.
apply: Congruence.etrans; last apply compmA.
apply: Congruence.etrans; first apply (proj2_sigT u' A).
apply subst_left.
apply: Congruence.etrans; first apply (proj2_sigT u A).
apply/reflP.
Defined.
End Exports.
End Limit.
Export Limit.Exports.

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
Section Isomorphism.
Inductive natural_isomorphisms@{u u'}
          (C : category@{u})
          (D : category@{u'})
          (F G : functor@{u u'} C D)
          (N : natural_transformation@{u u'} F G)
          (M : natural_transformation@{u' u} G F)
: Type@{max(u,u')} :=
  NaturalIsomorphisms :
    (forall X, isomorphisms@{u'} (N X) (M X)) -> 
    natural_isomorphisms N M.

Arguments natural_isomorphisms {_ _ _ _} _ _.
Arguments NaturalIsomorphisms {_ _ _ _} _ _ _.

Universes u u' u''.
Constraint u <= u''.
Constraint u' <= u''.
Variable C : category@{u}.
Variable D : category@{u'}.
Local Notation pniso :=
  (fun F G => (pairing (@natural_isomorphisms C D F G))).
Lemma pniso_sym : Equivalence.symmetricity pniso.
Proof.
move => ? ?.
move=> [N M] [H]; apply (Pairing M N).
apply NaturalIsomorphisms => X.
case: (H X) => H1 H2; by constructor.
Defined.

Lemma pniso_refl : Equivalence.reflexivity pniso.
Proof.
move => X; apply: Pairing.
apply (@NaturalIsomorphisms _ _ _ _ (idn X) (idn X)) => x.
apply: Isomorphisms => /=;
apply/symP; by apply comp0m.
Defined.

Lemma pniso_trans : Equivalence.transitivity pniso.
Proof.
move => ? ? ?.
move => [N1 M1] [H1] [N2 M2] [H2];
apply: Pairing;
apply (@NaturalIsomorphisms _ _ _ _ (N2 \compn N1) (M1 \compn M2)) => /= X;
case: (H1 X) => /= [H11 ?];
case: (H2 X) => /= [? H22];
apply: Isomorphisms => /=;
(apply: Congruence.etrans; first by apply: compmA);
[ apply: Congruence.etrans; last by apply H11
| apply: Congruence.etrans; last by apply H22 ];
apply subst_right => /=;
(apply/symP; apply: Congruence.etrans; last by apply compmA);
(apply: Congruence.etrans; first (by apply: comp0m));
apply subst_left; by apply/symP.
Defined.
Definition funs_equivMixin := Eval hnf in EquivMixin pniso_sym pniso_trans pniso_refl.
Definition funs_equivType := Eval hnf in EquivType (functor@{u u'} C D) funs_equivMixin.
End Isomorphism.

Universes u u' u'' u'''.
Constraint u <= u'''.
Constraint u' <= u'''.
Constraint u'' <= u'''.
Lemma cats_compmA : @Category.associativity_of_morphisms@{u'''} _ _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => /= C D E F h i j.
  set L := NatType _ _ (@NatMixin _ _ ((j \compf i) \compf h) (j \compf (i \compf h)) (idn _) (idn_map_naturality _)).
  set R := NatType _ _ (@NatMixin _ _ (j \compf (i \compf h)) ((j \compf i) \compf h) (idn _) (idn_map_naturality _)).
  apply: Pairing.
  apply (@NaturalIsomorphisms _ _ _ _ L R);
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.
Lemma cats_compm0 : @Category.identity_morphism_is_right_identity@{u'''} category _ idf compf@{u u' u''} funs_equivMixin.
Proof.
  move => /= C D f.
  set L := NatType _ _ (@NatMixin _ _ f (f \compf idf _) (idn _) (idn_map_naturality _)).
  set R := NatType _ _ (@NatMixin _ _ (f \compf idf _) f (idn _) (idn_map_naturality _)).
  apply: Pairing;
  apply (@NaturalIsomorphisms _ _ _ _ L R).
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: comp0m.
Defined.

Lemma cats_comp0m : @Category.identity_morphism_is_left_identity@{u'''} category _ idf compf@{u u' u''} funs_equivMixin.
Proof.
  move => /= C D f.
  set L := NatType _ _ (@NatMixin _ _ f (idf _ \compf f) (idn _) (idn_map_naturality _)).
  set R := NatType _ _ (@NatMixin _ _ (idf _ \compf f) f (idn _) (idn_map_naturality _)).
  apply: Pairing;
  apply (@NaturalIsomorphisms _ _ _ _ L R);
  move => X; apply: Isomorphisms => /=;
  apply/symP; by apply: compm0.
Defined.

Lemma cats_comp_left : @Category.compatibility_left@{u'''} category _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => ? ? ? f f' g [N M [H]].
  apply: (Pairing 
            (NatType _ _ (@NatMixin _ _ (g \compf f) (g \compf f')
                                    (g \compfn N) (compfn_naturality _ _)))
            (NatType _ _ (@NatMixin _ _ (g \compf f') (g \compf f)
                                    (g \compfn M) (compfn_naturality _ _)))).
  apply: NaturalIsomorphisms => X.
  apply: Isomorphisms; case: (H X) => /= H1 H2;
  (apply: Congruence.etrans;
   first by (apply/symP; apply pres_comp));
  (apply: Congruence.etrans; last by apply id_id);
  by apply: pres_equiv.
Defined.

Lemma cats_comp_right : @Category.compatibility_right@{u'''} category _ compf@{u u' u''} funs_equivMixin.
Proof.
  move => ? ? ? f g g' [N M] [H].
  set L := NatType _ _ (@NatMixin _ _ (g \compf f) (g' \compf f)
                                  (N \compnf f) (compnf_naturality _ _)).
  set R := NatType _ _ (@NatMixin _ _ (g' \compf f) (g \compf f)
                                  (M \compnf f) (compnf_naturality _ _)).
  apply: Pairing.
  apply (@NaturalIsomorphisms _ _ _ _ L R) => X;
  apply: Isomorphisms; by case: (H (f X)).
Defined.
Canonical cats_catMixin := Eval hnf in CatMixin cats_compmA cats_compm0 cats_comp0m cats_comp_left cats_comp_right.
Canonical cats := Eval hnf in CatType@{u'''} category cats_catMixin.
Canonical cats_obs_equivType := Eval hnf in EquivType category (obs_equivMixin cats).
Canonical obs_equivType.
End Cats.
Arguments compm : simpl never.
Section FunPrfK.
Import PartialEquiv.
Lemma fun_prfK C D (F G : Fun(C, D))
  (L : forall A : Ob C, Mor(F A, G A))
  (R : forall A : Ob C, Mor(G A, F A))
  (Ln : forall f : Map C,
      (L dom f) \compm 'F f == 'G f \compm (L cod f)) :
  
      ->
      == (R cod f) \compm 'G f
      isomorphisms (L f) (R f)) -> F == G.
Proof.
  move=> H.
  have Nn : NaturalTransformation.naturality_axiom (fun _ => (L ` id).1).
  move=> A A' f /=.
  move: (R ` f) (L ` f) (H ` f)
  => [/= r1 r2 r12] [/= l1 l2 l12] [[/= rl1 rl2] [/= lr1 lr2]].
  /=.
  case: (H ` f) => /=.
  move: (H ` f).1 => /=.
  Check 
  case: (H ` f) => [[/= fgd fgc] fg [/= gfd gfc] gf] [[/= did cid] [/= did' cid']].
  
Variable C : category.
Variable f g : Map C.
Variable H : (f == g).
Goal False.
  move=> H.
  have: (H ` (Category.id A)).1.1 == (H `f).1.1.
  case: (H ` (Category.id A)) => [[/= f1AA g1AA H1AA] [/= f2AA g2AA H2AA]] [[/= S11 S12] [/= S21 S22]].
  case: (H ` f) => [[/= f1AAf g1AAf H1AAf] [/= f2AAf g2AAf H2AAf]] [[/= S11f S12f] [/= S21f S22f]].
  
  case: (H ` (Category.id A)) => /=.
  intros.
  rewrite equivE /=.
  case: (H 
  subst H.
  
  About Isomorphisms.
  Check (Pairing (@Isomorphisms _ _ _ (H `f).1.1 (H ` (Category.id A)).1.2 _ _) _).
            _ _ (fun _ _ => (@Isomorphisms _ _ _ (H `f).1.1 _ _))).
  
  Check (Pairing
           (Isomorphisms S21 _)
           _
            _).
  
           (Isomorphisms S21 _)
            _).
              _ _ _ (H `f).1.2 _ _)
  
  
  Check (H `f).1.1.
  apply: Isomorphisms.
  apply S22.
  Check (H `f).1.2.
  apply: (@Isomorphisms _ _ _ (H `f).1.2 _ _).
  About Isomorphisms.
            (Pairing 
               (H `f).2 (H ` (Category.id A)).2 _)
         ).
  rewrite equivE /=.
  apply: pair.
  rewrite /=.
                           S1.
  rewrite /= equivE.
  case: (H A A id) => /= 
  case: (H A' A' id) => /= [[f1AA' g1AA' [H1AA'1 H1AA'2]] [f2AA' g2AA' [H2AA'1 H2AA'2]]] S2.
  
  case: (H A A id).
  rewrite equivE /=.
  
  apply: Congruence.etrans; first apply: comp0m.
  apply: Congruence.etrans; first apply: subst_left.
  apply/symP; apply: H1AA'2.
  apply: Congruence.etrans.
  apply: compmA.
  apply: Congruence.etrans.
  apply: subst_right. apply/symP; apply: compmA.
  apply: Congruence.etrans.
  apply: subst_right. 
  apply: subst_left.
  apply: H1AA'1.
  apply: Congruence.etrans.
  apply: subst_right. 
  apply/symP; apply: comp0m.
  
  case: (H A A' f) => /= [[f1 g1 [H11 H12]] [f2 g2 [H21 H22]]] f2f1.
  
  case: H1AA => H1AA1 H1AA2.
  move: S3 => /=.
  move: f1AA f1AA' S1 S2 H1AA'1 H1AA'2 H1AA => /=.
  apply: subst_left.
  
  case: (H A A' f).
  case=>[f1AA' g1AA' H1AA'].
  case=>[f2AA' g2AA' H2AA'].
  rewrite equivE /=.
  
  
  
  
  apply/symP; 
  rewrite /=.
  move=> 
  
  intros.
  case: H1.
  case:(H A' A' (g1 \compm f1)).
                       ? ? H'.
  apply: Congruence.etrans; last first.
  apply H'.
  
  apply/symP;
  a
  apply: Congruence.etrans; last (apply/symP; apply: compm0).
  apply: Congruence.etrans; last (apply: subst_right; apply: HKr).
  apply: Congruence.etrans; last apply: compmA.
  case: (H A A' f).
  move=> H1 H2.
  case: H1 => /= f1 g1 [Hf1 Hg1].
  case: H2 => /= f2 g2 [Hf2 Hg2].
  rewrite !equivE /=.
  move=> H'.
  apply: Congruence.etrans.
  apply H'.
  
  rewrite equivE /=.
  set M := (fun X => (H X X id).2.2).
  case: (H A' A' id).
  move=> H1' H2' /=.
  case => ? ?.
  case.
  case.
  rewrite /=.
  subst N.
  rewrite /=.
  apply: (Pairing (NatType _ _ (@NatMixin _ _ _ _ (fun X => (H X X id).1.1) _))
                  (NatType _ _ (@NatMixin _ _ _ _ (fun X => (H X X id).1.2) _))).
  apply: Isomorphisms.
  move=> X.
  case: 
  case=> f1 g1 [H11 H12].
  case=> f2 g2 [H21 H22].
  rewrite /=.

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
End Down.
End Down.

Definition down C : Fun(C, Down.down C).
apply: (FunType _ _ (@FunMixin _ _ _ (@Down.get_down_mor C) _ _ _)).
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros.
move=> ? ? ? ? H; by rewrite equivE /= Equivalence.downK.
Defined.
Definition up C : functor (Down.down C) C.
apply: (@Functor.pack (Down.down C) C _).
apply: (@FunMixin _ _ (@Down.get_up C) (@Down.get_up_mor C) _ _ _).
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros; move=> ?; intros; apply/reflP.
case: C => ? [] //=; intros.
move=> ? ? ? ?; by rewrite equivE /= Equivalence.downK.
Defined.
Lemma down_upK C : down C \compf up C == idf (Down.down C).
Proof.
  case: C => ? [] /=.
  intros.
  rewrite equivE /=.
  apply: Pairing.
  apply: Isomorphisms.
  apply/symP.
  apply: compm0.
  apply (Pairing (@idn (Down.down _)) _ _).
  vm_compute.
  apply (Pairing (@idn (Down.down C)) _ _).
  rewrite /=.

Coercion Category.down : category >-> category.