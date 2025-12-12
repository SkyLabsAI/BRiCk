Require Import bluerock.prelude.base.
Require Import bluerock.prelude.error.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.mcore.
Require Export bluerock.lang.cpp.syntax.namemap.

(** ** Template pre-instances *)
(**
A template file maps the symbol or type name of a template
instantiation (bound in a translation unit) to a _template
pre-instance_ comprising the instance's template name (bound in a
template file) and arguments.
*)
Definition temp_name : Set := name.

Section tpreinst.
  (* TODO: this type probably does not need to be parametric in [lang.t]
     The only meaningful instantation is [lang.cpp]
   *)
  Record tpreinst : Set := TPreInst {
    tpreinst_name : temp_name;
    tpreinst_args : list temp_arg;
  }.

  #[global] Instance tpreinst_inhabited : Inhabited tpreinst.
  Proof. solve_inhabited. Qed.

  #[global] Instance tpreinst_eq_dec : EqDecision tpreinst.
  Proof. solve_decision. Defined.
End tpreinst.
Add Printing Constructor tpreinst.

(** ** Template instances *)
Section tinst.
  #[local] Set Universe Polymorphism.
  #[local] Set Polymorphic Inductive Cumulativity.
  #[local] Unset Auto Template Polymorphism.
  Universe uV.
  Context {V : Type@{uV}}.

  Record tinst : Type@{uV} := TInst {
    tinst_params : list temp_param;
    tinst_args : list temp_arg;
    tinst_value : V;
  }.

  #[global] Instance tinst_inhabited `{!Inhabited V} : Inhabited tinst.
  Proof. solve_inhabited. Qed.

  #[global] Instance tinst_eq_dec
      `{!EqDecision V} :
    EqDecision tinst.
  Proof. solve_decision. Defined.
End tinst.
Add Printing Constructor tinst.
#[global] Arguments tinst : clear implicits.
#[global] Arguments TInst {_} _ _ & _ : assert.

Require Import bluerock.lang.cpp.syntax.translation_unit.

(** ** Templated values *)
Section template.
  #[local] Set Universe Polymorphism.
  #[local] Set Polymorphic Inductive Cumulativity.
  #[local] Unset Auto Template Polymorphism.
  Universe uV.
  Context {V : Type@{uV}}.

  Record template : Type@{uV} := Template {
    template_params : list Mtemp_param;
    template_value : V;
  }.

  #[global] Instance template_inhabited `{!Inhabited V} : Inhabited template.
  Proof. solve_inhabited. Qed.

  #[global] Instance template_eq_dec `{!EqDecision V} :
    EqDecision template.
  Proof. solve_decision. Defined.
End template.
Add Printing Constructor template.
#[global] Arguments template : clear implicits.
#[global] Arguments Template {_} _ & _ : assert.

#[universes(polymorphic)]
Section template.
  Import UPoly.

  #[global] Instance template_fmap : FMap template := fun A B f t =>
    Template t.(template_params) (f t.(template_value)).

  #[global] Instance template_traverse : Traverse template := fun F _ _ _ A B f t =>
    Template t.(template_params) <$> f t.(template_value).
End template.

Notation Mtpreinst := tpreinst (only parsing).
Notation Mtinst := tinst (only parsing).
Notation MUnion := Union (only parsing).
Notation MStruct := Struct (only parsing).
Notation MFunctionBody := FunctionBody (only parsing).
Notation MFunc := Func (only parsing).
Notation MMethod := Method (only parsing).
Notation MCtor := Ctor (only parsing).
Notation MDtor := Dtor (only parsing).
Notation MObjValue := ObjValue (only parsing).
Notation MGlobDecl := GlobDecl (only parsing).
Notation MGlobalInit := GlobalInit (only parsing).
Notation MGlobalInitializer := GlobalInitializer (only parsing).
Notation MInitializer := Initializer (only parsing).
Notation MMember := Member (only parsing).
Notation MInitializerBlock := InitializerBlock (only parsing).
Notation Mfield_name := field_name.t (only parsing).
Notation MInitPath := InitPath (only parsing).

(** ** Template TUs *)
(**
Template TUs house all templated code in a translation unit and relate
non-templated code induced by template application to the applied
template and its arguments.
*)
Definition Msymbol_table : Type := TM.t (template MObjValue).
Definition Mtype_table : Type := TM.t (template MGlobDecl).
Definition Malias_table : Type := TM.t (template Mtype).
Definition Minstance_table : Type := NM.t Mtpreinst.
Record Mtranslation_unit : Type := {
  msymbols : Msymbol_table;
  mtypes : Mtype_table;
  maliases : Malias_table;	(* we eschew <<Gtypedef>> for now *)
  minstances : Minstance_table
}.
