Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Import Typed.

Definition Annotation := Types.Annotation.
Definition info := Types.info.

Inductive MethodPrototype_pre_t :=
| Constructor (_: list Annotation) (_: Types.P4String) (_: list Parameter')
| AbstractMethod (_: list Annotation) (_: Type') (_: Types.P4String)
                 (_: list Types.P4String) (_: list Parameter')
| Method (_: list Annotation) (_: Type') (_: Types.P4String) (_: list Types.P4String)
         (_: list Parameter').

Definition MethodPrototype := info MethodPrototype_pre_t.

Inductive KeyValue_pre_t :=
  MkKeyValue_pre_t: Types.P4String -> unit -> KeyValue_pre_t
with KeyValue :=
  MkKeyValue: info KeyValue_pre_t -> KeyValue
with Expression_pre_t :=
| True'
| False'
| Int'' (_: Types.P4Int)
| String'' (_: Types.P4String)
| Name (_: Types.name)
| ArrayAccess (_: Expression) (_: Expression)
| BitStringAccess (_: Expression) (_: Z) (_: Z)
| List'' (_: list Expression)
| Record'' (_: list KeyValue)
| UnaryOp (_: Types.Op_uni) (_: Expression)
| BinaryOp (_: Types.Op_bin) (_: (Expression * Expression))
| Cast (_: Type') (_: Expression)
| TypeMember (_: Types.name) (_: Types.P4String)
| ErrorMember (_: Types.P4String)
| ExpressionMember (_: Expression) (_: Types.P4String)
| Ternary (_: Expression) (_: Expression) (_: Expression)
| FunctionCall (_: Expression) (_: list Type') (_: list (option Expression))
| NamelessInstantiation (_: Type') (_: list Expression)
| DontCare
| Mask (_: Expression) (_: Expression)
| Range (_: Expression) (_: Expression)
with Expression_typed_t :=
  MkExpression_typed_t (_: Expression_pre_t) (_: Type') (_: direction)
with Expression := MkExpression (_: info Expression_typed_t).

Inductive Match_pre_t :=
| DontCare'
| Expression' (_: Expression).

Inductive Match_typed_t :=
  MkMatch_typed_t: Match_pre_t -> Type' -> Match_typed_t.

Definition Match := info Match_typed_t.

Inductive Table_pre_action_ref :=
  MkTable_pre_action_ref (_: list Annotation) (_: Types.name)
                         (_: list (option Expression)).
Inductive Table_typed_action_ref :=
  MkTable_typed_action_ref (_: Table_pre_action_ref) (_: Typed.Type').
Definition Table_action_ref := info Table_typed_action_ref.
Inductive Table_pre_key :=
  MkTable_pre_key (_: list Annotation) (_: list Expression) (_: Types.P4String).
Definition Table_key := info Table_pre_key.
Inductive Table_pre_entry :=
  MkTable_pre_entry (_: list Annotation) (_: list Match) (_: Table_action_ref).
Definition Table_entry := info Table_pre_entry.
Inductive Table_pre_property :=
  MkTable_pre_property (_: list Annotation) (_: bool) (_: Types.P4String)
                       (_: Expression).
Definition Table_property := info Table_pre_property.

Inductive Statement_pre_switch_label :=
| Default
| Name' (_: Types.P4String).
Definition Statement_switch_label := info Statement_pre_switch_label.

Inductive Statement_pre_switch_case :=
| Action (_: Statement_switch_label) (_: Block)
| FallThrough (_: Statement_switch_label)
with Statement_switch_case :=
  MkStatement_switch_case (_: info Statement_pre_switch_case)
with Statement_pre_t :=
| MethodCall (_: Expression) (_: list Type') (_: list (option Expression))
| Assignment (_: Expression) (_: Expression)
| DirectApplication (_: Type') (_: list Expression)
| Conditional (_: Expression) (_: Statement)(_: option Statement)
| BlockStatement (_: Block)
| Exit
| EmptyStatement
| Return (_: option Expression)
| Switch (_: Expression) (_: list Statement_switch_case)
| DeclarationStatement (_: Declaration)
with Statement_typed_t :=
  MkStatement_typed_t (_: Statement_pre_t) (_: StmType)
with Statement :=
  MkStatement (_: info Statement_typed_t)
with Block :=
  MkBlock (_: unit)
with Declaration :=
  MkDeclaration (_: unit).
