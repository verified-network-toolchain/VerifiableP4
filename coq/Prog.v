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
  MkKeyValue_pre_t: Types.P4String -> Expression -> KeyValue_pre_t
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

Inductive Declaration_pre_field :=
  MkDeclaration_pre_field (_: list Annotation) (_: Type') (_: Types.P4String).
Definition Declaration_field := info Declaration_pre_field.

Definition Value_loc := string.

Inductive Value_vtable :=
  ValVTable: string -> list Table_pre_key -> list Table_action_ref ->
             Table_action_ref -> list Table_pre_entry -> Value_vtable.

Inductive Statement_pre_switch_case :=
| Action' (_: Statement_switch_label) (_: Block)
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
with Block_pre_t :=
  MkBlock_pre_t (_: list Annotation) (_: list Statement)
with Block :=
  MkBlock (_: info Block_pre_t)
with Parser_pre_case :=
  MkParser_pre_case (_: list Match) (_: Types.P4String)
with Parser_case :=
  MkParser_case (_: info Parser_pre_case)
with Parser_pre_transition :=
| Direct (_: Types.P4String)
| Select (_: list Expression) (_: list Parser_case)
with Parser_transition :=
  MkParser_transition (_: info Parser_pre_transition)
with Parser_pre_state :=
  MkParser_pre_state (_: list Annotation) (_: Types.P4String) (_: list Statement)
                     (_: Parser_transition)
with Parser_state :=
  MkParser_state (_: info Parser_pre_state)
with Declaration_pre_t :=
| Constant (_: list Annotation) (_: Type') (_: Types.P4String) (_: Value_value)
| Instantiation (_: list Annotation) (_: Type') (_: list Expression)
                (_: Types.P4String) (_: option Block)
| Parser (_: list Annotation) (_ : Types.P4String) (_: list Types.P4String)
         (_: list Parameter') (_: list Parameter') (_: list Declaration)
         (_: list Parser_state)
| Control (_: list Annotation) (_: Types.P4String) (_: list Types.P4String)
          (_: list Parameter') (_: list Parameter') (_: list Declaration)
          (_: Block)
| Function' (_: Type') (_: Types.P4String) (_: list Types.P4String)
            (_: list Parameter') (_: Block)
| ExternFunction (_: list Annotation) (_: Type') (_: Types.P4String)
                 (_: list Types.P4String) (_: list Parameter')
| Variable' (_: list Annotation) (_: Type') (_: Types.P4String)
            (_: option Expression)
| ValueSet (_: list Annotation) (_: Type') (_: Expression) (_: Types.P4String)
| Action (_: list Annotation) (_: Types.P4String) (_: list Parameter')
         (_: list Parameter') (_: Block)
| Table (_: list Annotation) (_: Types.P4String) (_: list Table_key)
        (_: list Table_action_ref) (_: option (list Table_entry))
        (_: option Table_action_ref) (_: option Types.P4Int)
        (_: list Table_property)
| Header (_: list Annotation) (_: Types.P4String) (_: list Declaration_field)
| HeaderUnion (_: list Annotation) (_: Types.P4String) (_: list Declaration_field)
| Struct (_: list Annotation) (_: Types.P4String) (_: list Declaration_field)
| Error (_: list Types.P4String)
| MatchKind (_: list Types.P4String)
| Enum (_: list Annotation) (_: Types.P4String) (_: list Types.P4String)
| SerializableEnum (_: list Annotation) (_: Type') (_: Types.P4String)
                   (_: list (Types.P4String * Expression))
| ExternObject (_: list Annotation) (_: Types.P4String) (_: list Types.P4String)
               (_: list MethodPrototype)
| TypeDef (_: list Annotation) (_: Types.P4String) (_: (Type' + Declaration))
| NewType (_: list Annotation) (_: Types.P4String) (_: (Type' + Declaration))
| ControlType (_: list Annotation) (_: Types.P4String) (_: list Types.P4String)
              (_: list Parameter')
| ParserType (_: list Annotation) (_: Types.P4String) (_: list Types.P4String)
             (_: list Parameter')
| PackageType (_: list Annotation) (_: Types.P4String) (_: list Types.P4String)
              (_: list Parameter')
with Declaration :=
  MkDeclaration (_: info Declaration_pre_t)
with Value_value :=
| VNull
| VBool (_: bool)
| VInteger (_: Z)
| VBit (_: Z) (_: Z)
| VInt (_: Z) (_: Z)
| VVarbit (_: Z) (_: Z) (_: Z)
| VString (_: string)
| VTuple (_: list Value_value)
| VRecord (_: list (string * Value_value))
| VSet (_: Value_set)
| VError (_: string)
| VMatchKind (_: string)
| VFun (_: Env_EvalEnv) (_: list Parameter') (_: Block)
| VBuiltinFun (_: string) (_: Value_lvalue)
| VAction (_: Env_EvalEnv) (_: list Parameter') (_: Block)
| VStruct (_: list (string * Value_value))
| VHeader (_: list (string * Value_value)) (_: bool)
| VUnion (_: list (string * Value_value))
| VStack (_: list Value_value) (_: Z) (_: Z)
| VEnumField (_: string) (_: string)
| VSenumField (_: string) (_: string) (_: Value_value)
| VSenum (_: list (string * Value_value))
| VRuntime (_: Value_loc) (_: string)
| VParser (_: Value_vparser)
| VControl (_: Value_vcontrol)
| VPackage (_: list Parameter') (_: list (string * Value_loc))
| VTable (_: Value_vtable)
| VExternFun (_: string) (_: option (Value_loc * string)) (_: list Parameter')
| VExternObj (_: list (string * list Parameter'))
with Value_set :=
| SSingleton (_: Z) (_: Z)
| SUniversal
| SMask (_: Value_value) (_: Value_value)
| SRange (_: Value_value) (_: Value_value)
| SProd (_: list Value_set)
| SLpm (_: Value_value) (_: Z) (_: Value_value)
| SValueSet (_: Value_value) (_: list (list Match)) (_: list Value_set)
with Value_pre_lvalue :=
| LName (_: Types.name)
| LMember (_: Value_lvalue) (_: string)
| LBitAccess (_: Value_lvalue) (_: Z) (_: Z)
| LArrayAccess (_: Value_lvalue) (_: Value_value)
with Value_lvalue :=
  MkValue_lvalue (_: Value_pre_lvalue) (_: Type')
with Value_vparser :=
  MkValue_vparser (_: Env_EvalEnv) (_: list Parameter') (_: list Parameter')
                  (_: list Declaration) (_: list Parser_state)
with Value_vcontrol :=
  MkValue_vcontrol (_: Env_EvalEnv) (_: list Parameter') (_: list Parameter')
                   (_: list Declaration) (_: Block)
with Env_EvalEnv :=
  MkEnv_EvalEvn (_: unit).
