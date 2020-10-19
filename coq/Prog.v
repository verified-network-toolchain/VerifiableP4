Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Import Typed.

(* Molly: not needed since it is defined in Typed.
Definition Annotation := Types.Annotation. *)

Definition info := Types.info.
Definition P4String := Types.P4String.
Definition P4Int := Types.P4Int.

Inductive MethodPrototype_pre_t :=
  (* annotations, name, params *)
  | MethProto_Constructor (_: list Annotation) (_: P4String)
                          (_: list Parameter')
  (* annotations, return, name, type_params, params *)
  | MethProto_AbstractMethod (_: list Annotation) (_: Type') (_: P4String)
                             (_: list P4String) (_: list Parameter')
  (* annotations, return, name, type_params, params *)
  | MethProto_Method (_: list Annotation) (_: Type') (_: P4String) 
                     (_: list P4String) (_: list Parameter').
Definition MethodPrototype := info MethodPrototype_pre_t.

Inductive KeyValue_pre_t :=
  | MkKeyValue_pre_t: P4String -> Expression -> KeyValue_pre_t
with KeyValue :=
  | MkKeyValue: info KeyValue_pre_t -> KeyValue
with Expression_pre_t :=
  | Exp_True
  | Exp_False
  | Exp_Int (_: P4Int)
  | Exp_String (_: P4String)
  | Exp_Name (_: Types.name)
  (* array, index *)
  | Exp_ArrayAccess (_: Expression) (_: Expression)
  (* bits, lo [int] , hi [int] *)
  | Exp_BitStringAccess (_: Expression) (_: Z) (_: Z)
  | Exp_List (_: list Expression)
  | Exp_Record (_: list KeyValue)
  | Exp_UnaryOp (_: Types.Op_uni) (_: Expression)
  | Exp_BinaryOp (_: Types.Op_bin) (_: (Expression * Expression))
  | Exp_Cast (_: Type') (_: Expression)
  | Exp_TypeMember (_: Types.name) (_: P4String)
  | Exp_ErrorMember (_: P4String)
  | Exp_ExpressionMember (_: Expression) (_: P4String)
  (* cond, tru, fls *)
  | Exp_Ternary (_: Expression) (_: Expression) (_: Expression)
  (* func, type_args, args *)
  | Exp_FunctionCall (_: Expression) (_: list Type')
                     (_: list (option Expression))
  (* type, args *)
  | NamelessInstantiation (_: Type') (_: list Expression)
  | DontCare
  (* expr, mask *)
  | Mask (_: Expression) (_: Expression)
  (* lo, hi *)
  | Range (_: Expression) (_: Expression)
with Expression_typed_t :=
  (* expr, typ, dir*)
  | MkExpression_typed_t (_: Expression_pre_t) (_: Type') (_: direction)
with Expression :=
  | MkExpression (_: info Expression_typed_t).

Inductive Match_pre_t :=
  | Match_DontCare
  | Match_Expression (_: Expression).
Inductive Match_typed_t :=
  | MkMatch_typed_t: Match_pre_t -> Type' -> Match_typed_t.
Definition Match := info Match_typed_t.

Inductive Table_pre_action_ref :=
  (* annotations, name, args *)
  | MkTable_pre_action_ref (_: list Annotation) (_: Types.name)
                         (_: list (option Expression)).
Inductive Table_typed_action_ref :=
  (* action, type *)
  | MkTable_typed_action_ref (_: Table_pre_action_ref) (_: Typed.Type').
Definition Table_action_ref := info Table_typed_action_ref.

Inductive Table_pre_key :=
  (* annotations, key, match_kind *)
  | MkTable_pre_key (_: list Annotation) (_: list Expression) 
                    (_: P4String).
Definition Table_key := info Table_pre_key.

Inductive Table_pre_entry :=
  (* annotations, matches, action *)
  | MkTable_pre_entry (_: list Annotation) (_: list Match) 
                      (_: Table_action_ref).
Definition Table_entry := info Table_pre_entry.

Inductive Table_pre_property :=
  (* annotations, const, name, value *)
  | MkTable_pre_property (_: list Annotation) (_: bool) (_: P4String)
                         (_: Expression).
Definition Table_property := info Table_pre_property.

Inductive Statement_pre_switch_label :=
  | StatSwLab_Default
  | StatSwLab_Name (_: P4String).
Definition Statement_switch_label := info Statement_pre_switch_label.

Inductive Declaration_pre_field :=
  | MkDeclaration_pre_field (_: list Annotation) (_: Type') (_: P4String).
Definition Declaration_field := info Declaration_pre_field.

Definition Value_loc := string.

Inductive Value_vtable :=
  (* name, keys, actions, default_action, const_entries *)
  | ValVTable: string -> list Table_pre_key -> list Table_action_ref ->
             Table_action_ref -> list Table_pre_entry -> Value_vtable.

Definition Env_env binding := list (list (string * binding)).

Inductive Env_EvalEnv :=
  | MkEnv_EvalEnv (_: Env_env Value_loc) (_: Env_env Type') (_: string).

Inductive Statement_pre_switch_case :=
  (* label, code *)
  | StatSwCase_Action (_: Statement_switch_label) (_: Block)
  (* label *)
  | StatSwCase_FallThrough (_: Statement_switch_label)
with Statement_switch_case :=
  | MkStatement_switch_case (_: info Statement_pre_switch_case)
with Statement_pre_t :=
  (* func, type_args, args *)
  | Stat_MethodCall (_: Expression) (_: list Type')
                    (_: list (option Expression))
  (* lhs, rhs *)
  | Stat_Assignment (_: Expression) (_: Expression)
  (* typ, args *)
  | Stat_DirectApplication (_: Type') (_: list Expression)
  (* cond, tru, fls *)
  | Stat_Conditional (_: Expression) (_: Statement)(_: option Statement)
  | Stat_BlockStatement (_: Block)
  | Stat_Exit
  | Stat_EmptyStatement
  | Stat_Return (_: option Expression)
  (* expr, cases *)
  | Stat_Switch (_: Expression) (_: list Statement_switch_case)
  | Stat_DeclarationStatement (_: Declaration)
with Statement_typed_t :=
  | MkStatement_typed_t (_: Statement_pre_t) (_: StmType)
with Statement :=
  | MkStatement (_: info Statement_typed_t)
with Block_pre_t :=
  | MkBlock_pre_t (_: list Annotation) (_: list Statement)
with Block :=
  | MkBlock (_: info Block_pre_t)
with Parser_pre_case :=
  (* matches, next *)
  | MkParser_pre_case (_: list Match) (_: P4String)
with Parser_case :=
  | MkParser_case (_: info Parser_pre_case)
with Parser_pre_transition :=
  (* next *)
  | Parse_Direct (_: P4String)
  (* exprs, cases *)
  | Parse_Select (_: list Expression) (_: list Parser_case)
with Parser_transition :=
  | MkParser_transition (_: info Parser_pre_transition)
with Parser_pre_state :=
  (* annotations, name, statements, transition *)
  | MkParser_pre_state (_: list Annotation) (_: P4String) 
                       (_: list Statement) (_: Parser_transition)
with Parser_state :=
  | MkParser_state (_: info Parser_pre_state)
with Declaration_pre_t :=
  (* annotations, typ, name, value *)
  | Decl_Constant (_: list Annotation) (_: Type') (_: P4String)
                  (_: Value_value)
  (* annotations, typ, args, name, init *)
  | Decl_Instantiation (_: list Annotation) (_: Type') (_: list Expression)
                  (_: P4String) (_: option Block)
  (* annotations, name, typ_params, params, constructor_params, locals,
     states *)
  | Decl_Parser (_: list Annotation) (_ : P4String) (_: list P4String)
                (_: list Parameter') (_: list Parameter') 
                (_: list Declaration) (_: list Parser_state)

  (* annotations, name, typ_params, params, constructor_params, locals,
     apply *)
  | Decl_Control (_: list Annotation) (_: P4String) (_: list P4String)
                 (_: list Parameter') (_: list Parameter') 
                 (_: list Declaration) (_: Block)
  (* return, name, typ_params, params, body *)
  | Decl_Function (_: Type') (_: P4String) (_: list P4String)
                  (_: list Parameter') (_: Block)
  (* annotations, return, name, typ_params, params *)
  | Decl_ExternFunction (_: list Annotation) (_: Type') (_: P4String)
                        (_: list P4String) (_: list Parameter')
  (* annotations, typ, name, init *)
  | Decl_Variable (_: list Annotation) (_: Type') (_: P4String)
                  (_: option Expression)
  (* annotations, typ, size, name *)
  | Decl_ValueSet (_: list Annotation) (_: Type') (_: Expression) (_: P4String)
  (* annotations, name, data_params, ctrl_params, body *)
  | Decl_Action (_: list Annotation) (_: P4String) (_: list Parameter')
                (_: list Parameter') (_: Block)
  (* annotations, name, key, actions, entries, default_action, size,
     custom_properties *)
  | Decl_Table (_: list Annotation) (_: P4String) (_: list Table_key)
               (_: list Table_action_ref) (_: option (list Table_entry))
               (_: option Table_action_ref) (_: option P4Int)
               (_: list Table_property)
  (* annotations, name, fields *)
  | Decl_Header (_: list Annotation) (_: P4String) 
                (_: list Declaration_field)
  (* annotations, name, fields *)
  | Decl_HeaderUnion (_: list Annotation) (_: P4String) 
                     (_: list Declaration_field)
  (* annotations, name, fields *)
  | Decl_Struct (_: list Annotation) (_: P4String) 
                (_: list Declaration_field)
  | Decl_Error (_: list P4String)
  (* members *)
  | Decl_MatchKind (_: list P4String)
  (* annotations, name, members *)
  | Decl_Enum (_: list Annotation) (_: P4String) (_: list P4String)
  (* annotations, typ, name, members *)
  | Decl_SerializableEnum (_: list Annotation) (_: Type') (_: P4String)
                          (_: list (P4String * Expression))
  (* annotations, name, typ_params, methods *)
  | Decl_ExternObject (_: list Annotation) (_: P4String) (_: list P4String)
                 (_: list MethodPrototype)
  (* annotations, name, typ_or_decl *)
  | Decl_TypeDef (_: list Annotation) (_: P4String) 
                 (_: (Type' + Declaration))
  (* annotations, name, typ_or_decl *)
  | Decl_NewType (_: list Annotation) (_: P4String) 
                 (_: (Type' + Declaration))
  (* annotations, name, typ_params, params *)
  | Decl_ControlType (_: list Annotation) (_: P4String) (_: list P4String)
                     (_: list Parameter')
  (* annotations, name, typ_params, params *)
  | Decl_ParserType (_: list Annotation) (_: P4String) (_: list P4String)
                    (_: list Parameter')
  (* annotations, name, typ_params, params *)
  | Decl_PackageType (_: list Annotation) (_: P4String) (_: list P4String)
                (_: list Parameter')
with Declaration :=
  | MkDeclaration (_: info Declaration_pre_t)
with Value_value :=
  | Val_VNull
  | Val_VBool (_: bool)
  | Val_VInteger (_: Z)
  (* width, value *)
  | Val_VBit (_: Z) (_: Z)
  (* width, value *)
  | Val_VInt (_: Z) (_: Z)
  (* max, width, value *)
  | Val_VVarbit (_: Z) (_: Z) (_: Z)
  | Val_VString (_: string)
  | Val_VTuple (_: list Value_value)
  | Val_VRecord (_: list (string * Value_value))
  | Val_VSet (_: Value_set)
  | Val_VError (_: string)
  | Val_VMatchKind (_: string)
  (* scope, params, body *)
  | Val_VFun (_: Env_EvalEnv) (_: list Parameter') (_: Block)
  (* name, caller *)
  | Val_VBuiltinFun (_: string) (_: Value_lvalue)
  (* scope, params, body *)
  | Val_VAction (_: Env_EvalEnv) (_: list Parameter') (_: Block)
  | Val_VStruct (_: list (string * Value_value))
  (* fields, is_valid *)
  | Val_VHeader (_: list (string * Value_value)) (_: bool)
  | Val_VUnion (_: list (string * Value_value))
  (* headers, size, next *)
  | Val_VStack (_: list Value_value) (_: Z) (_: Z)
  (* typ_name, enum_name *)
  | Val_VEnumField (_: string) (_: string)
  (* typ_name, enum_name, value *)
  | Val_VSenumField (_: string) (_: string) (_: Value_value)
  | Val_VSenum (_: list (string * Value_value))
  (* loc, obj_name *)
  | Val_VRuntime (_: Value_loc) (_: string)
  | Val_VParser (_: Value_vparser)
  | Val_VControl (_: Value_vcontrol)
  (* params, args *)
  | Val_VPackage (_: list Parameter') (_: list (string * Value_loc))
  | Val_VTable (_: Value_vtable)
  (* name, caller, params*)
  | Val_VExternFun (_: string) (_: option (Value_loc * string)) 
                   (_: list Parameter')
  | Val_VExternObj (_: list (string * list Parameter'))
with Value_set :=
  (* width, value *)
  | ValSet_SSingleton (_: Z) (_: Z)
  | ValSet_SUniversal
  (* value, mask *)
  | ValSet_SMask (_: Value_value) (_: Value_value)
  (* lo, hi *)
  | ValSet_SRange (_: Value_value) (_: Value_value)
  | ValSet_SProd (_: list Value_set)
  (* width, nbits, value *)
  | ValSet_SLpm (_: Value_value) (_: Z) (_: Value_value)
  (* size, members, sets *)
  | ValSet_SValueSet (_: Value_value) (_: list (list Match))
                      (_: list Value_set)
with Value_pre_lvalue :=
  | ValLeft_LName (_: Types.name)
  (* expr, name *)
  | ValLeft_LMember (_: Value_lvalue) (_: string)
  (* expr, msb, lsb *)
  | ValLeft_LBitAccess (_: Value_lvalue) (_: Z) (_: Z)
  (* expr, idx *)
  | ValLeft_LArrayAccess (_: Value_lvalue) (_: Value_value)
with Value_lvalue :=
  | MkValue_lvalue (_: Value_pre_lvalue) (_: Type')
with Value_vparser :=
  (* scope, constructor_params, params, locals, states *)
  | MkValue_vparser (_: Env_EvalEnv) (_: list Parameter') 
                    (_: list Parameter') (_: list Declaration)
                    (_: list Parser_state)
with Value_vcontrol :=
  (* scope, constructor_params, params, locals, apply *)
  | MkValue_vcontrol (_: Env_EvalEnv) (_: list Parameter') 
                     (_: list Parameter') (_: list Declaration) (_: Block).

(* Molly: Value_pkt, Value_entries, Value_vset, Value_ctrl, Value_signal 
          omitted*)

Inductive Env_Renamer_state :=
  MkEnv_Renamer_state: Z -> list string -> Env_Renamer_state.

(** * TODO Here the definition of Env_Renamer is just a placeholder *)
Inductive Env_Renamer := MkEnv_Renamer (_: Env_Renamer_state).

Inductive Env_CheckerEnv :=
  MkEnv_CheckerEnv (_: Env_env Type') (_: Env_env (Type' * direction))
                   (_: Env_env Value_value) (_: Env_Renamer).

Inductive program := Program (_: list Declaration).
