Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Types.

Definition P4String := Types.P4String.
Definition Annotation := Types.Annotation.

Inductive direction :=
| In
| Out
| InOut
| Directionless.

Definition eq_dir (d1 d2: direction) :=
  match d1, d2 with
  | In, In
  | Out, Out
  | InOut, InOut
  | Directionless, Directionless => true
  | _, _ => false
  end.

Inductive IntType :=
(* MkIntType : width [int] -> IntType *)
| MkIntType (width: Z).

Inductive TableType :=
| MkTableType (result_typ_name: string).

Inductive FunctionType_kind :=
| Fun_Parser
| Fun_Control
| Fun_Extern
| Fun_Table
| Fun_Action
| Fun_Function
| Fun_Builtin.

Inductive Parameter' :=
(* MkParameter: annotations -> direction -> type -> variable ->
                  opt_value -> Parameter' *)
| MkParameter (annotations: list Annotation) (direction: direction) (typ: Type')
              (variable: P4String) (opt_value: option Types.Expression)
with PackageType :=
(* MkPackageType : type_params -> wildcard_params -> parameters ->
                     PackageType *)
| MkPackageType (type_params: list string) (wildcard_params: list string)
                (parameters: list Parameter')
with ControlType :=
(* MkControlType : type_params -> parameters -> ControlType *)
| MkControlType (type_params: list string) (parameters: list Parameter')
with ExternType_extern_method :=
(* MkExternType_extern_method : name -> type ->
                                  ExternType_extern_method *)
| MkExternType_extern_method (name: string) (typ: FunctionType)
with ExternType :=
(* MkExternType : type_params -> methods -> ExternType *)
| MkExternType (type_params: list string) (methods: list ExternType_extern_method)
with ArrayType :=
(* MkArrayType : type -> size [int] -> ArrayType *)
| MkArrayType (typ: Type') (size: Z)
with TupleType :=
| MkTupleType (types: list Type')
with NewType :=
| MkNewType (name: string) (typ: Type')
with RecordType_field :=
| MkRecordType_field (name: string) (typ: Type')
with RecordType :=
| MkRecordType (fields: list RecordType_field)
with EnumType :=
(* MkEnumType : name -> type -> members -> EnumType *)
| MkEnumType (name: string) (typ: option Type') (members: list string)
with FunctionType :=
(* MkFunctionType : type_params -> parameters -> kind ->
                      return -> FunctionType *)
| MkFunctionType (type_params: list string) (parameters: list Parameter')
                 (kind: FunctionType_kind) (ret: Type')
with SpecializedType :=
(* MkSpecializedType : base -> args -> SpecializedType *)
| MkSpecializedType (base: Type') (args: list Type')
with ActionType :=
(* MkActionType : data_params -> ctrl_params -> ActionType *)
| MkActionType (data_params: list Parameter') (ctrl_params: list Parameter')
with ConstructorType :=
(* MkConstructorType : type_params -> wildcard_params -> parameters
                         return -> ConstructorType *)
| MkConstructorType (type_params: list string) (wildcard_params: list string)
                    (parameters: list Parameter') (ret: Type')
with Type' :=
| Typ_Bool
| Typ_String
| Typ_Integer
| Typ_Int (width: IntType)
| Typ_Bit (width: IntType)
| Typ_VarBit (width: IntType)
| Typ_Array (size: ArrayType)
| Typ_Tuple (_: TupleType)
| Typ_List (_: TupleType)
| Typ_Record (_: RecordType)
| Typ_Set (_: Type')
| Typ_Error
| Typ_MatchKind
| Typ_TypeName (_: Types.name)
| Typ_NewType (_: NewType)
| Typ_Void
| Typ_Header (_: RecordType)
| Typ_HeaderUnion (_: RecordType)
| Typ_Struct (_: RecordType)
| Typ_Enum (_: EnumType)
| Typ_SpecializedType (_: SpecializedType)
| Typ_Package (_: PackageType)
| Typ_Control (_: ControlType)
| Typ_Parser (_: ControlType)
| Typ_Extern (_: ExternType)
| Typ_Function (_: FunctionType)
| Typ_Action (_: ActionType)
| Typ_Constructor (_: ConstructorType)
| Typ_Table (_: TableType).

Inductive StmType :=
| Stm_Unit
| Stm_Void.

Inductive StmtContext :=
| StmtCx_Function (_: Type')
| StmtCx_Action
| StmtCx_ParserState
| StmtCx_ApplyBlock.

Inductive DeclContext :=
| DeclCx_TopLevel
| DeclCx_Nested
| DeclCx_Statement (_: StmtContext).

Inductive ParamContext_decl :=
| ParamCxDecl_Parser
| ParamCxDecl_Control
| ParamCxDecl_Method
| ParamCxDecl_Action
| ParamCxDecl_Function
| ParamCxDecl_Package.

Inductive ParamContext :=
| ParamCx_Runtime (_: ParamContext_decl)
| ParamCx_Constructor (_: ParamContext_decl).

Inductive ExprContext :=
| ExprCx_ParserState
| ExprCx_ApplyBlock
| ExprCx_DeclLocals
| ExprCx_TableAction
| ExprCx_Action
| ExprCx_Function
| ExprCx_Constant.
