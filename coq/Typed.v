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
  | MkIntType : Z -> IntType.

Inductive TableType := 
  | MkTableType: string -> TableType.

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
  | MkParameter: list Annotation -> direction -> Type' -> P4String ->
                 option Types.Expression -> Parameter'
with PackageType :=
  (* MkPackageType : type_params -> wildcard_params -> parameters ->
                     PackageType *)
  | MkPackageType: list string -> list string -> list Parameter' ->
                   PackageType
with ControlType :=
  (* MkControlType : type_params -> parameters -> ControlType *)
  | MkControlType: list string -> list Parameter' -> ControlType
with ExternType_extern_method :=
  (* MkExternType_extern_method : name -> type -> 
                                  ExternType_extern_method *)
  | MkExternType_extern_method: string -> FunctionType ->
                                ExternType_extern_method
with ExternType :=
  (* MkExternType : type_params -> methods -> ExternType *)
  | MkExternType: list string -> list ExternType_extern_method ->
                  ExternType
with ArrayType :=
  (* MkArrayType : type -> size [int] -> ArrayType *)
  | MkArrayType: Type' -> Z -> ArrayType
with TupleType :=
  | MkTupleType: list Type' -> TupleType
with NewType :=
  | MkNewType: string -> Type' -> NewType
with RecordType_field :=
  | MkRecordType_field: string -> Type' -> RecordType_field
with RecordType :=
  | MkRecordType: list RecordType_field -> RecordType
with EnumType :=
  (* MkEnumType : name -> type -> members -> EnumType *)
  | MkEnumType: string -> option Type' -> list string -> EnumType
with FunctionType :=
  (* MkFunctionType : type_params -> parameters -> kind -> 
                      return -> FunctionType *)
  | MkFunctionType: list string -> list Parameter' -> FunctionType_kind ->
                    Type' -> FunctionType
with SpecializedType :=
  (* MkSpecializedType : base -> args -> SpecializedType *)
  | MkSpecializedType: Type' -> list Type' -> SpecializedType
with ActionType :=
  (* MkActionType : data_params -> ctrl_params -> ActionType *)
  | MkActionType: list Parameter' -> list Parameter' -> ActionType
with ConstructorType :=
  (* MkConstructorType : type_params -> wildcard_params -> parameters
                         return -> ConstructorType *)
  | MkConstructorType: list string -> list string -> list Parameter' ->
                       Type' -> ConstructorType
with Type' :=
| Typ_Bool
| Typ_String
| Typ_Integer
| Typ_Int (_: IntType)
| Typ_Bit (_: IntType)
| Typ_VarBit (_: IntType)
| Typ_Array (_: ArrayType)
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
