Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Import Types.

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

Inductive IntType := Int: Z -> IntType.
Inductive TableType := MkTableType: string -> TableType.

Inductive FunctionType_kind :=
| Parser
| Control
| Extern
| Table
| Action
| Function'
| Builtin.

Inductive Parameter' :=
  MkParameter: list Annotation -> direction -> Type' -> P4String ->
               option Expression -> Parameter'
with PackageType :=
  MkPackageType: list string -> list string -> list Parameter' -> PackageType
with ControlType :=
  MkControlType: list string -> list Parameter' -> ControlType
with extern_method :=
  Mkextern_method: string -> FunctionType -> extern_method
with ExternType :=
  MkExternType: list string -> list extern_method -> ExternType
with ArrayType :=
  MkArrayType: Type' -> Z -> ArrayType
with TupleType :=
  MkTupleType: list Type' -> TupleType
with NewType :=
  MkNewType: string -> Type' -> NewType
with RecordType_field :=
  MkRecordType_field: string -> Type' -> RecordType_field
with RecordType :=
  MkRecordType: list RecordType_field -> RecordType
with EnumType :=
  MkEnumType: string -> option Type' -> list string -> EnumType
with FunctionType :=
  MkFunctionType: list string -> list Parameter' -> FunctionType_kind ->
                  Type' -> FunctionType
with SpecializedType :=
  MkSpecializedType: Type' -> list Type' -> SpecializedType
with ActionType :=
  MkActionType: list Parameter' -> list Parameter' -> ActionType
with ConstructorType :=
  MkConstructorType: list string -> list string -> list Parameter' ->
                     Type' -> ConstructorType
with Type' :=
| Bool'
| String'
| Integer
| Int' (_: IntType)
| Bit (_: IntType)
| VarBit (_: IntType)
| Array (_: ArrayType)
| Tuple (_: TupleType)
| List' (_: TupleType)
| Record' (_: RecordType)
| Set' (_: Type')
| Error
| MatchKind
| TypeName (_: Types.name)
| NewType' (_: NewType)
| Void
| Header (_: RecordType)
| HeaderUnion (_: RecordType)
| Struct (_: RecordType)
| Enum (_: EnumType)
| SpecializedType' (_: SpecializedType)
| Package (_: PackageType)
| Control' (_: ControlType)
| Parser' (_: ControlType)
| Extern' (_: ExternType)
| Function'' (_: FunctionType)
| Action' (_: ActionType)
| Constructor (_: ConstructorType)
| Table' (_: TableType).

Inductive StmType :=
| Unit
| Void'.

Inductive StmtContext :=
| Function''' (_: Type')
| Action''
| ParserState
| ApplyBlock.

Inductive DeclContext :=
| TopLevel
| Nested
| Statement' (_: StmtContext).

Inductive ParamContext_decl :=
| Parser''
| Control''
| Method
| Action'''
| Function''''
| Package'.

Inductive ParamContext :=
| Runtime (_: ParamContext_decl)
| Constructor' (_: ParamContext_decl).

Inductive ExprContext :=
| ParserState'
| ApplyBlock'
| DeclLocals
| TableAction
| Action''''
| Function'''''
| Constant.
