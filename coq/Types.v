Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Info.
Require Import Coq.extraction.Extraction.

Open Scope type_scope.

Definition info (A : Type) := Info * A.

Inductive P4Int_pre_t :=
| MkP4Int_pre_t (value: Z) (width_signed: option (Z * bool)).

(* P4Int = info (value [bigint] * (width [int] * signed) option) *)
Definition P4Int := info P4Int_pre_t.

Definition P4String := info string.

Inductive name :=
  | BareName : P4String -> name
  | QualifiedName (namespaces: list P4String) (name: P4String).

Inductive Op_pre_uni : Type :=
  | Not
  | BitNot
  | UMinus.
Definition Op_uni := info Op_pre_uni.

Inductive Op_pre_bin : Type :=
  | Plus
  | PlusSat
  | Minus
  | MinusSat
  | Mul
  | Div
  | Mod
  | Shl
  | Shr
  | Le
  | Ge
  | Lt
  | Gt
  | Eq
  | NotEq
  | BitAnd
  | BitXor
  | BitOr
  | PlusPlus
  | And
  | Or.
Definition Op_bin := info Op_pre_bin.

Inductive Direction_pre_t :=
  | In
  | Out
  | InOut.
Definition Direction := info Direction_pre_t.

Inductive KeyValue_pre_t :=
  | MkKeyValue_pre_t (key: P4String) (value: Expression)
with KeyValue :=
  | MkKeyValue: info KeyValue_pre_t -> KeyValue
with Type'_pre_t :=
  | Typ_Bool
  | Typ_Error
  | Typ_Integer
  | Typ_IntType : Expression -> Type'_pre_t
  | Typ_BitType : Expression -> Type'_pre_t
  | Typ_VarBit : Expression -> Type'_pre_t
  (* this could be a typename or a type variable. *)
  | Typ_TypeName : name -> Type'_pre_t
  (* SpecializedType : base -> args -> Type'_pre_t *)
  | Typ_SpecializedType (bese: Type') (args: list Type')
  (* HeaderStack : header_type -> header_size -> Type'_pre_t *)
  | Typ_HeaderStack (header: Type') (size: Expression)
  | Typ_Tuple : list Type' -> Type'_pre_t
  | Typ_String
  | Typ_Void
  | Typ_DontCare
with Type' :=
  | MkType' : info Type'_pre_t -> Type'
with Argument_pre_t :=
  | Arg_Expression (value: Expression)
  (* Arg_KeyValue : key -> value -> Argument_pre_t *)
  | Arg_KeyValue (key: P4String) (value: Expression)
  | Arg_Missing
with Argument :=
  | MkArgument : info Argument_pre_t -> Argument
with Expression_pre_t :=
  | Exp_True
  | Exp_False
  | Exp_Int : P4Int -> Expression_pre_t
  | Exp_String : P4String -> Expression_pre_t
  | Exp_Name : name -> Expression_pre_t
  (* | ArrayAccess of
      { array: t;
        index: t } *)
  (* | BitStringAccess of
      { bits: t;
        lo: t;
        hi: t } *)
  (* | List of
      { values: t list } *)
  (* | Record of
      { entries: KeyValue.t list } *)
  | Exp_UnaryOp (op: Op_uni) (arg: Expression)
  | Exp_BinaryOp (op: Op_bin) (args: (Expression * Expression))
  (* | Cast of
      { typ: Type.t;
        expr: t } *)
  (* | TypeMember of
      { typ: name;
        name: P4String.t } *)
  (* | ErrorMember of P4String.t *)
  (* | ExpressionMember of
      { expr: t;
        name: P4String.t } *)
  (* | Ternary of
      { cond: t;
        tru: t;
        fls: t } *)
  (* FunctionCall func type_args args *)
  | Exp_FunctionCall (func: Expression) (type_args: list Type') (args: list Argument)
  (* | NamelessInstantiation of
      { typ: Type.t [@key "type"];
        args: Argument.t list } *)
  (* | Mask of
      { expr: t;
        mask: t } *)
  (* | Range of
      { lo: t;
        hi: t } *)
with Expression :=
  | MkExpression : info Expression_pre_t -> Expression.

Inductive Annotation_pre_body :=
  | Anno_Empty
  | Anno_Unparsed : list P4String -> Annotation_pre_body
  | Anno_Expression : list Expression -> Annotation_pre_body
  | Anno_KeyValue : list KeyValue -> Annotation_pre_body.
Definition Annotation_body := info Annotation_pre_body.
Inductive Annotation_pre_t :=
  | MkAnnotation_pre_t (name: P4String) (body: Annotation_body).
Definition Annotation := info Annotation_pre_t.


(* Molly: Types.Parameter' seems not needed.

with Parameter' :=
  | MkParameter :
      Info ->
      list Annotation -> (* annotations *)
      option Direction -> (* direction *)
      Type' -> (* typ *)
      P4String -> (* variable *)
      option Expression -> (* opt_value *)
      Parameter'

*)



(* let to_bare : name -> name = function
  | BareName n
  | QualifiedName (_,n) -> BareName n

let name_info name : Info.t =
  match name with
  | BareName name -> fst name
  | QualifiedName (prefix, name) ->
     let infos = List.map fst prefix in
     List.fold_right Info.merge infos (fst name)

let name_eq n1 n2 =
  match n1, n2 with
  | BareName (_, s1),
    BareName (_, s2) ->
     s1 = s2
  | QualifiedName ([], (_, s1)),
    QualifiedName ([], (_, s2)) ->
     s1 = s2
  | _ -> false

and name_only n =
  match n with
  | BareName (_, s) -> s
  | QualifiedName (_, (_, s)) -> s
*)



(* and MethodPrototype : sig
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: P4String.t;
        params: Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: Parameter.t list}
        [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end = struct
  type pre_t =
    Constructor of
      { annotations: Annotation.t list;
        name: P4String.t;
        params: Parameter.t list }
  | AbstractMethod of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: Parameter.t list}
  | Method of
      { annotations: Annotation.t list;
        return: Type.t;
        name: P4String.t;
        type_params: P4String.t list;
        params: Parameter.t list}
    [@@deriving sexp,show,yojson]

  type t = pre_t info [@@deriving sexp,show,yojson]
end *)


(* and Table : sig
      type pre_action_ref =
        { annotations: Annotation.t list;
          name: name;
          args: Argument.t list }
      [@@deriving sexp,show,yojson]

      type action_ref = pre_action_ref info [@@deriving sexp,show,yojson]

      type pre_key =
        { annotations: Annotation.t list;
          key: Expression.t;
          match_kind: P4String.t }
      [@@deriving sexp,show,yojson]

      type key = pre_key info [@@deriving sexp,show,yojson]

      type pre_entry =
        { annotations: Annotation.t list;
          matches: Match.t list;
          action: action_ref }
      [@@deriving sexp,show,yojson { exn = true }]

      type entry = pre_entry info [@@deriving sexp,show,yojson]

      type pre_property =
          Key of
            { keys: key list }
        | Actions of
            { actions: action_ref list }
        | Entries of
            { entries: entry list }
        | Custom of
            { annotations: Annotation.t list;
              const: bool;
              name: P4String.t;
              value: Expression.t }
      [@@deriving sexp,show,yojson]

      type property = pre_property info [@@deriving sexp,show,yojson]

      val name_of_property : property -> string
    end = struct
              type pre_action_ref =
                { annotations: Annotation.t list;
                  name: name;
                  args: Argument.t list }
              [@@deriving sexp,show,yojson]

              type action_ref = pre_action_ref info [@@deriving sexp,show,yojson]

              type pre_key =
                { annotations: Annotation.t list;
                  key: Expression.t;
                  match_kind: P4String.t }
              [@@deriving sexp,show,yojson]

              type key = pre_key info [@@deriving sexp,show,yojson]

              type pre_entry =
                { annotations: Annotation.t list;
                  matches: Match.t list;
                  action: action_ref }
              [@@deriving sexp,show,yojson { exn = true }]

              type entry = pre_entry info [@@deriving sexp,show,yojson]

              type pre_property =
                  Key of
                    { keys: key list }
                | Actions of
                    { actions: action_ref list }
                | Entries of
                    { entries: entry list }
                | Custom of
                    { annotations: Annotation.t list;
                      const: bool;
                      name: P4String.t;
                      value: Expression.t }
              [@@deriving sexp,show,yojson]

              type property = pre_property info [@@deriving sexp,show,yojson]

              let name_of_property p =
                match snd p with
                | Key _ -> "key"
                | Actions _ -> "actions"
                | Entries _ -> "entries"
                | Custom {name; _} -> snd name
            end

and Match : sig
      type pre_t =
          Default
        | DontCare
        | Expression of
            { expr: Expression.t }
      [@@deriving sexp,show,yojson { exn = true }]

      type t = pre_t info [@@deriving sexp,show,yojson { exn = true }]
    end = struct
              type pre_t =
                  Default
                | DontCare
                | Expression of
                    { expr: Expression.t }
              [@@deriving sexp,show,yojson { exn = true }]

              type t = pre_t info [@@deriving sexp,show,yojson { exn = true }]
            end

and Parser : sig
      type pre_case =
        { matches: Match.t list;
          next: P4String.t }
      [@@deriving sexp,show,yojson { exn = true }]

      type case = pre_case info [@@deriving sexp,show,yojson]

      type pre_transition =
          Direct of
            { next: P4String.t }
        | Select of
            { exprs: Expression.t list;
              cases: case list }
      [@@deriving sexp,show,yojson]

      type transition = pre_transition info [@@deriving sexp,show,yojson]

      type pre_state =
        { annotations: Annotation.t list;
          name: P4String.t;
          statements: Statement.t list;
          transition: transition }
      [@@deriving sexp,show,yojson]

      type state = pre_state info [@@deriving sexp,show,yojson]
    end = struct
               type pre_case =
                 { matches: Match.t list;
                   next: P4String.t }
               [@@deriving sexp,show,yojson { exn = true }]

               type case = pre_case info [@@deriving sexp,show,yojson]

               type pre_transition =
                   Direct of
                     { next: P4String.t }
                 | Select of
                     { exprs: Expression.t list;
                       cases: case list }
               [@@deriving sexp,show,yojson]

               type transition = pre_transition info [@@deriving sexp,show,yojson]

               type pre_state =
                 { annotations: Annotation.t list;
                   name: P4String.t;
                   statements: Statement.t list;
                   transition: transition }
               [@@deriving sexp,show,yojson]

               type state = pre_state info [@@deriving sexp,show,yojson]
             end

and Declaration : sig
      type pre_t =
          Constant of
            { annotations: Annotation.t list;
              typ: Type.t [@key "type"];
              name: P4String.t;
              value: Expression.t }
        | Instantiation of
            { annotations: Annotation.t list;
              typ: Type.t [@key "type"];
              args: Argument.t list;
              name: P4String.t;
              init: Block.t option; }
        | Parser of
            { annotations: Annotation.t list;
              name: P4String.t;
              type_params: P4String.t list;
              params: Parameter.t list;
              constructor_params: Parameter.t list;
              locals: t list;
              states: Parser.state list }
        | Control of
            { annotations: Annotation.t list;
              name: P4String.t;
              type_params: P4String.t list;
              params: Parameter.t list;
              constructor_params: Parameter.t list;
              locals: t list;
              apply: Block.t }
        | Function of
            { return: Type.t;
              name: P4String.t;
              type_params: P4String.t list;
              params: Parameter.t list;
              body: Block.t }
        | ExternFunction of
            { annotations: Annotation.t list;
              return: Type.t;
              name: P4String.t;
              type_params: P4String.t list;
              params: Parameter.t list }
        | Variable of
            { annotations: Annotation.t list;
              typ: Type.t [@key "type"];
              name: P4String.t;
              init: Expression.t option }
        | ValueSet of
            { annotations: Annotation.t list;
              typ: Type.t [@key "type"];
              size: Expression.t;
              name: P4String.t }
        | Action of
            { annotations: Annotation.t list;
              name: P4String.t;
              params: Parameter.t list;
              body: Block.t }
        | Table of
            { annotations: Annotation.t list;
              name: P4String.t;
              properties: Table.property list }
        | Header of
            { annotations: Annotation.t list;
              name: P4String.t;
              fields: field list }
        | HeaderUnion of
            { annotations: Annotation.t list;
              name: P4String.t;
              fields: field list }
        | Struct of
            { annotations: Annotation.t list;
              name: P4String.t;
              fields: field list }
        | Error of
            { members: P4String.t list }
        | MatchKind of
            { members: P4String.t list }
        | Enum of
            { annotations: Annotation.t list;
              name: P4String.t;
              members: P4String.t list }
        | SerializableEnum of
            { annotations: Annotation.t list;
              typ: Type.t [@key "type"];
              name: P4String.t;
              members: (P4String.t * Expression.t) list }
        | ExternObject of
            { annotations: Annotation.t list;
              name: P4String.t;
              type_params: P4String.t list;
              methods: MethodPrototype.t list }
        | TypeDef of
            { annotations: Annotation.t list;
              name: P4String.t;
              typ_or_decl: (Type.t, t) alternative }
        | NewType of
            { annotations: Annotation.t list;
              name: P4String.t;
              typ_or_decl: (Type.t, t) alternative }
        | ControlType of
            { annotations: Annotation.t list;
              name: P4String.t;
              type_params: P4String.t list;
              params: Parameter.t list }
        | ParserType of
            { annotations: Annotation.t list;
              name: P4String.t;
              type_params: P4String.t list;
              params: Parameter.t list }
        | PackageType of
            { annotations: Annotation.t list;
              name: P4String.t;
              type_params: P4String.t list;
              params: Parameter.t list }
      [@@deriving sexp,show,yojson]

and t = pre_t info [@@deriving sexp,show,yojson]

and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: P4String.t } [@@deriving sexp,show,yojson]

and field = pre_field info [@@deriving sexp,show,yojson]

val name : t -> P4String.t

val name_opt : t -> P4String.t option

end = struct
  type pre_t =
      Constant of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          value: Expression.t }
    | Instantiation of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          args: Argument.t list;
          name: P4String.t;
          init: Block.t option; }
    | Parser of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          states: Parser.state list }
    | Control of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          constructor_params: Parameter.t list;
          locals: t list;
          apply: Block.t }
          [@name "control"]
    | Function of
        { return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list;
          body: Block.t }
    | ExternFunction of
        { annotations: Annotation.t list;
          return: Type.t;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | Variable of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          init: Expression.t option }
    | ValueSet of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          size: Expression.t;
          name: P4String.t }
    | Action of
        { annotations: Annotation.t list;
          name: P4String.t;
          params: Parameter.t list;
          body: Block.t }
    | Table of
        { annotations: Annotation.t list;
          name: P4String.t;
          properties: Table.property list }
    | Header of
        { annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | HeaderUnion of
        { annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Struct of
        { annotations: Annotation.t list;
          name: P4String.t;
          fields: field list }
    | Error of
        { members: P4String.t list }
    | MatchKind of
        { members: P4String.t list }
    | Enum of
        { annotations: Annotation.t list;
          name: P4String.t;
          members: P4String.t list }
    | SerializableEnum of
        { annotations: Annotation.t list;
          typ: Type.t [@key "type"];
          name: P4String.t;
          members: (P4String.t * Expression.t) list }
    | ExternObject of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          methods: MethodPrototype.t list }
    | TypeDef of
        { annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | NewType of
        { annotations: Annotation.t list;
          name: P4String.t;
          typ_or_decl: (Type.t, t) alternative }
    | ControlType of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | ParserType of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
    | PackageType of
        { annotations: Annotation.t list;
          name: P4String.t;
          type_params: P4String.t list;
          params: Parameter.t list }
  [@@deriving sexp,show,yojson]

and t = pre_t info [@@deriving sexp,show,yojson]

and pre_field =
    { annotations: Annotation.t list;
      typ: Type.t [@key "type"];
      name: P4String.t } [@@deriving sexp,show,yojson]

and field = pre_field info [@@deriving sexp,show,yojson]

let name_opt d =
  match snd d with
  | Constant {name; _}
  | Instantiation {name; _}
  | Parser {name; _}
  | Control {name; _}
  | Function {name; _}
  | ExternFunction {name; _}
  | Variable {name; _}
  | ValueSet {name; _}
  | Action {name; _}
  | Table {name; _}
  | Header {name; _}
  | HeaderUnion {name; _}
  | Struct {name; _}
  | Enum {name; _}
  | SerializableEnum {name; _}
  | ExternObject {name; _}
  | TypeDef {name; _}
  | NewType {name; _}
  | ControlType {name; _}
  | ParserType {name; _}
  | PackageType {name; _} ->
      Some name
  | Error _
  | MatchKind _ ->
      None

let name d =
  match name_opt d with
  | Some name -> name
  | None -> failwith "this declaration does not have a name"
end

and Statement : sig
      type pre_switch_label =
          Default
        | Name of P4String.t
      [@@deriving sexp,show,yojson]

      type switch_label = pre_switch_label info [@@deriving sexp,show,yojson]

      type pre_switch_case =
          Action of
            { label: switch_label;
              code: Block.t }
        | FallThrough of
            { label: switch_label }
      [@@deriving sexp,show,yojson]

      type switch_case = pre_switch_case info [@@deriving sexp,show,yojson]

      type pre_t =
          MethodCall of
            { func: Expression.t;
              type_args: Type.t list;
              args: Argument.t list }
        | Assignment of
            { lhs: Expression.t;
              rhs: Expression.t }
        | DirectApplication of
            { typ: Type.t [@key "type"];
              args: Argument.t list }
        | Conditional of
            { cond: Expression.t;
              tru: t;
              fls: t option }
        | BlockStatement of
            { block: Block.t }
        | Exit
        | EmptyStatement
        | Return of
            { expr: Expression.t option }
        | Switch of
            { expr: Expression.t;
              cases: switch_case list }
        | DeclarationStatement of
            { decl: Declaration.t }
      [@@deriving sexp,show,yojson]

and t = pre_t info [@@deriving sexp,show,yojson]
end = struct
  type pre_switch_label =
      Default [@name "default"]
    | Name of P4String.t [@name "name"]
  [@@deriving sexp,show,yojson]

  type switch_label = pre_switch_label info [@@deriving sexp,show,yojson]

  type pre_switch_case =
      Action of
        { label: switch_label;
          code: Block.t }
    | FallThrough of
        { label: switch_label }
  [@@deriving sexp,show,yojson]

  type switch_case = pre_switch_case info [@@deriving sexp,show,yojson]

  type pre_t =
      MethodCall of
        { func: Expression.t;
          type_args: Type.t list;
          args: Argument.t list } [@name "method_call"]
    | Assignment of
        { lhs: Expression.t;
          rhs: Expression.t } [@name "assignment"]
    | DirectApplication of
        { typ: Type.t [@key "type"];
          args: Argument.t list } [@name "direct_application"]
    | Conditional of
        { cond: Expression.t;
          tru: t;
          fls: t option } [@name "conditional"]
    | BlockStatement of
        { block: Block.t } [@name "block"]
    | Exit [@name "exit"]
    | EmptyStatement [@name "empty_statement"]
    | Return of
        { expr: Expression.t option } [@name "return"]
    | Switch of
        { expr: Expression.t;
          cases: switch_case list } [@name "switch"]
    | DeclarationStatement of
        { decl: Declaration.t } [@name "declaration"]
  [@@deriving sexp,show,yojson]

and t = pre_t info [@@deriving sexp,show,yojson]
end

and Block : sig
      type pre_t =
        { annotations: Annotation.t list;
          statements: Statement.t list }
      [@@deriving sexp,show,yojson]

      type t = pre_t info [@@deriving sexp,show,yojson]
    end = struct
              type pre_t =
                { annotations: Annotation.t list;
                  statements: Statement.t list }
              [@@deriving sexp,show,yojson]

              type t = pre_t info [@@deriving sexp,show,yojson]
            end

type program =
    Program of Declaration.t list [@name "program"]
[@@deriving sexp,show,yojson] *)
