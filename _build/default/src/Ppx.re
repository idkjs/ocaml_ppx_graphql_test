open Ppxlib;
/* module List = ListLabels; */
open Ast_builder.Default;
let basicTypes = ["int", "string", "bool"];

let extract_string_from_core_type = (core_type, loc) => {
  switch (core_type.ptyp_desc) {
  | Ptyp_constr({txt: Lident(typename), _}, _) => typename
  | _ => Location.raise_errorf(~loc, "Could not access typename")
  };
};
let get_core_type = (core_type, loc) => {
  switch (core_type.ptyp_desc) {
  | Ptyp_constr({txt: Lident(_), _}, core_types) => core_types
  | _ => Location.raise_errorf(~loc, "No core_types found")
  };
};

let rec convert_nested_core_types = (core_type, type_name, opt, loc): label => {
  let core_type_string = extract_string_from_core_type(core_type, loc);
/*   print_endline(Printf.sprintf("opt: %B", opt));
 */
  switch (type_name) {
  | "int"
  | "string"
  | "bool" => (type_name |> String.capitalize_ascii) ++ (opt ? "" : "!")
  | "option" =>
    convert_nested_core_types(
          List.mem(core_type_string, basicTypes) ? core_type : get_core_type(core_type, loc) |> List.hd,
          core_type_string,
          true,
          loc,
        )
  | "list"
  | "array" =>
    "["
    ++ (
      convert_nested_core_types(
            List.mem(core_type_string, basicTypes) ? core_type : get_core_type(core_type, loc) |> List.hd,
            core_type_string,
            false,
            loc,
          )
    )
    ++ "]" ++ (opt ? "" : "!")
  | _ => Location.raise_errorf(~loc, "Could not identify kind of type")
  };
};

let convert_typename = (type_name, core_types, loc): label => {
  switch (core_types) {
  | [] =>
    List.mem(type_name, basicTypes)
      ? (type_name |> String.capitalize_ascii) ++ "!"
      : (type_name ++ "_gql") ++ "!"
  | [core_type] => convert_nested_core_types(core_type, type_name, false, loc)
  | _ => Location.raise_errorf(~loc, "List of more than one core_type")
  };
};

let isBasicType = (typename): bool =>
  List.mem(typename, basicTypes) ? true : false;

let rec isBasicTypeRec = (ptyp_desc, loc): bool =>
  switch (ptyp_desc) {
  | Ptyp_constr({txt: Lident(typename), _}, core_types) =>
    core_types == []
      ? isBasicType(typename)
      : core_types
        |> List.fold_left(
             (acc, core_type) =>
               acc && isBasicTypeRec(core_type.ptyp_desc, loc),
             true,
           )
  | _ => Location.raise_errorf(~loc, "Element is no ptyp_desc")
  };

let recordContainsOnlyBasicTypes = (lds, loc): bool => {
  lds
  |> List.fold_left(
       (acc, ld) => acc && isBasicTypeRec(ld.pld_type.ptyp_desc, loc),
       true,
     );
};

let get_type_correctly_formatted = (ptyp_desc, loc) => {
  switch (ptyp_desc) {
  | Ptyp_constr({txt: Lident(typename), _}, core_types) =>
    convert_typename(typename, core_types, loc)
  | _ => Location.raise_errorf(~loc, "Could not access typename")
  };
};

let createSchemaField = (lds, loc): string => {
  List.fold_left(
    (acc, ld) =>
      acc
      ++ " "
      ++ ld.pld_name.txt
      ++ ": "
      ++ get_type_correctly_formatted(ld.pld_type.ptyp_desc, loc)
      ++ "\n",
    "",
    lds,
  );
};

let structure_item_with_basic_types =
    (lds: list(label_declaration), type_name, loc): structure_item => {
  let type_ = type_name ++ "_gql";

  let gql_schema =
    "type "
    ++ (type_name |> String.capitalize_ascii)
    ++ " {\n"
    ++ createSchemaField(lds, loc)
    ++ "}";

  pstr_value(
    ~loc,
    Nonrecursive,
    [
      {
        pvb_pat: ppat_var(~loc, {loc, txt: type_}),
        pvb_expr: {
          pexp_constant(~loc, Pconst_string(gql_schema, None));
        },
        pvb_attributes: [],
        pvb_loc: loc,
      },
    ],
  );
};

let rec resolve_string = (lds, loc): string => {
  let ld = List.hd(lds);

  recordContainsOnlyBasicTypes([ld], loc)
    ? createSchemaField([ld], loc)
      ++ (
        compare(List.length(lds), 1) == 0
          ? "" : resolve_string(List.tl(lds), loc)
      )
    : "";
};
let resolve_first_part = (lds, typename, loc): string => {
  let recString = resolve_string(lds, loc);

  "type " ++ (typename |> String.capitalize_ascii) ++ " {\n" ++ recString;
};

let rec get_record_list_without_first_basic_records =
        (lds, loc): list(label_declaration) => {
  recordContainsOnlyBasicTypes([List.hd(lds)], loc) && List.length(lds) > 1
    ? get_record_list_without_first_basic_records(List.tl(lds), loc) : lds;
};

let rec convert_complex_nested_core_types = (core_type, type_name, opt, loc) => {
  let core_type_string = extract_string_from_core_type(core_type, loc);
/*   print_endline(Printf.sprintf("opt: %B", opt));
 */
  switch (type_name) {
  | "option" =>
    convert_complex_nested_core_types(
          List.length(get_core_type(core_type, loc)) > 0 ? get_core_type(core_type, loc) |> List.hd : core_type,
          core_type_string,
          true,
          loc,
        )
  | "list"
  | "array" =>
    %expr
    [%e estring(~loc, "[")]
    ++ (
      [%e convert_complex_nested_core_types(
            List.length(get_core_type(core_type, loc)) > 0 ? get_core_type(core_type, loc) |> List.hd : core_type,
            core_type_string,
            false,
            loc,
          )]
    )
    ++ [%e estring(~loc, "]" ++ (opt ? "" : "!"))]
  | _ => %expr [%e evar(~loc, type_name ++ "_gql")]
  };
};

let complexGqlDeclaration = (ld, loc) => {
  let type_name_expr =
    (
      switch (ld.pld_type.ptyp_desc) {
      | Ptyp_constr({txt: Lident(typename), _}, core_types) => {
        core_types == [] ? {%expr [%e evar(~loc, typename ++ "_gql")]} : convert_complex_nested_core_types(core_types |> List.hd, typename, false, loc)
      }
      | _ => Location.raise_errorf(~loc, "Coud not access typename")
      }
    );
  let record_field_name = " " ++ ld.pld_name.txt ++ ": ";

  %expr
  [%e estring(~loc, record_field_name)]
  ++ [%e type_name_expr]
  ++ [%e estring(~loc, "\n")];
};

let primitiveGqlDeclaration = (ld, loc) => {
  let expr_string = createSchemaField([ld], loc);
  estring(~loc, expr_string);
};

let structure_item_with_alias_types = (lds, typename, loc): structure_item => {
  let make_expression = ld =>
    recordContainsOnlyBasicTypes([ld], loc)
      ? primitiveGqlDeclaration(ld, loc) : complexGqlDeclaration(ld, loc);

  let consolidate_expressions = expressions =>
    expressions
    |> List.tl
    |> List.fold_left(
         (acc, ld) => {
           %expr
           [%e acc] ++ [%e ld |> make_expression]
         },
         [%expr [%e expressions |> List.hd |> make_expression]],
       );

  [%stri
    let [%p pvar(~loc, typename ++ "_gql")] =
      [%e estring(~loc, resolve_first_part(lds, typename, loc))]
      ++ [%e
        get_record_list_without_first_basic_records(lds, loc)
        |> consolidate_expressions
      ]
      ++ [%e estring(~loc, "}")]
  ];
};

let record_accessor_impl =
    (lds: list(label_declaration), type_name: string, loc) =>
  if (recordContainsOnlyBasicTypes(lds, loc)) {
    structure_item_with_basic_types(lds, type_name, loc);
  } else {
    structure_item_with_alias_types(lds, type_name, loc);
  };

let get_abstract_expression = (core_type, loc) => {
  let extracted_core_type = extract_string_from_core_type(core_type, loc);
  isBasicTypeRec(core_type.ptyp_desc, loc)
    ? estring(~loc, get_type_correctly_formatted(core_type.ptyp_desc, loc))
    : evar(~loc, extracted_core_type ++ "_gql");
};

let abstract_accessor_impl = (core_type, type_name, loc) => [%stri
  let [%p pvar(~loc, type_name ++ "_gql")] = [%e
    get_abstract_expression(core_type, loc)
  ]
];

let generate_impl = (~ctxt, (_rec_flag, type_declarations)) => {
  let loc = Expansion_context.Deriver.derived_item_loc(ctxt);
  ListLabels.map(type_declarations, ~f=(td: type_declaration) =>
    switch (td) {
    | {ptype_kind: Ptype_variant(_) | Ptype_open, _} =>
      Location.raise_errorf(
        ~loc,
        "Cannot derive accessors for non record types",
      )
    | {ptype_kind: Ptype_abstract, ptype_manifest, ptype_name, ptype_loc, _} =>
      switch (ptype_manifest) {
      | Some(core_type) =>
        abstract_accessor_impl(core_type, ptype_name.txt, ptype_loc)
      | _ => Location.raise_errorf(~loc, "No type found")
      }

    | {ptype_kind: Ptype_record(fields), ptype_name, ptype_loc, _} =>
      record_accessor_impl(fields, ptype_name.txt, ptype_loc)
    }
  );
};

let impl_generator = Deriving.Generator.V2.make_noarg(generate_impl);

let my_deriver = Deriving.add("gql", ~str_type_decl=impl_generator);

/*
  Here are the kinds of generators that can be registered:

  -str_type_decl;
  -str_type_ext;
  -str_exception;
  -sig_type_decl;
  -sig_type_ext;
  -sig_exception;
  -extension.
  The str_xyz generators are for structures/implementations, while the sig_xyz generators are for signatures/interfaces.
  extension can be used only in structures (it generates an expression).

  Then, xyz_type_decl is for type declarations (i.e. type t = (…) [@@deriving foo]),
  xyz_exception is for exception declarations (i.e. exception E [@@deriving foo]),
  and xyz_type_ext is for type extensions (i.e. type t += A [@@deriving foo] after type t = ..).
  Finally, extension is expected to be used like that: let _ = [%foo : t].



   let accessor_intf = (~ptype_name, ld: label_declaration) => {
     let loc = ld.pld_loc;
     psig_value(
       ~loc,
       {
         pval_name: ld.pld_name,
         pval_type:
           ptyp_arrow(
             ~loc,
             Nolabel,
             ptyp_constr(~loc, {loc, txt: lident(ptype_name.txt)}, []),
             ld.pld_type,
           ),
         pval_attributes: [],
         pval_loc: loc,
         pval_prim: [],
       },
     );
   };

   let generate_intf = (~ctxt, (_rec_flag, type_declarations)) => {
     let loc = Expansion_context.Deriver.derived_item_loc(ctxt);
     List.concat_map(type_declarations, ~f=(td: type_declaration) =>
       switch (td) {
       | {ptype_kind: Ptype_abstract | Ptype_variant(_) | Ptype_open, _} =>
         Location.raise_errorf(
           ~loc,
           "Cannot derive accessors for non record types",
         )
       | {ptype_kind: Ptype_record(fields), ptype_name, _} =>
         List.map(fields, ~f=accessor_intf(~ptype_name))
       }
     );
    };

    let intf_generator = Deriving.Generator.V2.make_noarg(generate_intf);

    let my_deriver =
   Deriving.add(
     "accessors",
     ~str_type_decl=impl_generator,
     ~sig_type_decl=intf_generator,
   );
 let intf_generator = Deriving.Generator.V2.make_noarg(generate_intf);

 let my_deriver =
   Deriving.add(
     "accessors",
     ~str_type_decl=impl_generator,
     ~sig_type_decl=intf_generator,
   );
    */