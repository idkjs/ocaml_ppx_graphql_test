[@deriving gql]
type x = int;

[@deriving gql]
type y = option(string);

[@deriving gql]
type z = y;

[@deriving gql]
type t = {
  a: option(list(array(option(int)))),
  b: option(list(x)),
  c: y,
  d: array(z),
};

print_endline("\n" ++ t_gql);