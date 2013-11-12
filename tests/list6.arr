#lang pyret

#! value in cases expression should have type Option<Number>, but has incompatible type Option<String>

x = ["Foo"]

cases(Option<Number>) x.find(fun(x): true end):
  | none => 1
  | some(x) => 2
end