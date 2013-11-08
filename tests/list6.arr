#lang pyret

x = ["Foo"]

cases(Option<Number>) x.find(fun(x): true end):
  | none => 1
  | some(x) => 2
end