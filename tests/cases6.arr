#lang pyret

#! variant pattern for cases branch foo should have 3 fields, not 1

data Foo:
  | foo(a,b,c)
  | bar
end

cases(Foo) bar:
  | foo(a) => 1
  | bar => 2
end