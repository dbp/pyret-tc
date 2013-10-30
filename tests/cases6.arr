#lang pyret

data Foo:
  | foo(a,b,c)
  | bar
end

cases(Foo) bar:
  | foo(a) => 1
  | bar => 2
end