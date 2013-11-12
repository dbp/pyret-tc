#lang pyret

#==

data Foo:
  | foo(a :: Number)
end

x :: Number = cases(Foo) foo(10):
  | foo(a) => a
end