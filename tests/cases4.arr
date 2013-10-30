#lang pyret

data Foo:
  | foo(a :: Number)
end

fun f(x :: String) -> String:
  x
end

cases(Foo) foo(10):
  | foo(a) => f(a)
end