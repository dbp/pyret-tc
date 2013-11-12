#lang pyret

#! 1st argument was expected to be of type String, but was the incompatible type Number

data Foo:
  | foo(a :: Number)
end

fun f(x :: String) -> String:
  x
end

cases(Foo) foo(10):
  | foo(a) => f(a)
end